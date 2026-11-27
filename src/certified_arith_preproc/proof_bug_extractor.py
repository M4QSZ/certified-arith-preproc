"""
ATAQUE-08: Constructive Bug-Extraction & K^t Witness-Compression Diagnostic.

Implements:
(a) Parallel TC^0 / SAT Local Step Bug-Extractor & O(log t) Binary-Search
    Localization over alleged Krajicek (Circuits, ≈) chains:
    - PHP (corrupted pigeonhole refutation chain)
    - Goldreich XOR-MAJ3 (corrupted planted-witness equivalence chain)
    - 3-SAT near alpha=4.26 (corrupted UNSAT rewrite chain)
    - Faulty DeMorgan / fan-out-2 simultaneous-rewrite chain (Datta-Dutta v1 style bug)
(b) K^t Witness-Compression & Symmetry-of-Information (SoI) Diagnostic (n = 6..14):
    - Measures empirical LZ77/zlib and circuit-DAG description complexity
      K^t(x, f(x)) vs K^t(x) + K^t(f(x)|x) and reverse K^t(f(x)) + K^t(x|f(x))
      on Schoolbook mult, Goldreich XOR-MAJ3, Keccak-chi 4-round, and Random permutation,
      quantifying the SoI deficit Delta_SoI (Hirahara, Lu & Nanashima FOCS 2024).

Uses z3-solver if available, otherwise python-sat (Cadical195) via Tseitin encoding.
"""

from __future__ import annotations

import json
import math
import random
import time
import zlib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

try:
    import z3  # type: ignore
    HAS_Z3 = True
except ImportError:
    HAS_Z3 = False

from pysat.solvers import Cadical195


# ---------------------------------------------------------------------------
# 1. Hash-Consed DeMorgan DAG Circuits
# ---------------------------------------------------------------------------

class CircuitPool:
    """Hash-consed DeMorgan DAG circuit builder over {0, 1, neg, disj, conj, var}."""

    def __init__(self) -> None:
        self.nodes: List[Tuple] = [("zero",), ("one",)]
        self.intern: Dict[Tuple, int] = {("zero",): 0, ("one",): 1}
        self.ZERO = 0
        self.ONE = 1

    def var(self, idx: int) -> int:
        key = ("var", idx)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def neg(self, a: int) -> int:
        if a == self.ZERO:
            return self.ONE
        if a == self.ONE:
            return self.ZERO
        key = ("neg", a)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def neg_raw(self, a: int) -> int:
        """Un-simplified negation node (preserves explicit syntactic steps)."""
        key = ("neg", a)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def disj(self, a: int, b: int) -> int:
        key = ("disj", a, b)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def conj(self, a: int, b: int) -> int:
        key = ("conj", a, b)
        if key not in self.intern:
            self.intern[key] = len(self.nodes)
            self.nodes.append(key)
        return self.intern[key]

    def xor(self, a: int, b: int) -> int:
        # a ^ b = (a & ~b) | (~a & b)
        return self.disj(self.conj(a, self.neg_raw(b)), self.conj(self.neg_raw(a), b))

    def maj3(self, a: int, b: int, c: int) -> int:
        return self.disj(self.conj(a, b), self.disj(self.conj(a, c), self.conj(b, c)))

    def eval(self, root: int, env: Dict[int, bool]) -> bool:
        memo: Dict[int, bool] = {}

        def _ev(nid: int) -> bool:
            if nid in memo:
                return memo[nid]
            node = self.nodes[nid]
            op = node[0]
            if op == "zero":
                res = False
            elif op == "one":
                res = True
            elif op == "var":
                res = env.get(node[1], False)
            elif op == "neg":
                res = not _ev(node[1])
            elif op == "disj":
                res = _ev(node[1]) or _ev(node[2])
            elif op == "conj":
                res = _ev(node[1]) and _ev(node[2])
            else:
                raise ValueError(f"Unknown op: {op}")
            memo[nid] = res
            return res

        return _ev(root)

    def dag_size(self, root: int) -> int:
        seen: set[int] = set()
        stack = [root]
        while stack:
            nid = stack.pop()
            if nid in seen:
                continue
            seen.add(nid)
            node = self.nodes[nid]
            if node[0] == "neg":
                stack.append(node[1])
            elif node[0] in ("disj", "conj"):
                stack.append(node[1])
                stack.append(node[2])
        return len(seen)


# ---------------------------------------------------------------------------
# 2. Local Step Equivalence Checker (Z3 or PySAT Cadical195)
# ---------------------------------------------------------------------------

def check_step_mismatch(
    pool: CircuitPool, a_root: int, b_root: int, num_vars: int
) -> Optional[Dict[int, bool]]:
    """
    Checks whether E_a(x) != E_b(x) is satisfiable.
    Returns a witnessing assignment env : {0..num_vars-1 -> bool} if a mismatch exists,
    or None if E_a === E_b.
    """
    if HAS_Z3:
        solver = z3.Solver()
        zvars = {i: z3.Bool(f"x_{i}") for i in range(num_vars)}
        memo: Dict[int, z3.BoolRef] = {}

        def _to_z3(nid: int) -> z3.BoolRef:
            if nid in memo:
                return memo[nid]
            node = pool.nodes[nid]
            op = node[0]
            if op == "zero":
                res = z3.BoolVal(False)
            elif op == "one":
                res = z3.BoolVal(True)
            elif op == "var":
                res = zvars[node[1]]
            elif op == "neg":
                res = z3.Not(_to_z3(node[1]))
            elif op == "disj":
                res = z3.Or(_to_z3(node[1]), _to_z3(node[2]))
            elif op == "conj":
                res = z3.And(_to_z3(node[1]), _to_z3(node[2]))
            else:
                raise ValueError(op)
            memo[nid] = res
            return res

        solver.add(_to_z3(a_root) != _to_z3(b_root))
        if solver.check() == z3.sat:
            m = solver.model()
            return {i: bool(z3.is_true(m.eval(zvars[i], model_completion=True))) for i in range(num_vars)}
        return None

    # Tseitin encoding into PySAT (Cadical195)
    clauses: List[List[int]] = []
    next_lit = num_vars + 1
    var_map: Dict[int, int] = {i: i + 1 for i in range(num_vars)}
    node_lit: Dict[int, int] = {}

    def _tseitin(nid: int) -> int:
        nonlocal next_lit
        if nid in node_lit:
            return node_lit[nid]
        node = pool.nodes[nid]
        op = node[0]
        if op == "zero":
            lit = next_lit
            next_lit += 1
            clauses.append([-lit])
        elif op == "one":
            lit = next_lit
            next_lit += 1
            clauses.append([lit])
        elif op == "var":
            lit = var_map[node[1]]
        elif op == "neg":
            c = _tseitin(node[1])
            lit = next_lit
            next_lit += 1
            # lit <-> -c
            clauses.append([-lit, -c])
            clauses.append([lit, c])
        elif op == "disj":
            la = _tseitin(node[1])
            lb = _tseitin(node[2])
            lit = next_lit
            next_lit += 1
            # lit <-> la \/ lb
            clauses.append([-la, lit])
            clauses.append([-lb, lit])
            clauses.append([-lit, la, lb])
        elif op == "conj":
            la = _tseitin(node[1])
            lb = _tseitin(node[2])
            lit = next_lit
            next_lit += 1
            # lit <-> la /\ lb
            clauses.append([-lit, la])
            clauses.append([-lit, lb])
            clauses.append([lit, -la, -lb])
        else:
            raise ValueError(op)
        node_lit[nid] = lit
        return lit

    la = _tseitin(a_root)
    lb = _tseitin(b_root)
    # Require la != lb: (la \/ lb) /\ (-la \/ -lb)
    clauses.append([la, lb])
    clauses.append([-la, -lb])

    with Cadical195(bootstrap_with=clauses) as solver:
        if solver.solve():
            model = set(solver.get_model())
            return {i: ((i + 1) in model) for i in range(num_vars)}
    return None


# ---------------------------------------------------------------------------
# 3. Binary-Search Bug Localization & Parallel Local Step Extraction
# ---------------------------------------------------------------------------

def binary_search_bug(
    pool: CircuitPool, chain: List[int], x_star: Dict[int, bool]
) -> Tuple[int, int]:
    """
    Mirrors Lean `findBrokenStep`:
    Given chain [E_0, ..., E_t] with eval(E_0, x*) = False and eval(E_t, x*) = True,
    locates idx < t with eval(E_idx, x*) = False and eval(E_{idx+1}, x*) = True
    in <= ceil(log2 t) midpoint evaluations.
    Returns (idx, eval_queries_used).
    """
    lo = 0
    hi = len(chain) - 1
    assert hi >= 1
    assert pool.eval(chain[lo], x_star) is False
    assert pool.eval(chain[hi], x_star) is True
    queries = 0
    while hi > lo + 1:
        mid = (lo + hi) // 2
        val = pool.eval(chain[mid], x_star)
        queries += 1
        if val:
            hi = mid
        else:
            lo = mid
    return lo, queries


def parallel_local_step_bug_extract(
    pool: CircuitPool, chain: List[int], num_vars: int
) -> Dict:
    """
    Simulates TC^0 / parallel local consistency checking across all steps (E_i, E_{i+1})
    in the alleged ≈-chain, followed by O(log t) binary-search verification.
    """
    t0 = time.perf_counter()
    t = len(chain) - 1
    broken_steps: List[Tuple[int, Dict[int, bool]]] = []
    for i in range(t):
        witness = check_step_mismatch(pool, chain[i], chain[i + 1], num_vars)
        if witness is not None:
            broken_steps.append((i, witness))

    # Prefer a witness that also falsifies E_0 (and satisfies E_t)
    chosen_step, x_star = broken_steps[0]
    for step_idx, w in broken_steps:
        if not pool.eval(chain[0], w) and pool.eval(chain[t], w):
            chosen_step, x_star = step_idx, w
            break

    bs_idx, bs_queries = binary_search_bug(pool, chain, x_star)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    e0_val = pool.eval(chain[0], x_star)
    et_val = pool.eval(chain[t], x_star)
    ei_val = pool.eval(chain[bs_idx], x_star)
    ei1_val = pool.eval(chain[bs_idx + 1], x_star)

    return {
        "chain_len_t": t,
        "num_vars": num_vars,
        "solver_backend": "z3" if HAS_Z3 else "pysat_cadical195",
        "broken_steps_detected": [s for s, _ in broken_steps],
        "broken_step_parallel_local": chosen_step,
        "broken_step_binary_search": bs_idx,
        "binary_search_queries": bs_queries,
        "ceil_log2_t": math.ceil(math.log2(t)) if t > 1 else 0,
        "E0_eval_x_star": e0_val,
        "Et_eval_x_star": et_val,
        "E_idx_eval_x_star": ei_val,
        "E_idx_plus_1_eval_x_star": ei1_val,
        "verified_falsifies_E0": (e0_val is False and et_val is True),
        "verified_broken_transition": (ei_val is False and ei1_val is True),
        "extracted_x_star": {str(k): v for k, v in sorted(x_star.items())},
        "extract_time_ms": round(elapsed_ms, 3),
    }


# ---------------------------------------------------------------------------
# 4. Benchmark Chain Generators (Corrupted ≈-Chains)
# ---------------------------------------------------------------------------

def build_cnf_circuit(pool: CircuitPool, clauses: List[List[int]]) -> int:
    """Builds a DeMorgan conjunction of 1-indexed signed-literal clauses."""
    clause_nodes = []
    for cl in clauses:
        lits = []
        for lit in cl:
            v = pool.var(abs(lit) - 1)
            lits.append(v if lit > 0 else pool.neg_raw(v))
        acc = lits[0]
        for l in lits[1:]:
            acc = pool.disj(acc, l)
        clause_nodes.append(acc)
    acc = clause_nodes[0]
    for c in clause_nodes[1:]:
        acc = pool.conj(acc, c)
    return acc


def gen_corrupted_php_chain(pigeons: int = 4, holes: int = 3) -> Tuple[CircuitPool, List[int], int]:
    """
    PHP_4^3: 4 pigeons, 3 holes.
    Alleged ≈-chain purporting to prove ¬PHP ≡ 1, EXCEPT PHP is SAT if we
    corrupt/omit a hole-conflict or consider a satisfiable 3-pigeon 3-hole sub-instance
    or drop a clause mid-chain. Here we build a chain starting at E_0 = ¬PHP_3^3
    (which is NOT a tautology because PHP_3^3 is SAT!) and at step i* silently
    drops the satisfiable branch / short-circuits to 1.
    """
    pool = CircuitPool()
    n_p, n_h = 3, 3
    num_vars = n_p * n_h

    def v_idx(p: int, h: int) -> int:
        return p * n_h + h + 1

    clauses: List[List[int]] = []
    for p in range(n_p):
        clauses.append([v_idx(p, h) for h in range(n_h)])
    for h in range(n_h):
        for p1 in range(n_p):
            for p2 in range(p1 + 1, n_p):
                clauses.append([-v_idx(p1, h), -v_idx(p2, h)])

    php_cnf = build_cnf_circuit(pool, clauses)
    e0 = pool.neg_raw(php_cnf)  # ¬PHP_3^3: false on any valid bijection!

    # Valid BA steps (double negation / commutativity / associativity wrappers)
    chain = [e0]
    cur = e0
    for _ in range(5):
        cur = pool.disj(pool.ZERO, cur)  # 0 \/ cur ≈ cur (valid BA step)
        chain.append(cur)

    # Corrupted step at i*=5: illicitly collapses to (cur \/ ¬cur) ≈ 1
    corrupted = pool.disj(cur, pool.neg_raw(cur))
    chain.append(corrupted)
    # Valid BA steps from (cur \/ ¬cur) to 1
    chain.append(pool.ONE)
    chain.append(pool.neg_raw(pool.ZERO))
    chain.append(pool.ONE)
    return pool, chain, num_vars


def gen_corrupted_goldreich_chain(n: int = 10, seed: int = 42) -> Tuple[CircuitPool, List[int], int]:
    """
    Goldreich XOR-MAJ3 PRG output consistency check:
    E_0 = ¬(PRG(x) == y_planted), which is FALSE at x = x_planted.
    A corrupted ≈-chain wraps E_0 in valid BA identities, then silently flips one
    MAJ3 predicate to a tautology at step i*=6.
    """
    rng = random.Random(seed)
    pool = CircuitPool()
    x_planted = {i: bool(rng.randint(0, 1)) for i in range(n)}

    def eval_xormaj3(env: Dict[int, bool], idxs: Tuple[int, int, int, int, int]) -> bool:
        a, b, c, d, e = [env[k] for k in idxs]
        maj = (c and d) or (c and e) or (d and e)
        return (a ^ b) ^ maj

    # Build m = n output constraints
    eq_nodes = []
    for _ in range(n):
        idxs = tuple(rng.sample(range(n), 5))
        y_bit = eval_xormaj3(x_planted, idxs)  # type: ignore
        va, vb, vc, vd, ve = [pool.var(k) for k in idxs]
        gate = pool.xor(pool.xor(va, vb), pool.maj3(vc, vd, ve))
        eq_nodes.append(gate if y_bit else pool.neg_raw(gate))

    sat_formula = eq_nodes[0]
    for g in eq_nodes[1:]:
        sat_formula = pool.conj(sat_formula, g)

    e0 = pool.neg_raw(sat_formula)  # False at x_planted!
    chain = [e0]
    cur = e0
    for _ in range(6):
        cur = pool.conj(pool.ONE, cur)  # 1 /\ cur ≈ cur (valid BA step)
        chain.append(cur)

    # Corrupted step at i*=6: drops sat_formula inside ¬sat_formula -> ¬0 -> 1
    chain.append(pool.neg_raw(pool.ZERO))
    for _ in range(4):
        chain.append(pool.ONE)
    return pool, chain, n


def gen_corrupted_3sat_chain(n: int = 18, alpha: float = 4.26, seed: int = 108) -> Tuple[CircuitPool, List[int], int]:
    """
    Random planted/near-threshold 3-SAT at alpha = 4.26 (m = round(4.26 * n)).
    Plant a satisfying assignment x_planted so E_0 = ¬F is falsifiable,
    then inject a corrupted rewrite step at i*=7.
    """
    rng = random.Random(seed)
    pool = CircuitPool()
    m = round(alpha * n)
    x_planted = {i: bool(rng.randint(0, 1)) for i in range(n)}
    clauses: List[List[int]] = []
    while len(clauses) < m:
        vs = rng.sample(range(1, n + 1), 3)
        signs = [rng.choice([-1, 1]) for _ in range(3)]
        cl = [s * v for s, v in zip(signs, vs)]
        # Ensure x_planted satisfies cl
        if any((x_planted[abs(l) - 1] if l > 0 else not x_planted[abs(l) - 1]) for l in cl):
            clauses.append(cl)

    f_cnf = build_cnf_circuit(pool, clauses)
    e0 = pool.neg_raw(f_cnf)
    chain = [e0]
    cur = e0
    for k in range(7):
        if k % 2 == 0:
            cur = pool.disj(pool.ZERO, cur)
        else:
            cur = pool.conj(pool.ONE, cur)
        chain.append(cur)

    # Corrupted step at i*=7: illicitly replaces cur with (x_0 \/ ¬x_0)
    x0 = pool.var(0)
    chain.append(pool.disj(x0, pool.neg_raw(x0)))
    chain.append(pool.ONE)
    chain.append(pool.ONE)
    return pool, chain, n


def gen_faulty_demorgan_fanout2_chain(n: int = 6) -> Tuple[CircuitPool, List[int], int]:
    r"""
    Models the Datta-Dutta v1 fan-out-2 simultaneous-rewrite bug:
    A shared subcircuit S = (x0 /\ x1) has fan-out 2 in E_0 = (S /\ x2) \/ (~S /\ ~x2),
    which is falsified whenever S != x2.
    Steps 1..3: valid BA commutativity / zero-identity rewrites.
    Step 4 (buggy fan-out-2 simultaneous rewrite): mutates one fan-out branch of S
    inconsistently, collapsing the circuit to a tautology.
    """
    pool = CircuitPool()
    x0, x1, x2 = pool.var(0), pool.var(1), pool.var(2)
    shared_s = pool.conj(x0, x1)  # fan-out 2!
    # E_0: (S /\ x2) \/ (¬S /\ ¬x2)  (false whenever S != x2)
    branch1 = pool.conj(shared_s, x2)
    branch2 = pool.conj(pool.neg_raw(shared_s), pool.neg_raw(x2))
    e0 = pool.disj(branch1, branch2)

    chain = [e0]
    # Step 1: valid commutativity on branch1
    b1_comm = pool.conj(x2, shared_s)
    chain.append(pool.disj(b1_comm, branch2))
    # Step 2: valid DeMorgan-style padding 0 \/ ...
    chain.append(pool.disj(pool.ZERO, chain[-1]))
    # Step 3: valid commutativity
    chain.append(pool.disj(chain[-1], pool.ZERO))
    # Step 4 (BUGGY simultaneous fan-out-2 mutation): mutates one branch of shared_s
    # to x2 (breaking fan-out consistency!) so it becomes (x2 \/ ¬x2) /\ 1 = 1!
    mutated_branch2 = pool.conj(pool.neg_raw(x2), pool.neg_raw(x2))
    # And mutates b1_comm's shared_s to ONE:
    mutated_b1 = pool.conj(x2, pool.ONE)
    chain.append(pool.disj(mutated_b1, mutated_branch2))
    # Wait: (x2 /\ 1) \/ (¬x2 /\ ¬x2) is actually a tautology (x2 \/ ¬x2)!
    # Valid BA steps to 1:
    chain.append(pool.disj(x2, pool.neg_raw(x2)))
    chain.append(pool.ONE)
    return pool, chain, n


# ---------------------------------------------------------------------------
# 5. K^t Witness-Compression & Symmetry-of-Information (SoI) Diagnostic
# ---------------------------------------------------------------------------

def _bits_to_bytes(bit_list: List[int]) -> bytes:
    """Pack a list of 0/1 bits into bytes (MSB first, padded to full bytes)."""
    out = bytearray()
    for i in range(0, len(bit_list), 8):
        byte = 0
        for j in range(8):
            if i + j < len(bit_list):
                byte = (byte << 1) | (bit_list[i + j] & 1)
            else:
                byte <<= 1
        out.append(byte)
    return bytes(out)


def _kt_zlib(data: bytes) -> int:
    """Time-bounded Kolmogorov proxy K^t(data) in bits via zlib level-9."""
    return len(zlib.compress(data, level=9)) * 8


def _kt_zlib_cond(target: bytes, cond: bytes) -> int:
    """Conditional K^t(target | cond) in bits using zlib preset dictionary."""
    comp = zlib.compressobj(level=9, zdict=cond)
    compressed = comp.compress(target) + comp.flush()
    return len(compressed) * 8


def map_schoolbook_mult(x_bits: List[int]) -> List[int]:
    n = len(x_bits)
    half = n // 2
    a = sum((b << i) for i, b in enumerate(x_bits[:half]))
    b = sum((b << i) for i, b in enumerate(x_bits[half:2 * half]))
    prod = a * b
    return [(prod >> i) & 1 for i in range(n)]


def map_goldreich_xormaj3(x_bits: List[int], seed: int = 77) -> List[int]:
    n = len(x_bits)
    rng = random.Random(seed + n)
    out = []
    for _ in range(n):
        a, b, c, d, e = rng.sample(range(n), 5)
        maj = (x_bits[c] & x_bits[d]) | (x_bits[c] & x_bits[e]) | (x_bits[d] & x_bits[e])
        out.append(x_bits[a] ^ x_bits[b] ^ maj)
    return out


def map_keccak_chi_4round(x_bits: List[int]) -> List[int]:
    n = len(x_bits)
    state = list(x_bits)
    for r in range(4):
        nxt = [0] * n
        for i in range(n):
            nxt[i] = state[i] ^ ((1 - state[(i + 1) % n]) & state[(i + 2) % n])
        # Linear diffusion between rounds
        state = [nxt[i] ^ nxt[(i + 3 + r) % n] for i in range(n)]
    return state


def make_random_permutation_fn(n: int, seed: int = 999):
    """Deterministic 4-round Feistel permutation on n-bit strings (bijection for even n)."""
    half = n // 2
    mask_l = (1 << half) - 1
    mask_r = (1 << (n - half)) - 1

    def _feistel(x_bits: List[int]) -> List[int]:
        val = sum((b << i) for i, b in enumerate(x_bits))
        L = val & mask_l
        R = (val >> half) & mask_r
        for r in range(4):
            # Pseudorandom round function
            h = ((R * 0x9E3779B97F4A7C15 + (r + 1) * 0xBF58476D1CE4E5B9 + seed) >> 17) & mask_l
            L, R = R & mask_l, (L ^ h) & mask_r
        out_val = (R << half) | L
        return [(out_val >> i) & 1 for i in range(n)]

    return _feistel


def run_kt_soi_diagnostic(
    ns: Tuple[int, ...] = (6, 8, 10, 12, 14),
    batch_samples: int = 128,
    seed: int = 2026,
) -> List[Dict]:
    """
    Measures K^t(x), K^t(f(x)), K^t(x, f(x)), K^t(f(x)|x), K^t(x|f(x)),
    and the Symmetry-of-Information (SoI) deficits:
      delta_soi_forward = K^t(x, f(x)) - (K^t(x) + K^t(f(x) | x))
      soi_asymmetry     = (K^t(f(x)) + K^t(x | f(x))) - (K^t(x) + K^t(f(x) | x))
    """
    rng = random.Random(seed)
    results: List[Dict] = []

    for n in ns:
        samples_x = [[rng.randint(0, 1) for _ in range(n)] for _ in range(batch_samples)]
        maps = {
            "schoolbook_mult": map_schoolbook_mult,
            "goldreich_xormaj3": map_goldreich_xormaj3,
            "keccak_chi_4round": map_keccak_chi_4round,
            "random_permutation": make_random_permutation_fn(n),
        }
        x_flat = [bit for s in samples_x for bit in s]
        x_bytes = _bits_to_bytes(x_flat)
        kt_x = _kt_zlib(x_bytes)

        for map_name, fn in maps.items():
            samples_y = [fn(s) for s in samples_x]
            y_flat = [bit for s in samples_y for bit in s]
            xy_flat = [bit for sx, sy in zip(samples_x, samples_y) for bit in (sx + sy)]

            y_bytes = _bits_to_bytes(y_flat)
            xy_bytes = _bits_to_bytes(xy_flat)

            kt_y = _kt_zlib(y_bytes)
            kt_xy = _kt_zlib(xy_bytes)
            kt_y_given_x = _kt_zlib_cond(y_bytes, x_bytes)
            kt_x_given_y = _kt_zlib_cond(x_bytes, y_bytes)

            delta_soi_fwd = kt_xy - (kt_x + kt_y_given_x)
            delta_soi_rev = (kt_y + kt_x_given_y) - kt_xy
            soi_asymmetry = (kt_y + kt_x_given_y) - (kt_x + kt_y_given_x)

            # Compression ratio of output vs raw bits
            raw_bits = batch_samples * n
            output_compress_ratio = round(kt_y / raw_bits, 4)

            results.append({
                "n": n,
                "map": map_name,
                "batch_samples": batch_samples,
                "raw_bits_per_side": raw_bits,
                "Kt_x_bits": kt_x,
                "Kt_y_bits": kt_y,
                "Kt_xy_bits": kt_xy,
                "Kt_y_given_x_bits": kt_y_given_x,
                "Kt_x_given_y_bits": kt_x_given_y,
                "delta_SoI_forward_bits": delta_soi_fwd,
                "delta_SoI_reverse_bits": delta_soi_rev,
                "SoI_asymmetry_bits": soi_asymmetry,
                "output_compression_ratio": output_compress_ratio,
            })
    return results


# ---------------------------------------------------------------------------
# 6. Main Entrypoint
# ---------------------------------------------------------------------------

def main() -> None:
    benchmarks = {
        "PHP_3_3_corrupted": gen_corrupted_php_chain(4, 3),
        "Goldreich_XOR_MAJ3_corrupted": gen_corrupted_goldreich_chain(10),
        "Random_3SAT_alpha_4_26_corrupted": gen_corrupted_3sat_chain(18, 4.26),
        "DattaDutta_v1_DeMorgan_fanout2_bug": gen_faulty_demorgan_fanout2_chain(6),
    }

    bug_extraction_results: Dict[str, Dict] = {}
    for name, (pool, chain, num_vars) in benchmarks.items():
        res = parallel_local_step_bug_extract(pool, chain, num_vars)
        res["E0_dag_size"] = pool.dag_size(chain[0])
        bug_extraction_results[name] = res

    soi_results = run_kt_soi_diagnostic(ns=(6, 8, 10, 12, 14), batch_samples=128)

    output = {
        "ataque": "ATAQUE-08",
        "title": "Constructive Bug-Extraction (arXiv:2611.08305 / Li-Li-Ren STOC 2026) & K^t Witness-Compression SoI Diagnostic (Hirahara FOCS 2024)",
        "solver_backend": "z3" if HAS_Z3 else "pysat_cadical195",
        "bug_extraction_benchmarks": bug_extraction_results,
        "kt_soi_diagnostic": soi_results,
    }

    out_path = Path(__file__).resolve().parents[2] / "results" / "proof_bug_extractor_results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2))
    print(f"Wrote {out_path}")
    for name, r in bug_extraction_results.items():
        print(
            f"[BUG-EXTRACT] {name}: t={r['chain_len_t']}, "
            f"broken_idx={r['broken_step_binary_search']}, "
            f"queries={r['binary_search_queries']}/{r['ceil_log2_t']}, "
            f"falsifies_E0={r['verified_falsifies_E0']}, "
            f"broken_step_ok={r['verified_broken_transition']}, "
            f"time={r['extract_time_ms']}ms"
        )
    print(f"[Kt-SoI] Completed {len(soi_results)} diagnostics across n in {{6,8,10,12,14}}.")


if __name__ == "__main__":
    main()
