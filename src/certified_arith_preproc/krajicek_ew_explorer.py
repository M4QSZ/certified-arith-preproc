"""
Exact Computational Laboratory for Jan Krajicek's Rewrite Proof System (A ≈ B)
from arXiv:2606.13367v2 ("Extended Frege proofs, circuits and rewriting", Oct 2026).

Implements:
1. Hash-consed DeMorgan DAG circuits (identifying identical subformulas).
2. Exact polynomial-time `are_approx(C, D)` decider (Def 3.1 & Lemma 3.2):
   `A ≈ B` iff `Fla[A] ~_BA Fla[B]` (single-occurrence replacement at a path
   `p in {0, 1}^*` under the 12 Boolean Algebra equations `BA` of Sec. 2).
3. Exact Bidirectional BFS in `(Circuits, ≈)` for geodesic distances `d_≈(C, D)`.
4. Constructive verified BA rewrite compiler + geodesic shortcutting for larger
   benchmarks (3-bit XOR associativity, PHP_3^2, etc.), with 100% step-by-step
   verification via `are_approx` and exact truth-table equivalence.
5. Complexity functionals along every chain: DAG size `|E_i|_DAG`, unwound formula
   size `|Fla[E_i]|`, fan-out unsharing metrics, multiplicative AND-depth, and
   exact Fourier / average-sensitivity energy profiles.
"""

from __future__ import annotations

import json
import math
import time
from collections import deque
from pathlib import Path
from typing import Callable, Dict, List, Optional, Set, Tuple

NodeKey = Tuple


class DAGStore:
    """Global hash-consed store of DeMorgan DAG circuits.

    Each distinct formula `Fla[C]` has a unique canonical integer node ID.
    Consequently, `Fla[c] == Fla[d]` iff `c == d` in O(1) time.
    """

    def __init__(self) -> None:
        self._key_to_id: Dict[NodeKey, int] = {}
        self._id_to_key: List[NodeKey] = []
        self._approx_cache: Dict[Tuple[int, int], Optional[dict]] = {}
        self.ZERO = self._intern(("0",))
        self.ONE = self._intern(("1",))

    def _intern(self, key: NodeKey) -> int:
        cid = self._key_to_id.get(key)
        if cid is None:
            cid = len(self._id_to_key)
            self._key_to_id[key] = cid
            self._id_to_key.append(key)
        return cid

    def key(self, cid: int) -> NodeKey:
        return self._id_to_key[cid]

    def var(self, name: str) -> int:
        return self._intern(("v", name))

    def neg(self, a: int) -> int:
        return self._intern(("!", a))

    def disj(self, a: int, b: int) -> int:
        return self._intern(("|", a, b))

    def conj(self, a: int, b: int) -> int:
        return self._intern(("&", a, b))

    def xor(self, a: int, b: int) -> int:
        """Standard DeMorgan XOR: a ^ b := (a & ~b) v (~a & b) (fanout 2 on a, b)."""
        return self.disj(self.conj(a, self.neg(b)), self.conj(self.neg(a), b))

    def disj_many(self, items: List[int]) -> int:
        assert items, "disj_many requires non-empty list"
        acc = items[0]
        for x in items[1:]:
            acc = self.disj(acc, x)
        return acc

    def conj_many(self, items: List[int]) -> int:
        assert items, "conj_many requires non-empty list"
        acc = items[0]
        for x in items[1:]:
            acc = self.conj(acc, x)
        return acc

    # ------------------------------------------------------------------
    # Structural & complexity metrics on a hash-consed DAG circuit
    # ------------------------------------------------------------------

    def reachable_nodes(self, root: int) -> Set[int]:
        visited: Set[int] = set()
        stack = [root]
        while stack:
            u = stack.pop()
            if u in visited:
                continue
            visited.add(u)
            k = self._id_to_key[u]
            op = k[0]
            if op == "!":
                stack.append(k[1])
            elif op in ("|", "&"):
                stack.append(k[1])
                stack.append(k[2])
        return visited

    def dag_size(self, root: int) -> int:
        return len(self.reachable_nodes(root))

    def formula_size(self, root: int) -> int:
        memo: Dict[int, int] = {}

        def rec(u: int) -> int:
            if u in memo:
                return memo[u]
            k = self._id_to_key[u]
            op = k[0]
            if op in ("0", "1", "v"):
                val = 1
            elif op == "!":
                val = 1 + rec(k[1])
            else:
                val = 1 + rec(k[1]) + rec(k[2])
            memo[u] = val
            return val

        return rec(root)

    def and_depth(self, root: int) -> int:
        """Multiplicative AND-depth (max number of '&' gates on any root-to-leaf path)."""
        memo: Dict[int, int] = {}

        def rec(u: int) -> int:
            if u in memo:
                return memo[u]
            k = self._id_to_key[u]
            op = k[0]
            if op in ("0", "1", "v"):
                val = 0
            elif op == "!":
                val = rec(k[1])
            elif op == "|":
                val = max(rec(k[1]), rec(k[2]))
            else:
                val = 1 + max(rec(k[1]), rec(k[2]))
            memo[u] = val
            return val

        return rec(root)

    def gate_depth(self, root: int) -> int:
        memo: Dict[int, int] = {}

        def rec(u: int) -> int:
            if u in memo:
                return memo[u]
            k = self._id_to_key[u]
            op = k[0]
            if op in ("0", "1", "v"):
                val = 0
            elif op == "!":
                val = 1 + rec(k[1])
            else:
                val = 1 + max(rec(k[1]), rec(k[2]))
            memo[u] = val
            return val

        return rec(root)

    def fanout_stats(self, root: int) -> Dict[str, int]:
        """Compute max DAG fanout (parent-wire count) and max formula occurrence count."""
        nodes = self.reachable_nodes(root)
        dag_fanout: Dict[int, int] = {u: 0 for u in nodes}
        for u in nodes:
            k = self._id_to_key[u]
            op = k[0]
            if op == "!":
                dag_fanout[k[1]] += 1
            elif op in ("|", "&"):
                dag_fanout[k[1]] += 1
                dag_fanout[k[2]] += 1

        # Top-down tree occurrence count in Fla[root]
        indeg = {u: dag_fanout[u] for u in nodes}
        occ = {u: 0 for u in nodes}
        occ[root] = 1
        q = deque([u for u in nodes if indeg[u] == 0])
        while q:
            u = q.popleft()
            k = self._id_to_key[u]
            op = k[0]
            if op == "!":
                occ[k[1]] += occ[u]
                indeg[k[1]] -= 1
                if indeg[k[1]] == 0:
                    q.append(k[1])
            elif op in ("|", "&"):
                occ[k[1]] += occ[u]
                indeg[k[1]] -= 1
                if indeg[k[1]] == 0:
                    q.append(k[1])
                occ[k[2]] += occ[u]
                indeg[k[2]] -= 1
                if indeg[k[2]] == 0:
                    q.append(k[2])

        non_leaf_nodes = [u for u in nodes if self._id_to_key[u][0] in ("!", "|", "&")]
        max_gate_fanout = max((dag_fanout[u] for u in non_leaf_nodes), default=0)
        max_gate_occ = max((occ[u] for u in non_leaf_nodes), default=0)
        shared_gates = sum(1 for u in non_leaf_nodes if dag_fanout[u] >= 2)
        return {
            "max_dag_fanout_all": max(dag_fanout.values(), default=0),
            "max_gate_fanout": max_gate_fanout,
            "max_gate_tree_occ": max_gate_occ,
            "shared_gate_count": shared_gates,
        }

    def variables(self, root: int) -> List[str]:
        vs = sorted(
            self._id_to_key[u][1]
            for u in self.reachable_nodes(root)
            if self._id_to_key[u][0] == "v"
        )
        return vs

    def pretty(self, root: int, max_len: int = 140) -> str:
        def rec(u: int) -> str:
            k = self._id_to_key[u]
            op = k[0]
            if op in ("0", "1"):
                return op
            if op == "v":
                return k[1]
            if op == "!":
                inner = self._id_to_key[k[1]]
                if inner[0] in ("0", "1", "v", "!"):
                    return f"~{rec(k[1])}"
                return f"~({rec(k[1])})"
            if op == "|":
                return f"({rec(k[1])} v {rec(k[2])})"
            return f"({rec(k[1])} & {rec(k[2])})"

        s = rec(root)
        if len(s) > max_len:
            return s[: max_len - 3] + "..."
        return s

    # ------------------------------------------------------------------
    # Exact semantic evaluation & Fourier / sensitivity energy
    # ------------------------------------------------------------------

    def truth_table(self, root: int, var_names: List[str]) -> int:
        """Return bitmask truth table over 2^n assignments (bit i = eval on assignment i)."""
        n = len(var_names)
        full_mask = (1 << (1 << n)) - 1
        var_masks: Dict[str, int] = {}
        for idx, name in enumerate(var_names):
            m = 0
            for a in range(1 << n):
                if (a >> idx) & 1:
                    m |= 1 << a
            var_masks[name] = m

        memo: Dict[int, int] = {}

        def rec(u: int) -> int:
            if u in memo:
                return memo[u]
            k = self._id_to_key[u]
            op = k[0]
            if op == "0":
                val = 0
            elif op == "1":
                val = full_mask
            elif op == "v":
                val = var_masks[k[1]]
            elif op == "!":
                val = full_mask ^ rec(k[1])
            elif op == "|":
                val = rec(k[1]) | rec(k[2])
            else:
                val = rec(k[1]) & rec(k[2])
            memo[u] = val
            return val

        return rec(root)

    @staticmethod
    def fourier_sensitivity_from_tt(tt: int, n: int) -> Dict[str, float]:
        """Exact average sensitivity I(f) and Fourier L1 / spectral entropy via FWHT."""
        size = 1 << n
        # Total influence / average sensitivity: I(f) = (1/2^n) sum_x sum_i [f(x) != f(x^e_i)]
        sens_sum = 0
        for i in range(n):
            bit = 1 << i
            for x in range(size):
                if ((tt >> x) & 1) != ((tt >> (x ^ bit)) & 1):
                    sens_sum += 1
        avg_sensitivity = sens_sum / size

        # Fourier coefficients of f: {0,1}^n -> {-1, +1} (True -> -1, False -> +1)
        vals = [-1.0 if ((tt >> x) & 1) else 1.0 for x in range(size)]
        h = 1
        while h < size:
            for i in range(0, size, h * 2):
                for j in range(i, i + h):
                    u = vals[j]
                    v = vals[j + h]
                    vals[j] = u + v
                    vals[j + h] = u - v
            h *= 2
        coeffs = [v / size for v in vals]
        fourier_l1 = sum(abs(c) for c in coeffs)
        spectral_entropy = 0.0
        for c in coeffs:
            p = c * c
            if p > 1e-15:
                spectral_entropy -= p * math.log2(p)
        return {
            "avg_sensitivity": round(avg_sensitivity, 6),
            "fourier_l1": round(fourier_l1, 6),
            "spectral_entropy": round(spectral_entropy, 6),
        }

    def subcircuit_energy_profile(self, root: int, var_names: List[str]) -> Dict[str, float]:
        """Sum and max of sensitivity & Fourier L1 across all distinct subcircuits in DAG(root)."""
        if len(var_names) > 8:
            return {"subcircuit_sens_sum": -1.0, "subcircuit_fourier_l1_sum": -1.0}
        nodes = self.reachable_nodes(root)
        n = len(var_names)
        sens_sum = 0.0
        l1_sum = 0.0
        for u in nodes:
            tt = self.truth_table(u, var_names)
            fs = self.fourier_sensitivity_from_tt(tt, n)
            sens_sum += fs["avg_sensitivity"]
            l1_sum += fs["fourier_l1"]
        return {
            "subcircuit_sens_sum": round(sens_sum, 4),
            "subcircuit_fourier_l1_sum": round(l1_sum, 4),
        }

    # ------------------------------------------------------------------
    # Exact p-time `are_approx(C, D)` decider (Def 3.1 & Lemma 3.2)
    # ------------------------------------------------------------------

    def _match_ba_fwd(self, c: int, d: int) -> Optional[str]:
        """Check if (Fla[c], Fla[d]) matches one of the 12 BA axioms in forward direction."""
        kc = self._id_to_key[c]
        kd = self._id_to_key[d]

        # 1. ~0 = 1
        if kc == ("!", self.ZERO) and d == self.ONE:
            return "negZero"
        # 2. ~1 = 0
        if kc == ("!", self.ONE) and d == self.ZERO:
            return "negOne"
        # 3. 0 v a = a
        if kc[0] == "|" and kc[1] == self.ZERO and kc[2] == d:
            return "disjZeroLeft"
        # 4. 1 & a = a
        if kc[0] == "&" and kc[1] == self.ONE and kc[2] == d:
            return "conjOneLeft"
        # 5. a v ~a = 1
        if kc[0] == "|" and d == self.ONE:
            a, b = kc[1], kc[2]
            if self._id_to_key[b] == ("!", a):
                return "disjCompl"
        # 6. a & ~a = 0
        if kc[0] == "&" and d == self.ZERO:
            a, b = kc[1], kc[2]
            if self._id_to_key[b] == ("!", a):
                return "conjCompl"
        # 7. a v b = b v a
        if kc[0] == "|" and kd[0] == "|" and kc[1] == kd[2] and kc[2] == kd[1]:
            return "disjComm"
        # 8. a & b = b & a
        if kc[0] == "&" and kd[0] == "&" and kc[1] == kd[2] and kc[2] == kd[1]:
            return "conjComm"
        # 9. a v (b v c) = (a v b) v c
        if kc[0] == "|" and kd[0] == "|":
            kcr = self._id_to_key[kc[2]]
            kdl = self._id_to_key[kd[1]]
            if kcr[0] == "|" and kdl[0] == "|":
                if kc[1] == kdl[1] and kcr[1] == kdl[2] and kcr[2] == kd[2]:
                    return "disjAssoc"
        # 10. a & (b & c) = (a & b) & c
        if kc[0] == "&" and kd[0] == "&":
            kcr = self._id_to_key[kc[2]]
            kdl = self._id_to_key[kd[1]]
            if kcr[0] == "&" and kdl[0] == "&":
                if kc[1] == kdl[1] and kcr[1] == kdl[2] and kcr[2] == kd[2]:
                    return "conjAssoc"
        # 11. a v (b & c) = (a v b) & (a v c)
        if kc[0] == "|" and kd[0] == "&":
            a = kc[1]
            kcr = self._id_to_key[kc[2]]
            kdl = self._id_to_key[kd[1]]
            kdr = self._id_to_key[kd[2]]
            if kcr[0] == "&" and kdl[0] == "|" and kdr[0] == "|":
                if kdl[1] == a and kdr[1] == a and kdl[2] == kcr[1] and kdr[2] == kcr[2]:
                    return "disjDistrib"
        # 12. a & (b v c) = (a & b) v (a & c)
        if kc[0] == "&" and kd[0] == "|":
            a = kc[1]
            kcr = self._id_to_key[kc[2]]
            kdl = self._id_to_key[kd[1]]
            kdr = self._id_to_key[kd[2]]
            if kcr[0] == "|" and kdl[0] == "&" and kdr[0] == "&":
                if kdl[1] == a and kdr[1] == a and kdl[2] == kcr[1] and kdr[2] == kcr[2]:
                    return "conjDistrib"
        return None

    def match_ba_root(self, c: int, d: int) -> Optional[Tuple[str, str]]:
        ax = self._match_ba_fwd(c, d)
        if ax is not None:
            return (ax, "fwd")
        ax = self._match_ba_fwd(d, c)
        if ax is not None:
            return (ax, "bwd")
        return None

    def are_approx(self, c: int, d: int) -> Tuple[bool, Optional[dict]]:
        """Exact O(|C|_DAG * |D|_DAG) decider for `C ≈ D` (Def 3.1 & Lemma 3.2).

        Returns `(True, witness)` where `witness = {"path": [...], "axiom": ..., "dir": ...}`
        if and only if `Fla[C] ~_BA Fla[D]` via a single-occurrence BA replacement.
        """
        pair = (c, d)
        if pair in self._approx_cache:
            w = self._approx_cache[pair]
            return (w is not None, w)

        root_match = self.match_ba_root(c, d)
        if root_match is not None:
            w = {"path": [], "axiom": root_match[0], "dir": root_match[1]}
            self._approx_cache[pair] = w
            return (True, w)

        kc = self._id_to_key[c]
        kd = self._id_to_key[d]
        if kc[0] == kd[0]:
            op = kc[0]
            if op == "!":
                ok, sub = self.are_approx(kc[1], kd[1])
                if ok and sub is not None:
                    w = {"path": [0] + sub["path"], "axiom": sub["axiom"], "dir": sub["dir"]}
                    self._approx_cache[pair] = w
                    return (True, w)
            elif op in ("|", "&"):
                if kc[2] == kd[2]:
                    ok, sub = self.are_approx(kc[1], kd[1])
                    if ok and sub is not None:
                        w = {"path": [0] + sub["path"], "axiom": sub["axiom"], "dir": sub["dir"]}
                        self._approx_cache[pair] = w
                        return (True, w)
                if kc[1] == kd[1]:
                    ok, sub = self.are_approx(kc[2], kd[2])
                    if ok and sub is not None:
                        w = {"path": [1] + sub["path"], "axiom": sub["axiom"], "dir": sub["dir"]}
                        self._approx_cache[pair] = w
                        return (True, w)

        self._approx_cache[pair] = None
        return (False, None)

    # ------------------------------------------------------------------
    # Exact single-occurrence neighbor generator for BFS in (Circuits, ≈)
    # ------------------------------------------------------------------

    def root_neighbors(self, c: int, compl_pool: Tuple[int, ...], allow_expand: bool = True) -> List[int]:
        """Generate all root `BAStep` neighbors of `c` (both directions)."""
        res: List[int] = []
        k = self._id_to_key[c]
        op = k[0]

        # 1 & 2: ~0 <-> 1, ~1 <-> 0
        if c == self.ONE:
            res.append(self.neg(self.ZERO))
            if allow_expand:
                for a in compl_pool:
                    res.append(self.disj(a, self.neg(a)))
        elif c == self.ZERO:
            res.append(self.neg(self.ONE))
            if allow_expand:
                for a in compl_pool:
                    res.append(self.conj(a, self.neg(a)))
        elif op == "!":
            if k[1] == self.ZERO:
                res.append(self.ONE)
            elif k[1] == self.ONE:
                res.append(self.ZERO)

        # 3 & 4 backward: a -> 0 v a, a -> 1 & a
        if allow_expand:
            res.append(self.disj(self.ZERO, c))
            res.append(self.conj(self.ONE, c))

        if op == "|":
            a, b = k[1], k[2]
            # 3 fwd: 0 v b -> b
            if a == self.ZERO:
                res.append(b)
            # 5 fwd: a v ~a -> 1
            if self._id_to_key[b] == ("!", a):
                res.append(self.ONE)
            # 7: a v b -> b v a
            if a != b:
                res.append(self.disj(b, a))
            # 9 fwd: a v (b1 v b2) -> (a v b1) v b2
            kb = self._id_to_key[b]
            if kb[0] == "|":
                res.append(self.disj(self.disj(a, kb[1]), kb[2]))
            # 9 bwd: (a1 v a2) v b -> a1 v (a2 v b)
            ka = self._id_to_key[a]
            if ka[0] == "|":
                res.append(self.disj(ka[1], self.disj(ka[2], b)))
            # 11 fwd: a v (b1 & b2) -> (a v b1) & (a v b2)
            if kb[0] == "&":
                res.append(self.conj(self.disj(a, kb[1]), self.disj(a, kb[2])))
            # 12 bwd: (x & y) v (x & z) -> x & (y v z)
            if ka[0] == "&" and kb[0] == "&" and ka[1] == kb[1]:
                res.append(self.conj(ka[1], self.disj(ka[2], kb[2])))

        elif op == "&":
            a, b = k[1], k[2]
            # 4 fwd: 1 & b -> b
            if a == self.ONE:
                res.append(b)
            # 6 fwd: a & ~a -> 0
            if self._id_to_key[b] == ("!", a):
                res.append(self.ZERO)
            # 8: a & b -> b & a
            if a != b:
                res.append(self.conj(b, a))
            # 10 fwd: a & (b1 & b2) -> (a & b1) & b2
            kb = self._id_to_key[b]
            if kb[0] == "&":
                res.append(self.conj(self.conj(a, kb[1]), kb[2]))
            # 10 bwd: (a1 & a2) & b -> a1 & (a2 & b)
            ka = self._id_to_key[a]
            if ka[0] == "&":
                res.append(self.conj(ka[1], self.conj(ka[2], b)))
            # 12 fwd: a & (b1 v b2) -> (a & b1) v (a & b2)
            if kb[0] == "|":
                res.append(self.disj(self.conj(a, kb[1]), self.conj(a, kb[2])))
            # 11 bwd: (x v y) & (x v z) -> x v (y & z)
            if ka[0] == "|" and kb[0] == "|" and ka[1] == kb[1]:
                res.append(self.disj(ka[1], self.conj(ka[2], kb[2])))

        return res

    def approx_neighbors(
        self,
        root: int,
        compl_pool: Tuple[int, ...],
        max_dag_size: int,
        allow_expand: bool = True,
    ) -> List[int]:
        """Generate exact single-occurrence `≈`-neighbors of `root` bounded by `max_dag_size`."""
        memo: Dict[int, List[int]] = {}

        def rec(u: int) -> List[int]:
            if u in memo:
                return memo[u]
            out: Set[int] = set(self.root_neighbors(u, compl_pool, allow_expand=allow_expand))
            k = self._id_to_key[u]
            op = k[0]
            if op == "!":
                for a2 in rec(k[1]):
                    out.add(self.neg(a2))
            elif op == "|":
                a, b = k[1], k[2]
                for a2 in rec(a):
                    out.add(self.disj(a2, b))
                for b2 in rec(b):
                    out.add(self.disj(a, b2))
            elif op == "&":
                a, b = k[1], k[2]
                for a2 in rec(a):
                    out.add(self.conj(a2, b))
                for b2 in rec(b):
                    out.add(self.conj(a, b2))
            lst = list(out)
            memo[u] = lst
            return lst

        raw = rec(root)
        return [v for v in raw if v != root and self.dag_size(v) <= max_dag_size]

    def bidirectional_bfs(
        self,
        src: int,
        dst: int,
        compl_pool: Tuple[int, ...],
        max_dag_size: int = 16,
        max_visited: int = 40000,
        allow_expand: bool = True,
    ) -> Optional[List[int]]:
        """Exact Bidirectional BFS in `(Circuits, ≈)` with DAG size cap."""
        if src == dst:
            return [src]

        parent_f: Dict[int, Optional[int]] = {src: None}
        parent_b: Dict[int, Optional[int]] = {dst: None}
        frontier_f: List[int] = [src]
        frontier_b: List[int] = [dst]

        def reconstruct(meet: int) -> List[int]:
            left: List[int] = []
            cur: Optional[int] = meet
            while cur is not None:
                left.append(cur)
                cur = parent_f[cur]
            left.reverse()
            right: List[int] = []
            cur = parent_b[meet]
            while cur is not None:
                right.append(cur)
                cur = parent_b[cur]
            return left + right

        while frontier_f and frontier_b and (len(parent_f) + len(parent_b) < max_visited):
            # Expand the smaller frontier to minimize branching
            if len(frontier_f) <= len(frontier_b):
                next_f: List[int] = []
                for u in frontier_f:
                    for v in self.approx_neighbors(u, compl_pool, max_dag_size, allow_expand):
                        if v not in parent_f:
                            parent_f[v] = u
                            if v in parent_b:
                                return reconstruct(v)
                            next_f.append(v)
                            if len(parent_f) + len(parent_b) >= max_visited:
                                break
                    if len(parent_f) + len(parent_b) >= max_visited:
                        break
                frontier_f = next_f
            else:
                next_b: List[int] = []
                for u in frontier_b:
                    for v in self.approx_neighbors(u, compl_pool, max_dag_size, allow_expand):
                        if v not in parent_b:
                            parent_b[v] = u
                            if v in parent_f:
                                return reconstruct(v)
                            next_b.append(v)
                            if len(parent_f) + len(parent_b) >= max_visited:
                                break
                    if len(parent_f) + len(parent_b) >= max_visited:
                        break
                frontier_b = next_b

        return None


# ======================================================================
# Constructive Verified BA Rewrite Compiler (every step checked by `≈`)
# ======================================================================


class BACompiler:
    """Builds 100%-verified `≈`-chains in `(Circuits, ≈)` from derived BA lemmas."""

    def __init__(self, store: DAGStore) -> None:
        self.s = store

    def concat(self, c1: List[int], c2: List[int]) -> List[int]:
        assert c1[-1] == c2[0], f"Chain mismatch: {self.s.pretty(c1[-1])} != {self.s.pretty(c2[0])}"
        return c1 + c2[1:]

    def rev(self, chain: List[int]) -> List[int]:
        return list(reversed(chain))

    def lift(self, ctx: Callable[[int], int], chain: List[int]) -> List[int]:
        return [ctx(u) for u in chain]

    # --- Basic derived BA chains ---

    def disj_zero_right(self, a: int) -> List[int]:
        """a | 0 ~* a (2 steps)."""
        s = self.s
        return [s.disj(a, s.ZERO), s.disj(s.ZERO, a), a]

    def conj_one_right(self, a: int) -> List[int]:
        """a & 1 ~* a (2 steps)."""
        s = self.s
        return [s.conj(a, s.ONE), s.conj(s.ONE, a), a]

    def disj_one_right(self, a: int) -> List[int]:
        """a | 1 ~* 1 (6 steps)."""
        s = self.s
        na = s.neg(a)
        return [
            s.disj(a, s.ONE),
            s.conj(s.ONE, s.disj(a, s.ONE)),
            s.conj(s.disj(a, na), s.disj(a, s.ONE)),
            s.disj(a, s.conj(na, s.ONE)),
            s.disj(a, s.conj(s.ONE, na)),
            s.disj(a, na),
            s.ONE,
        ]

    def disj_one_left(self, a: int) -> List[int]:
        """1 | a ~* 1 (7 steps)."""
        s = self.s
        return self.concat([s.disj(s.ONE, a), s.disj(a, s.ONE)], self.disj_one_right(a))

    def conj_zero_right(self, a: int) -> List[int]:
        """a & 0 ~* 0 (6 steps)."""
        s = self.s
        na = s.neg(a)
        return [
            s.conj(a, s.ZERO),
            s.disj(s.ZERO, s.conj(a, s.ZERO)),
            s.disj(s.conj(a, na), s.conj(a, s.ZERO)),
            s.conj(a, s.disj(na, s.ZERO)),
            s.conj(a, s.disj(s.ZERO, na)),
            s.conj(a, na),
            s.ZERO,
        ]

    def conj_zero_left(self, a: int) -> List[int]:
        """0 & a ~* 0 (7 steps)."""
        s = self.s
        return self.concat([s.conj(s.ZERO, a), s.conj(a, s.ZERO)], self.conj_zero_right(a))

    def disj_idem(self, a: int) -> List[int]:
        """a | a ~* a (7 steps)."""
        s = self.s
        na = s.neg(a)
        return [
            s.disj(a, a),
            s.conj(s.ONE, s.disj(a, a)),
            s.conj(s.disj(a, na), s.disj(a, a)),
            s.disj(a, s.conj(na, a)),
            s.disj(a, s.conj(a, na)),
            s.disj(a, s.ZERO),
            s.disj(s.ZERO, a),
            a,
        ]

    def conj_idem(self, a: int) -> List[int]:
        """a & a ~* a (7 steps)."""
        s = self.s
        na = s.neg(a)
        return [
            s.conj(a, a),
            s.disj(s.ZERO, s.conj(a, a)),
            s.disj(s.conj(a, na), s.conj(a, a)),
            s.conj(a, s.disj(na, a)),
            s.conj(a, s.disj(a, na)),
            s.conj(a, s.ONE),
            s.conj(s.ONE, a),
            a,
        ]

    def compl_unique(
        self, a: int, b: int, ch_or_1: List[int], ch_and_0: List[int]
    ) -> List[int]:
        """From `a | b ~* 1` and `a & b ~* 0`, derive `b ~* ~a`."""
        s = self.s
        na = s.neg(a)
        # b ~* b & ~a
        c1 = [
            b,
            s.conj(s.ONE, b),
            s.conj(s.disj(a, na), b),
            s.conj(b, s.disj(a, na)),
            s.disj(s.conj(b, a), s.conj(b, na)),
            s.disj(s.conj(a, b), s.conj(b, na)),
        ]
        c1 = self.concat(c1, self.lift(lambda u: s.disj(u, s.conj(b, na)), ch_and_0))
        c1 = self.concat(c1, [s.disj(s.ZERO, s.conj(b, na)), s.conj(b, na)])

        # ~a ~* b & ~a
        c2 = [na, s.conj(s.ONE, na)]
        c2 = self.concat(c2, self.lift(lambda u: s.conj(u, na), self.rev(ch_or_1)))
        c2 = self.concat(
            c2,
            [
                s.conj(s.disj(a, b), na),
                s.conj(na, s.disj(a, b)),
                s.disj(s.conj(na, a), s.conj(na, b)),
                s.disj(s.conj(a, na), s.conj(na, b)),
                s.disj(s.ZERO, s.conj(na, b)),
                s.conj(na, b),
                s.conj(b, na),
            ],
        )
        return self.concat(c1, self.rev(c2))

    def double_neg(self, a: int) -> List[int]:
        """~~a ~* a."""
        s = self.s
        na = s.neg(a)
        ch_or_1 = [s.disj(na, a), s.disj(a, na), s.ONE]
        ch_and_0 = [s.conj(na, a), s.conj(a, na), s.ZERO]
        a_to_nna = self.compl_unique(na, a, ch_or_1, ch_and_0)
        return self.rev(a_to_nna)

    def demorgan_disj(self, a: int, b: int) -> List[int]:
        """~(a | b) ~* (~a & ~b)."""
        s = self.s
        na, nb = s.neg(a), s.neg(b)
        ab = s.disj(a, b)
        nanb = s.conj(na, nb)
        # (a | b) | (~a & ~b) ~* 1
        ch_or = [ab, s.disj(ab, nanb)][1:]  # start at ab | nanb
        ch_or = [
            s.disj(ab, nanb),
            s.conj(s.disj(ab, na), s.disj(ab, nb)),
            # left: (a | b) | ~a -> (b | a) | ~a -> b | (a | ~a) -> b | 1 ~* 1
            s.conj(s.disj(s.disj(b, a), na), s.disj(ab, nb)),
            s.conj(s.disj(b, s.disj(a, na)), s.disj(ab, nb)),
            s.conj(s.disj(b, s.ONE), s.disj(ab, nb)),
        ]
        ch_or = self.concat(
            ch_or, self.lift(lambda u: s.conj(u, s.disj(ab, nb)), self.disj_one_right(b))
        )
        ch_or = self.concat(
            ch_or,
            [
                s.conj(s.ONE, s.disj(ab, nb)),
                s.disj(ab, nb),
                s.disj(a, s.disj(b, nb)),
                s.disj(a, s.ONE),
            ],
        )
        ch_or = self.concat(ch_or, self.disj_one_right(a))

        # (a | b) & (~a & ~b) ~* 0
        ch_and = [
            s.conj(ab, nanb),
            s.conj(nanb, ab),
            s.disj(s.conj(nanb, a), s.conj(nanb, b)),
            # left: (~a & ~b) & a -> (~b & ~a) & a -> ~b & (~a & a) -> ~b & (a & ~a) -> ~b & 0 ~* 0
            s.disj(s.conj(s.conj(nb, na), a), s.conj(nanb, b)),
            s.disj(s.conj(nb, s.conj(na, a)), s.conj(nanb, b)),
            s.disj(s.conj(nb, s.conj(a, na)), s.conj(nanb, b)),
            s.disj(s.conj(nb, s.ZERO), s.conj(nanb, b)),
        ]
        ch_and = self.concat(
            ch_and, self.lift(lambda u: s.disj(u, s.conj(nanb, b)), self.conj_zero_right(nb))
        )
        ch_and = self.concat(
            ch_and,
            [
                s.disj(s.ZERO, s.conj(nanb, b)),
                s.conj(nanb, b),
                s.conj(na, s.conj(nb, b)),
                s.conj(na, s.conj(b, nb)),
                s.conj(na, s.ZERO),
            ],
        )
        ch_and = self.concat(ch_and, self.conj_zero_right(na))

        nanb_to_neg = self.compl_unique(ab, nanb, ch_or, ch_and)
        return self.rev(nanb_to_neg)

    def demorgan_conj(self, a: int, b: int) -> List[int]:
        """~(a & b) ~* (~a | ~b)."""
        s = self.s
        na, nb = s.neg(a), s.neg(b)
        ab = s.conj(a, b)
        nanb = s.disj(na, nb)
        # (a & b) | (~a | ~b) ~* 1
        ch_or = [
            s.disj(ab, nanb),
            s.disj(nanb, ab),
            s.conj(s.disj(nanb, a), s.disj(nanb, b)),
            s.conj(s.disj(s.disj(nb, na), a), s.disj(nanb, b)),
            s.conj(s.disj(nb, s.disj(na, a)), s.disj(nanb, b)),
            s.conj(s.disj(nb, s.disj(a, na)), s.disj(nanb, b)),
            s.conj(s.disj(nb, s.ONE), s.disj(nanb, b)),
        ]
        ch_or = self.concat(
            ch_or, self.lift(lambda u: s.conj(u, s.disj(nanb, b)), self.disj_one_right(nb))
        )
        ch_or = self.concat(
            ch_or,
            [
                s.conj(s.ONE, s.disj(nanb, b)),
                s.disj(nanb, b),
                s.disj(na, s.disj(nb, b)),
                s.disj(na, s.disj(b, nb)),
                s.disj(na, s.ONE),
            ],
        )
        ch_or = self.concat(ch_or, self.disj_one_right(na))

        # (a & b) & (~a | ~b) ~* 0
        ch_and = [
            s.conj(ab, nanb),
            s.disj(s.conj(ab, na), s.conj(ab, nb)),
            s.disj(s.conj(s.conj(b, a), na), s.conj(ab, nb)),
            s.disj(s.conj(b, s.conj(a, na)), s.conj(ab, nb)),
            s.disj(s.conj(b, s.ZERO), s.conj(ab, nb)),
        ]
        ch_and = self.concat(
            ch_and, self.lift(lambda u: s.disj(u, s.conj(ab, nb)), self.conj_zero_right(b))
        )
        ch_and = self.concat(
            ch_and,
            [
                s.disj(s.ZERO, s.conj(ab, nb)),
                s.conj(ab, nb),
                s.conj(a, s.conj(b, nb)),
                s.conj(a, s.ZERO),
            ],
        )
        ch_and = self.concat(ch_and, self.conj_zero_right(a))

        nanb_to_neg = self.compl_unique(ab, nanb, ch_or, ch_and)
        return self.rev(nanb_to_neg)

    def modus_ponens(self, a: int, b: int, ch_a: List[int], ch_imp: List[int]) -> List[int]:
        """Krajicek Lemma 2.1 (lines 359-371): from `a ~* 1` and `(~a | b) ~* 1`, derive `b ~* 1`."""
        s = self.s
        # ~a ~* ~1 -> 0
        c1 = self.lift(s.neg, ch_a)
        c1 = self.concat(c1, [s.neg(s.ONE), s.ZERO])
        # (~a | b) ~* (0 | b) -> b
        c2 = self.lift(lambda u: s.disj(u, b), c1)
        c2 = self.concat(c2, [s.disj(s.ZERO, b), b])
        # b ~* (~a | b) ~* 1
        return self.concat(self.rev(c2), ch_imp)

    # --- NNF + Constant Simplification + Shannon Expansion ---

    def to_nnf(self, u: int) -> List[int]:
        """Push all negations to leaves and simplify constants."""
        s = self.s
        k = s.key(u)
        op = k[0]
        if op in ("0", "1", "v"):
            return [u]
        if op == "!":
            sub = k[1]
            ks = s.key(sub)
            if ks[0] == "0":
                return [u, s.ONE]
            if ks[0] == "1":
                return [u, s.ZERO]
            if ks[0] == "v":
                return [u]
            if ks[0] == "!":
                c1 = self.double_neg(ks[1])
                c2 = self.to_nnf(ks[1])
                return self.concat(c1, c2)
            if ks[0] == "|":
                c1 = self.demorgan_disj(ks[1], ks[2])
                c2 = self.to_nnf(c1[-1])
                return self.concat(c1, c2)
            if ks[0] == "&":
                c1 = self.demorgan_conj(ks[1], ks[2])
                c2 = self.to_nnf(c1[-1])
                return self.concat(c1, c2)
        if op == "|":
            c1 = self.to_nnf(k[1])
            ch = self.lift(lambda x: s.disj(x, k[2]), c1)
            a = c1[-1]
            c2 = self.to_nnf(k[2])
            ch = self.concat(ch, self.lift(lambda y: s.disj(a, y), c2))
            b = c2[-1]
            return self.concat(ch, self.simplify_disj(a, b))
        if op == "&":
            c1 = self.to_nnf(k[1])
            ch = self.lift(lambda x: s.conj(x, k[2]), c1)
            a = c1[-1]
            c2 = self.to_nnf(k[2])
            ch = self.concat(ch, self.lift(lambda y: s.conj(a, y), c2))
            b = c2[-1]
            return self.concat(ch, self.simplify_conj(a, b))
        return [u]

    def simplify_disj(self, a: int, b: int) -> List[int]:
        s = self.s
        cur = s.disj(a, b)
        if a == s.ZERO:
            return [cur, b]
        if b == s.ZERO:
            return self.disj_zero_right(a)
        if a == s.ONE:
            return self.disj_one_left(b)
        if b == s.ONE:
            return self.disj_one_right(a)
        if a == b:
            return self.disj_idem(a)
        if s.key(b) == ("!", a):
            return [cur, s.ONE]
        if s.key(a) == ("!", b):
            return [cur, s.disj(b, a), s.ONE]
        return [cur]

    def simplify_conj(self, a: int, b: int) -> List[int]:
        s = self.s
        cur = s.conj(a, b)
        if a == s.ONE:
            return [cur, b]
        if b == s.ONE:
            return self.conj_one_right(a)
        if a == s.ZERO:
            return self.conj_zero_left(b)
        if b == s.ZERO:
            return self.conj_zero_right(a)
        if a == b:
            return self.conj_idem(a)
        if s.key(b) == ("!", a):
            return [cur, s.ZERO]
        if s.key(a) == ("!", b):
            return [cur, s.conj(b, a), s.ZERO]
        return [cur]

    def subst_nnf_under_lit(self, u: int, v_id: int, val: bool) -> Tuple[List[int], int]:
        """Given NNF formula `u` and literal `lit = v_id` (if val) or `~v_id` (if not val),
        construct a verified `≈`-chain `(u & lit) ~* (u' & lit)` where `u'` has `v_id` substituted
        by `1` (if val) or `0` (if not val) and simplified."""
        s = self.s
        lit = v_id if val else s.neg(v_id)
        k = s.key(u)
        op = k[0]
        if op in ("0", "1"):
            return ([s.conj(u, lit)], u)
        if op == "v":
            if u == v_id:
                if val:
                    # x & x ~* x <- 1 & x
                    ch = self.concat(self.conj_idem(lit), [lit, s.conj(s.ONE, lit)])
                    return (ch, s.ONE)
                else:
                    # x & ~x -> 0 <- 0 & ~x
                    ch = [s.conj(u, lit), s.ZERO]
                    ch = self.concat(ch, self.rev(self.conj_zero_left(lit)))
                    return (ch, s.ZERO)
            return ([s.conj(u, lit)], u)
        if op == "!":
            # In NNF, child is a variable
            if k[1] == v_id:
                if val:
                    # ~x & x -> x & ~x -> 0 <- 0 & x
                    ch = [s.conj(u, lit), s.conj(lit, u), s.ZERO]
                    ch = self.concat(ch, self.rev(self.conj_zero_left(lit)))
                    return (ch, s.ZERO)
                else:
                    # ~x & ~x ~* ~x <- 1 & ~x
                    ch = self.concat(self.conj_idem(lit), [lit, s.conj(s.ONE, lit)])
                    return (ch, s.ONE)
            return ([s.conj(u, lit)], u)
        if op == "|":
            a, b = k[1], k[2]
            ch = [
                s.conj(u, lit),
                s.conj(lit, u),
                s.disj(s.conj(lit, a), s.conj(lit, b)),
                s.disj(s.conj(a, lit), s.conj(lit, b)),
                s.disj(s.conj(a, lit), s.conj(b, lit)),
            ]
            ch_a, a2 = self.subst_nnf_under_lit(a, v_id, val)
            ch = self.concat(ch, self.lift(lambda x: s.disj(x, s.conj(b, lit)), ch_a))
            ch_b, b2 = self.subst_nnf_under_lit(b, v_id, val)
            ch = self.concat(ch, self.lift(lambda y: s.disj(s.conj(a2, lit), y), ch_b))
            ch = self.concat(
                ch,
                [
                    s.disj(s.conj(a2, lit), s.conj(b2, lit)),
                    s.disj(s.conj(lit, a2), s.conj(b2, lit)),
                    s.disj(s.conj(lit, a2), s.conj(lit, b2)),
                    s.conj(lit, s.disj(a2, b2)),
                    s.conj(s.disj(a2, b2), lit),
                ],
            )
            simp = self.simplify_disj(a2, b2)
            ch = self.concat(ch, self.lift(lambda z: s.conj(z, lit), simp))
            return (ch, simp[-1])
        if op == "&":
            a, b = k[1], k[2]
            # (a & b) & lit -> a & (b & lit) ~* a & (b2 & lit) -> (a & b2) & lit
            ch = [s.conj(u, lit), s.conj(a, s.conj(b, lit))]
            ch_b, b2 = self.subst_nnf_under_lit(b, v_id, val)
            ch = self.concat(ch, self.lift(lambda y: s.conj(a, y), ch_b))
            ch = self.concat(
                ch,
                [
                    s.conj(a, s.conj(b2, lit)),
                    s.conj(s.conj(a, b2), lit),
                    s.conj(s.conj(b2, a), lit),
                    s.conj(b2, s.conj(a, lit)),
                ],
            )
            ch_a, a2 = self.subst_nnf_under_lit(a, v_id, val)
            ch = self.concat(ch, self.lift(lambda x: s.conj(b2, x), ch_a))
            ch = self.concat(
                ch,
                [
                    s.conj(b2, s.conj(a2, lit)),
                    s.conj(s.conj(b2, a2), lit),
                    s.conj(s.conj(a2, b2), lit),
                ],
            )
            simp = self.simplify_conj(a2, b2)
            ch = self.concat(ch, self.lift(lambda z: s.conj(z, lit), simp))
            return (ch, simp[-1])
        raise ValueError(f"Unexpected op {op}")

    def prove_tautology_shannon(self, root: int, var_order: List[str]) -> List[int]:
        """Prove any tautology `root ~* 1` via NNF + pruned Shannon expansion in BA."""
        s = self.s
        ch_nnf = self.to_nnf(root)

        def rec(u: int, rem_vars: List[str]) -> List[int]:
            if u == s.ONE:
                return [s.ONE]
            if not rem_vars:
                raise ValueError(f"Formula not a tautology! Reduced to {s.pretty(u)}")
            v_name = rem_vars[0]
            rest = rem_vars[1:]
            # Skip variable if not present in u
            if v_name not in s.variables(u):
                return rec(u, rest)
            v_id = s.var(v_name)
            nv_id = s.neg(v_id)
            # u <- 1 & u <- (v | ~v) & u -> u & (v | ~v) -> (u & v) | (u & ~v)
            ch = [
                u,
                s.conj(s.ONE, u),
                s.conj(s.disj(v_id, nv_id), u),
                s.conj(u, s.disj(v_id, nv_id)),
                s.disj(s.conj(u, v_id), s.conj(u, nv_id)),
            ]
            ch_t, u_t = self.subst_nnf_under_lit(u, v_id, True)
            ch = self.concat(ch, self.lift(lambda x: s.disj(x, s.conj(u, nv_id)), ch_t))
            ch_t_one = rec(u_t, rest)
            ch = self.concat(
                ch, self.lift(lambda x: s.disj(s.conj(x, v_id), s.conj(u, nv_id)), ch_t_one)
            )
            ch_f, u_f = self.subst_nnf_under_lit(u, v_id, False)
            ch = self.concat(ch, self.lift(lambda y: s.disj(s.conj(s.ONE, v_id), y), ch_f))
            ch_f_one = rec(u_f, rest)
            ch = self.concat(
                ch, self.lift(lambda y: s.disj(s.conj(s.ONE, v_id), s.conj(y, nv_id)), ch_f_one)
            )
            # (1 & v) | (1 & ~v) -> v | (1 & ~v) -> v | ~v -> 1
            ch = self.concat(
                ch,
                [
                    s.disj(s.conj(s.ONE, v_id), s.conj(s.ONE, nv_id)),
                    s.disj(v_id, s.conj(s.ONE, nv_id)),
                    s.disj(v_id, nv_id),
                    s.ONE,
                ],
            )
            return ch

        return self.concat(ch_nnf, rec(ch_nnf[-1], var_order))

    def to_canonical_shannon(self, root: int, var_order: List[str]) -> List[int]:
        """Rewrite any formula `root` to its canonical Shannon decision tree over `var_order`."""
        s = self.s
        ch_nnf = self.to_nnf(root)

        def rec(u: int, rem_vars: List[str]) -> List[int]:
            if u in (s.ZERO, s.ONE) or not rem_vars:
                return [u]
            v_name = rem_vars[0]
            rest = rem_vars[1:]
            v_id = s.var(v_name)
            nv_id = s.neg(v_id)
            ch = [
                u,
                s.conj(s.ONE, u),
                s.conj(s.disj(v_id, nv_id), u),
                s.conj(u, s.disj(v_id, nv_id)),
                s.disj(s.conj(u, v_id), s.conj(u, nv_id)),
            ]
            ch_t, u_t = self.subst_nnf_under_lit(u, v_id, True)
            ch = self.concat(ch, self.lift(lambda x: s.disj(x, s.conj(u, nv_id)), ch_t))
            ch_t_can = rec(u_t, rest)
            t_can = ch_t_can[-1]
            ch = self.concat(
                ch, self.lift(lambda x: s.disj(s.conj(x, v_id), s.conj(u, nv_id)), ch_t_can)
            )
            ch_f, u_f = self.subst_nnf_under_lit(u, v_id, False)
            ch = self.concat(ch, self.lift(lambda y: s.disj(s.conj(t_can, v_id), y), ch_f))
            ch_f_can = rec(u_f, rest)
            f_can = ch_f_can[-1]
            ch = self.concat(
                ch, self.lift(lambda y: s.disj(s.conj(t_can, v_id), s.conj(y, nv_id)), ch_f_can)
            )
            # If both branches equal the same constant/term, collapse: (c & v) | (c & ~v) -> c
            if t_can == f_can:
                ch = self.concat(
                    ch,
                    [
                        s.disj(s.conj(t_can, v_id), s.conj(t_can, nv_id)),
                        s.conj(t_can, s.disj(v_id, nv_id)),
                        s.conj(t_can, s.ONE),
                        s.conj(s.ONE, t_can),
                        t_can,
                    ],
                )
            return ch

        return self.concat(ch_nnf, rec(ch_nnf[-1], var_order))

    def prove_equiv_shannon(self, c: int, d: int, var_order: List[str]) -> List[int]:
        """Prove `c ~* d` via canonical Shannon trees."""
        c_can = self.to_canonical_shannon(c, var_order)
        d_can = self.to_canonical_shannon(d, var_order)
        assert c_can[-1] == d_can[-1], "Canonical Shannon trees differ (formulas not equivalent!)"
        return self.concat(c_can, self.rev(d_can))

    def shortcut_chain(self, chain: List[int]) -> List[int]:
        """Remove cycles and apply exact greedy `≈`-shortcutting (preserving 100% validity)."""
        # First remove repeated states (cycles)
        no_cycles: List[int] = []
        pos: Dict[int, int] = {}
        for u in chain:
            if u in pos:
                cut = pos[u]
                for rem in no_cycles[cut + 1 :]:
                    pos.pop(rem, None)
                no_cycles = no_cycles[: cut + 1]
            else:
                pos[u] = len(no_cycles)
                no_cycles.append(u)

        # Greedy forward `are_approx` shortcutting
        out = [no_cycles[0]]
        i = 0
        n = len(no_cycles)
        while i < n - 1:
            best_j = i + 1
            # Scan backwards within a window to find furthest direct `≈` jump
            hi = min(n - 1, i + 40)
            for j in range(hi, i + 1, -1):
                ok, _ = self.s.are_approx(no_cycles[i], no_cycles[j])
                if ok:
                    best_j = j
                    break
            out.append(no_cycles[best_j])
            i = best_j
        return out


# ======================================================================
# Verification, Metrics & Benchmark Suite
# ======================================================================


def verify_and_profile_chain(
    store: DAGStore,
    name: str,
    family: str,
    chain: List[int],
    search_mode: str,
    var_names: List[str],
    elapsed_ms: float,
    include_full_chain: bool = True,
) -> dict:
    """Independently verify every step via `are_approx` + truth table, and record functionals."""
    assert len(chain) >= 1
    tt0 = store.truth_table(chain[0], var_names)
    step_witnesses = []
    for idx in range(len(chain) - 1):
        u, v = chain[idx], chain[idx + 1]
        ok, w = store.are_approx(u, v)
        if not ok or w is None:
            raise AssertionError(
                f"[{name}] INVALID ≈ step at {idx}: {store.pretty(u)} !≈ {store.pretty(v)}"
            )
        if store.truth_table(v, var_names) != tt0:
            raise AssertionError(f"[{name}] SEMANTIC MISMATCH at step {idx + 1}")
        step_witnesses.append(
            {
                "step": idx,
                "axiom": w["axiom"],
                "dir": w["dir"],
                "path": w["path"],
                "dag_size_before": store.dag_size(u),
                "dag_size_after": store.dag_size(v),
            }
        )

    dag_sizes = [store.dag_size(u) for u in chain]
    formula_sizes = [store.formula_size(u) for u in chain]
    and_depths = [store.and_depth(u) for u in chain]
    fanouts = [store.fanout_stats(u) for u in chain]
    max_gate_fanouts = [f["max_gate_fanout"] for f in fanouts]
    max_gate_occs = [f["max_gate_tree_occ"] for f in fanouts]

    root_fourier = (
        store.fourier_sensitivity_from_tt(tt0, len(var_names))
        if len(var_names) <= 10
        else {}
    )
    # Sample subcircuit energy at start, peak DAG size, and end
    peak_idx = dag_sizes.index(max(dag_sizes))
    energy_start = store.subcircuit_energy_profile(chain[0], var_names)
    energy_peak = store.subcircuit_energy_profile(chain[peak_idx], var_names)
    energy_end = store.subcircuit_energy_profile(chain[-1], var_names)

    # Axiom histogram
    ax_hist: Dict[str, int] = {}
    for sw in step_witnesses:
        key = f"{sw['axiom']}:{sw['dir']}"
        ax_hist[key] = ax_hist.get(key, 0) + 1

    rec = {
        "name": name,
        "family": family,
        "search_mode": search_mode,
        "verified_all_approx_steps": True,
        "verified_semantic_invariance": True,
        "num_vars": len(var_names),
        "vars": var_names,
        "src_expr": store.pretty(chain[0], 220),
        "dst_expr": store.pretty(chain[-1], 220),
        "distance_steps": len(chain) - 1,
        "src_dag_size": dag_sizes[0],
        "dst_dag_size": dag_sizes[-1],
        "peak_dag_size": max(dag_sizes),
        "peak_dag_step": peak_idx,
        "dag_blowup_ratio": round(max(dag_sizes) / max(1, max(dag_sizes[0], dag_sizes[-1])), 3),
        "total_chain_dag_size": sum(dag_sizes),
        "src_formula_size": formula_sizes[0],
        "dst_formula_size": formula_sizes[-1],
        "peak_formula_size": max(formula_sizes),
        "src_and_depth": and_depths[0],
        "dst_and_depth": and_depths[-1],
        "peak_and_depth": max(and_depths),
        "src_max_gate_fanout": max_gate_fanouts[0],
        "peak_max_gate_fanout": max(max_gate_fanouts),
        "peak_max_gate_tree_occ": max(max_gate_occs),
        "root_fourier_sensitivity": root_fourier,
        "subcircuit_energy_start": energy_start,
        "subcircuit_energy_peak": energy_peak,
        "subcircuit_energy_end": energy_end,
        "axiom_usage": ax_hist,
        "elapsed_ms": round(elapsed_ms, 2),
    }
    if include_full_chain and len(chain) <= 60:
        rec["chain_exprs"] = [store.pretty(u, 180) for u in chain]
        rec["step_witnesses"] = step_witnesses
    else:
        rec["chain_exprs_sample"] = {
            "first_5": [store.pretty(u, 160) for u in chain[:5]],
            "peak": store.pretty(chain[peak_idx], 160),
            "last_5": [store.pretty(u, 160) for u in chain[-5:]],
        }
    return rec


def run_v2_self_tests(store: DAGStore) -> dict:
    """Verify the Datta & Dutta v2 single-occurrence fan-out unsharing semantics."""
    x = store.var("x")
    g = store.disj(x, store.neg(x))  # x v ~x
    shared = store.conj(g, g)  # (x v ~x) & (x v ~x)  (g has fanout 2!)
    unshared_one = store.conj(store.ONE, g)  # 1 & (x v ~x)
    both_replaced = store.conj(store.ONE, store.ONE)  # 1 & 1

    ok_single, w_single = store.are_approx(shared, unshared_one)
    ok_both, _ = store.are_approx(shared, both_replaced)

    assert ok_single is True, "Single-occurrence rewrite inside fanout-2 gate MUST be ≈!"
    assert ok_both is False, "Simultaneous multi-occurrence rewrite MUST NOT be ≈ (v2 fix)!"
    assert w_single == {"path": [0], "axiom": "disjCompl", "dir": "fwd"}

    # Check DAG size jump on unsharing: shared has {x, ~x, g, shared} = 4 nodes;
    # unshared_one has {1, x, ~x, g, unshared_one} = 5 nodes (+1 unsharing cost).
    return {
        "fanout2_single_occurrence_approx": ok_single,
        "fanout2_simultaneous_both_approx": ok_both,
        "single_occurrence_witness": w_single,
        "shared_dag_size": store.dag_size(shared),
        "unshared_one_dag_size": store.dag_size(unshared_one),
        "status": "PASS",
    }


def main() -> None:
    store = DAGStore()
    comp = BACompiler(store)

    v2_tests = run_v2_self_tests(store)
    results: List[dict] = []

    x1 = store.var("x1")
    x2 = store.var("x2")
    x3 = store.var("x3")

    # ==================================================================
    # (a) Tautology families, DeMorgan, Modus Ponens, 2-bit & 3-bit XOR
    # ==================================================================

    # a1. Law of excluded middle: x1 v ~x1 -> 1 (exact BFS)
    t0 = time.perf_counter()
    lem = store.disj(x1, store.neg(x1))
    ch = store.bidirectional_bfs(lem, store.ONE, (x1,), max_dag_size=10)
    assert ch is not None
    results.append(
        verify_and_profile_chain(
            store, "taut_lem_x_or_not_x", "tautology", ch, "exact_bidirectional_bfs", ["x1"], (time.perf_counter() - t0) * 1000
        )
    )

    # a2. Fan-out 2 tautology: (x1 v ~x1) & (x1 v ~x1) -> 1 (exact BFS, demonstrates unsharing!)
    t0 = time.perf_counter()
    lem2 = store.conj(lem, lem)
    ch = store.bidirectional_bfs(lem2, store.ONE, (x1,), max_dag_size=10)
    assert ch is not None
    results.append(
        verify_and_profile_chain(
            store, "taut_fanout2_lem_and_lem", "tautology_unsharing", ch, "exact_bidirectional_bfs", ["x1"], (time.perf_counter() - t0) * 1000
        )
    )

    # a3. Double negation: ~~x1 -> x1 (exact BFS vs constructive)
    t0 = time.perf_counter()
    dn = store.neg(store.neg(x1))
    ch_dn = store.bidirectional_bfs(
        dn, x1, (x1, store.neg(x1)), max_dag_size=12, max_visited=80000
    )
    if ch_dn is not None:
        mode = "exact_bidirectional_bfs"
    else:
        ch_dn = comp.shortcut_chain(comp.double_neg(x1))
        mode = "constructive_verified_chain"
    results.append(
        verify_and_profile_chain(
            store, "double_negation_elim", "tautology", ch_dn, mode, ["x1"], (time.perf_counter() - t0) * 1000
        )
    )

    # a4. DeMorgan Disj: ~(x1 v x2) -> (~x1 & ~x2)
    t0 = time.perf_counter()
    dm_d_src = store.neg(store.disj(x1, x2))
    dm_d_dst = store.conj(store.neg(x1), store.neg(x2))
    ch_dmd = comp.shortcut_chain(comp.demorgan_disj(x1, x2))
    results.append(
        verify_and_profile_chain(
            store, "demorgan_disj", "demorgan", ch_dmd, "constructive_verified_chain", ["x1", "x2"], (time.perf_counter() - t0) * 1000
        )
    )

    # a5. DeMorgan Conj: ~(x1 & x2) -> (~x1 v ~x2)
    t0 = time.perf_counter()
    ch_dmc = comp.shortcut_chain(comp.demorgan_conj(x1, x2))
    results.append(
        verify_and_profile_chain(
            store, "demorgan_conj", "demorgan", ch_dmc, "constructive_verified_chain", ["x1", "x2"], (time.perf_counter() - t0) * 1000
        )
    )

    # a6. Modus Ponens chain (Krajicek Lemma 2.1):
    #     Given a = (x1 v ~x1) ~* 1 and (~a v b) = (~(x1 v ~x1) v (x2 v ~x2)) ~* 1,
    #     derive b = (x2 v ~x2) ~* 1 via explicit Lemma 2.1 construction (+2 overhead).
    t0 = time.perf_counter()
    a_mp = store.disj(x1, store.neg(x1))
    b_mp = store.disj(x2, store.neg(x2))
    ch_a = [a_mp, store.ONE]
    # (~a v b) -> (~a v 1) ~* 1
    ch_imp = comp.concat(
        [store.disj(store.neg(a_mp), b_mp), store.disj(store.neg(a_mp), store.ONE)],
        comp.disj_one_right(store.neg(a_mp)),
    )
    ch_mp_raw = comp.modus_ponens(a_mp, b_mp, ch_a, ch_imp)
    results.append(
        verify_and_profile_chain(
            store, "modus_ponens_lemma21_raw", "modus_ponens", ch_mp_raw, "lemma21_exact_simulation", ["x1", "x2"], (time.perf_counter() - t0) * 1000
        )
    )

    # a7. 2-bit XOR commutativity: (x1 ^ x2) <-> (x2 ^ x1) (exact BFS!)
    t0 = time.perf_counter()
    xor12 = store.xor(x1, x2)
    xor21 = store.xor(x2, x1)
    ch_x2 = store.bidirectional_bfs(
        xor12, xor21, (x1, x2), max_dag_size=12, max_visited=30000, allow_expand=False
    )
    assert ch_x2 is not None
    results.append(
        verify_and_profile_chain(
            store, "xor2_commutativity", "xor", ch_x2, "exact_bidirectional_bfs", ["x1", "x2"], (time.perf_counter() - t0) * 1000
        )
    )

    # a8. 3-bit XOR associativity: ((x1 ^ x2) ^ x3) <-> (x1 ^ (x2 ^ x3))
    #     Note: a ^ b := (a & ~b) v (~a & b) has fanout 2 per level!
    t0 = time.perf_counter()
    xor_lhs = store.xor(store.xor(x1, x2), x3)
    xor_rhs = store.xor(x1, store.xor(x2, x3))
    ch_x3 = comp.shortcut_chain(comp.prove_equiv_shannon(xor_lhs, xor_rhs, ["x1", "x2", "x3"]))
    results.append(
        verify_and_profile_chain(
            store, "xor3_associativity", "xor", ch_x3, "constructive_verified_chain", ["x1", "x2", "x3"], (time.perf_counter() - t0) * 1000, include_full_chain=False
        )
    )

    # ==================================================================
    # (b) MAJ_3 equivalent DeMorgan circuits:
    #     DNF: (x1 & x2) v (x1 & x3) v (x2 & x3)
    #     CNF: (x1 v x2) & (x1 v x3) & (x2 v x3)
    # ==================================================================
    t0 = time.perf_counter()
    maj3_dnf = store.disj_many([store.conj(x1, x2), store.conj(x1, x3), store.conj(x2, x3)])
    maj3_cnf = store.conj_many([store.disj(x1, x2), store.disj(x1, x3), store.disj(x2, x3)])
    # Try exact BFS without complement expansion first (distributivity + comm + assoc)
    ch_maj3 = store.bidirectional_bfs(
        maj3_dnf, maj3_cnf, (x1, x2, x3), max_dag_size=18, max_visited=60000, allow_expand=False
    )
    if ch_maj3 is not None:
        mode_maj3 = "exact_bidirectional_bfs"
    else:
        ch_maj3 = comp.shortcut_chain(comp.prove_equiv_shannon(maj3_dnf, maj3_cnf, ["x1", "x2", "x3"]))
        mode_maj3 = "constructive_verified_chain"
    results.append(
        verify_and_profile_chain(
            store, "maj3_dnf_to_cnf", "maj3", ch_maj3, mode_maj3, ["x1", "x2", "x3"], (time.perf_counter() - t0) * 1000, include_full_chain=(len(ch_maj3) <= 60)
        )
    )

    # ==================================================================
    # (c) Miniature PHP_2^1 and PHP_3^2 tautologies (~PHP -> 1)
    #     (Krajicek rewrite.tex Remark p. 11 line 642)
    # ==================================================================

    # c1. ~PHP_2^1 in DNF tautology form: (~p11 v ~p21) v (p11 & p21) -> 1
    t0 = time.perf_counter()
    p11, p21 = store.var("p11"), store.var("p21")
    not_php21_dnf = store.disj(store.disj(store.neg(p11), store.neg(p21)), store.conj(p11, p21))
    ch_php21 = store.bidirectional_bfs(
        not_php21_dnf, store.ONE, (p11, p21), max_dag_size=14, max_visited=60000
    )
    if ch_php21 is not None:
        mode_p21 = "exact_bidirectional_bfs"
    else:
        ch_php21 = comp.shortcut_chain(comp.prove_tautology_shannon(not_php21_dnf, ["p11", "p21"]))
        mode_p21 = "constructive_verified_chain"
    results.append(
        verify_and_profile_chain(
            store, "not_php_2_1_dnf_to_1", "php", ch_php21, mode_p21, ["p11", "p21"], (time.perf_counter() - t0) * 1000
        )
    )

    # c2. ~PHP_2^1 in negated-CNF form: ~(p11 & p21 & (~p11 v ~p21)) -> 1
    t0 = time.perf_counter()
    php21_cnf = store.conj_many([p11, p21, store.disj(store.neg(p11), store.neg(p21))])
    not_php21_negcnf = store.neg(php21_cnf)
    ch_php21_nc = comp.shortcut_chain(comp.prove_tautology_shannon(not_php21_negcnf, ["p11", "p21"]))
    results.append(
        verify_and_profile_chain(
            store, "not_php_2_1_negcnf_to_1", "php", ch_php21_nc, "constructive_verified_chain", ["p11", "p21"], (time.perf_counter() - t0) * 1000, include_full_chain=(len(ch_php21_nc) <= 60)
        )
    )

    # c3. ~PHP_3^2 tautology (3 pigeons, 2 holes, 6 variables p_{i,j}):
    #     Every assignment violates a pigeon axiom (~p_{i,1} & ~p_{i,2}) or a hole axiom (p_{i,j} & p_{i',j}).
    t0 = time.perf_counter()
    p = {(i, j): store.var(f"p{i}{j}") for i in (1, 2, 3) for j in (1, 2)}
    php32_vars = [f"p{i}{j}" for i in (1, 2, 3) for j in (1, 2)]
    pigeon_fail = [store.conj(store.neg(p[(i, 1)]), store.neg(p[(i, 2)])) for i in (1, 2, 3)]
    hole_clash = [
        store.conj(p[(i1, j)], p[(i2, j)])
        for j in (1, 2)
        for i1 in (1, 2, 3)
        for i2 in range(i1 + 1, 4)
    ]
    not_php32 = store.disj_many(pigeon_fail + hole_clash)
    ch_php32 = comp.shortcut_chain(comp.prove_tautology_shannon(not_php32, php32_vars))
    results.append(
        verify_and_profile_chain(
            store, "not_php_3_2_to_1", "php", ch_php32, "constructive_verified_chain", php32_vars, (time.perf_counter() - t0) * 1000, include_full_chain=False
        )
    )

    out_path = Path("/home/miguel/certified-arith-preproc/results/krajicek_ew_graph_results.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "paper": "Jan Krajicek, Extended Frege proofs, circuits and rewriting (arXiv:2606.13367v2, 11.X.2026)",
        "v2_datta_dutta_self_tests": v2_tests,
        "total_hash_cons_nodes_allocated": len(store._id_to_key),
        "benchmarks": results,
    }
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    # Concise summary table to stdout
    print(f"V2 self-tests: {v2_tests['status']} (fanout2 single={v2_tests['fanout2_single_occurrence_approx']}, both={v2_tests['fanout2_simultaneous_both_approx']})")
    print(f"{'Benchmark':<28} {'Mode':<27} {'d_≈':>5} {'|C|':>4} {'Peak':>5} {'Ratio':>6} {'AND_d':>5} {'Fanout':>6} {'ms':>7}")
    print("-" * 102)
    for r in results:
        print(
            f"{r['name']:<28} {r['search_mode']:<27} {r['distance_steps']:>5} "
            f"{r['src_dag_size']:>4} {r['peak_dag_size']:>5} {r['dag_blowup_ratio']:>6.2f} "
            f"{r['peak_and_depth']:>5} {r['peak_max_gate_fanout']:>6} {r['elapsed_ms']:>7.1f}"
        )
    print(f"\nSaved verified JSON results to {out_path}")


if __name__ == "__main__":
    main()
