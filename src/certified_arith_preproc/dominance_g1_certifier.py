#!/usr/bin/env python3
"""
ATAQUE-07: VeriPB 3.0 Dominance Rule (dom ~= G_1) Certifier & Benchmark Suite.

Generates and mechanically verifies with `veripb 3.0.2 --cnf` real `dom` (G_1) proofs for:
  (i)  PHP_{n+1}^n for n in [6, 8, 10, 12, 16] using explicit `def_order` lexicographic
       order + `dom` adjacent pigeon-transposition symmetry breaking (O(n^2) dom steps),
       compared against v0.4 Cutting-Planes `pol` proofs and Kissat 4.0.4.
  (ii) Symmetric Weak Rank / Parity-Permuted PHP (`Permuted_PHP`) and 1-Round Keccak
       chi-layer Bijection PHP (`Keccak_1Round_Bijection_PHP`) using `dom` / `red`
       witness orderings verified by `veripb 3.0.2`.

Saves verified `.pbp` certificates in `results/dominance_g1_pbp/` and complete JSON
metrics in `results/dominance_g1_results.json`.
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Tuple


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULTS_DIR = REPO_ROOT / "results"
PBP_DIR = RESULTS_DIR / "dominance_g1_pbp"
RESULTS_JSON = RESULTS_DIR / "dominance_g1_results.json"

VERIPB_BIN = os.environ.get("VERIPB_BIN", "veripb")
KISSAT_BIN = os.environ.get("KISSAT_BIN", "kissat")


# ---------------------------------------------------------------------------
# CNF & Proof Helpers
# ---------------------------------------------------------------------------

def write_dimacs_cnf(path: Path, num_vars: int, clauses: List[List[int]]) -> None:
    lines = [f"p cnf {num_vars} {len(clauses)}"]
    for cl in clauses:
        lines.append(" ".join(str(lit) for lit in cl) + " 0")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def lit_str(lit: int) -> str:
    return f"x{lit}" if lit > 0 else f"~x{-lit}"


def run_veripb(cnf_path: Path, pbp_path: Path, timeout_s: float = 60.0) -> Tuple[str, float, str]:
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [VERIPB_BIN, "--cnf", str(cnf_path), str(pbp_path)],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        out = (proc.stdout or "") + "\n" + (proc.stderr or "")
        if proc.returncode == 0 and "VERIFIED UNSATISFIABLE" in out:
            return "VERIFIED UNSATISFIABLE", round(elapsed_ms, 2), out.strip()
        return f"FAILED (rc={proc.returncode})", round(elapsed_ms, 2), out.strip()
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2), "timeout"


def run_kissat(cnf_path: Path, timeout_s: float = 30.0) -> Tuple[str, float]:
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [KISSAT_BIN, str(cnf_path)],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        out = proc.stdout or ""
        if "s UNSATISFIABLE" in out:
            return "UNSAT", round(elapsed_ms, 2)
        if "s SATISFIABLE" in out:
            return "SAT", round(elapsed_ms, 2)
        return f"UNKNOWN (rc={proc.returncode})", round(elapsed_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)


# ---------------------------------------------------------------------------
# (i) PHP_{n+1}^n: CNF, VeriPB 3.0 `dom` (G_1), and v0.4 Cutting-Planes `pol`
# ---------------------------------------------------------------------------

def generate_php_cnf(n: int) -> Tuple[int, List[List[int]]]:
    """Generate PHP_{n+1}^n: n+1 pigeons, n holes. var(i, j) = i*n + j + 1."""
    num_vars = (n + 1) * n
    clauses: List[List[int]] = []
    for i in range(n + 1):
        clauses.append([i * n + j + 1 for j in range(n)])
    for j in range(n):
        for i1 in range(n + 1):
            for i2 in range(i1 + 1, n + 1):
                clauses.append([-(i1 * n + j + 1), -(i2 * n + j + 1)])
    return num_vars, clauses


def _lex_order_block(
    order_name: str,
    num_order_vars: int,
    lit_signs: List[int] | None = None,
) -> List[str]:
    """Emit a VeriPB `def_order` block for lexicographic ordering over `num_order_vars`."""
    if lit_signs is None:
        lit_signs = [1] * num_order_vars
    u_vars = " ".join(f"u{k}" for k in range(1, num_order_vars + 1))
    v_vars = " ".join(f"v{k}" for k in range(1, num_order_vars + 1))
    w_vars = " ".join(f"w{k}" for k in range(1, num_order_vars + 1))
    terms = []
    for k in range(1, num_order_vars + 1):
        w = 1 << (num_order_vars - k)
        if lit_signs[k - 1] > 0:
            terms.append(f"{w} u{k} -{w} v{k}")
        else:
            terms.append(f"{w} ~u{k} -{w} ~v{k}")
    return [
        f"def_order {order_name}",
        "    vars",
        f"        left {u_vars}",
        f"        right {v_vars}",
        "        aux",
        "    end",
        "    def",
        f"        {' '.join(terms)} >= 0 ;",
        "    end",
        "    transitivity",
        "        vars",
        f"            fresh_right {w_vars}",
        "        end",
        "        proof",
        "            proofgoal #1",
        "                p 1 2 + 3 +",
        "            qed -1",
        "        qed",
        "    end",
        "end",
    ]


def emit_php_dom_pbp(n: int, num_clauses: int) -> Tuple[str, int, int]:
    """Emit O(n^2) `dom` proof for PHP_{n+1}^n. Returns (pbp_text, dom_steps, rup_steps)."""
    N = (n + 1) * n
    x_vars = " ".join(f"x{k}" for k in range(1, N + 1))
    lines = [
        "pseudo-Boolean proof version 2.0",
        f"f {num_clauses} 0",
        *_lex_order_block("lex_php", N),
        f"load_order lex_php {x_vars}",
    ]

    dom_steps = 0
    for i in range(n):
        subst = " ".join(
            f"x{i * n + j + 1} -> x{(i + 1) * n + j + 1} x{(i + 1) * n + j + 1} -> x{i * n + j + 1}"
            for j in range(n)
        )
        for j in range(n):
            prev = " ".join(f"1 x{i * n + k + 1}" for k in range(j))
            lhs = f"1 ~x{(i + 1) * n + j + 1}" + (" " + prev if prev else "")
            lines.append(f"dom {lhs} >= 1 ; {subst} ;")
            dom_steps += 1

    rup_steps = 0
    for j in range(n):
        for i in range(j + 1, n + 1):
            lines.append(f"u 1 ~x{i * n + j + 1} >= 1 ;")
            rup_steps += 1

    lines.append("u >= 1 ;")
    rup_steps += 1
    lines.append("output NONE")
    lines.append("conclusion UNSAT : -1")
    lines.append("end pseudo-Boolean proof")
    return "\n".join(lines) + "\n", dom_steps, rup_steps


def emit_php_cp_v04_pbp(n: int, num_clauses: int) -> Tuple[str, int]:
    """Emit v0.4 Cutting-Planes `pol` proof for PHP_{n+1}^n. Returns (pbp_text, pol_steps)."""
    lines = [
        "pseudo-Boolean proof version 2.0",
        f"f {num_clauses} 0",
    ]
    next_id = num_clauses + 1
    pol_steps = 0

    def hole_clause_id(j: int, i1: int, i2: int) -> int:
        # Pairwise clauses start at (n+1) + 1 = n + 2
        per_hole = (n + 1) * n // 2
        offset = j * per_hole
        # Index of (i1, i2) with 0 <= i1 < i2 <= n
        pair_idx = i1 * (n + 1) - i1 * (i1 + 1) // 2 + (i2 - i1 - 1)
        return (n + 1) + 1 + offset + pair_idx

    # Derive at-most-one for each hole j: sum_{i=0..n} ~x_{i,j} >= n
    amo_ids: List[int] = []
    for j in range(n):
        cur_id = hole_clause_id(j, 0, 1)
        for k in range(2, n + 1):
            # (k-1) * cur_id + sum_{i=0..k-1} clause(i, k) -> divide by k
            expr = f"{cur_id} {k - 1} *"
            for i in range(k):
                cid = hole_clause_id(j, i, k)
                expr += f" {cid} +"
            expr += f" {k} d"
            lines.append(f"p {expr}")
            cur_id = next_id
            next_id += 1
            pol_steps += 1
        amo_ids.append(cur_id)

    # Sum all pigeon clauses (IDs 1 .. n+1) and all at-most-one hole constraints
    sum_expr = "1"
    for pid in range(2, n + 2):
        sum_expr += f" {pid} +"
    for aid in amo_ids:
        sum_expr += f" {aid} +"
    lines.append(f"p {sum_expr}")
    pol_steps += 1

    lines.append("output NONE")
    lines.append("conclusion UNSAT : -1")
    lines.append("end pseudo-Boolean proof")
    return "\n".join(lines) + "\n", pol_steps


# ---------------------------------------------------------------------------
# (ii) Symmetric Weak Rank / Parity-Permuted PHP & Keccak Bijection PHP
# ---------------------------------------------------------------------------

def generate_permuted_php_cnf(n: int) -> Tuple[int, List[List[int]], List[int], List[int]]:
    """
    Parity-Permuted PHP_{n+1}^n:
    - Cyclic/involutive pigeon permutation `p_perm`
    - Deterministic parity mask `mask[i*n + j] = (i + j) % 2`
    """
    num_vars = (n + 1) * n
    p_perm = [(i * 3 + 1) % (n + 1) if (n + 1) % 3 != 0 else (n - i) for i in range(n + 1)]
    mask = [((i + j) % 2) for i in range(n + 1) for j in range(n)]

    def lit_of(i: int, j: int, positive: bool) -> int:
        v = p_perm[i] * n + j + 1
        eff_pos = positive if mask[v - 1] == 0 else not positive
        return v if eff_pos else -v

    clauses: List[List[int]] = []
    for i in range(n + 1):
        clauses.append([lit_of(i, j, True) for j in range(n)])
    for j in range(n):
        for i1 in range(n + 1):
            for i2 in range(i1 + 1, n + 1):
                clauses.append([lit_of(i1, j, False), lit_of(i2, j, False)])
    return num_vars, clauses, p_perm, mask


def emit_permuted_php_dom_pbp(
    n: int, num_clauses: int, p_perm: List[int], mask: List[int]
) -> Tuple[str, int, int]:
    """Emit VeriPB `dom` proof for Permuted_PHP_{n+1}^n using literal-polarity order."""
    N = (n + 1) * n
    # Order variables in logical pigeon order i=0..n, j=0..n-1
    ordered_vars = [p_perm[i] * n + j + 1 for i in range(n + 1) for j in range(n)]
    lit_signs = [1 if mask[v - 1] == 0 else -1 for v in ordered_vars]
    x_vars = " ".join(f"x{v}" for v in ordered_vars)

    lines = [
        "pseudo-Boolean proof version 2.0",
        f"f {num_clauses} 0",
        *_lex_order_block("lex_perm_php", N, lit_signs),
        f"load_order lex_perm_php {x_vars}",
    ]

    def logical_lit(i: int, j: int, positive: bool) -> str:
        v = p_perm[i] * n + j + 1
        eff_pos = positive if mask[v - 1] == 0 else not positive
        return f"x{v}" if eff_pos else f"~x{v}"

    dom_steps = 0
    for i in range(n):
        # Witness swaps logical pigeon i and i+1, respecting polarity masks!
        subst_parts = []
        for j in range(n):
            v1 = p_perm[i] * n + j + 1
            v2 = p_perm[i + 1] * n + j + 1
            if mask[v1 - 1] == mask[v2 - 1]:
                subst_parts.append(f"x{v1} -> x{v2} x{v2} -> x{v1}")
            else:
                subst_parts.append(f"x{v1} -> ~x{v2} x{v2} -> ~x{v1}")
        subst = " ".join(subst_parts)
        for j in range(n):
            prev = " ".join(f"1 {logical_lit(i, k, True)}" for k in range(j))
            lhs = f"1 {logical_lit(i + 1, j, False)}" + (" " + prev if prev else "")
            lines.append(f"dom {lhs} >= 1 ; {subst} ;")
            dom_steps += 1

    rup_steps = 0
    for j in range(n):
        for i in range(j + 1, n + 1):
            lines.append(f"u 1 {logical_lit(i, j, False)} >= 1 ;")
            rup_steps += 1

    lines.append("u >= 1 ;")
    rup_steps += 1
    lines.append("output NONE")
    lines.append("conclusion UNSAT : -1")
    lines.append("end pseudo-Boolean proof")
    return "\n".join(lines) + "\n", dom_steps, rup_steps


def generate_keccak_bijection_php_cnf(n: int) -> Tuple[int, List[List[int]]]:
    """
    1-Round Keccak chi-layer Bijection PHP_{n+1}^n (requires n divisible by 5, e.g. n=5, 10):
    For each pigeon row i, y_{i, 0..n-1} is coupled to input x_{i, 0..n-1} via 5-bit Keccak chi:
      y_{i, b*5 + r} = x_{i, b*5 + r} XOR ((~x_{i, b*5 + (r+1)%5}) AND x_{i, b*5 + (r+2)%5})
    encoded via Tseitin auxiliary variables z_{i, j} = (~x_{i, b*5+(r+1)%5} AND x_{i, b*5+(r+2)%5}),
    plus PHP_{n+1}^n on y.
    """
    assert n % 5 == 0, "n must be a multiple of 5 for 5-bit Keccak chi blocks"
    N = (n + 1) * n
    # Variable layout:
    # y_{i,j}: 1 .. N
    # x_{i,j}: N + 1 .. 2*N
    # z_{i,j}: 2*N + 1 .. 3*N
    num_vars = 3 * N
    clauses: List[List[int]] = []

    def y_var(i: int, j: int) -> int:
        return i * n + j + 1

    def x_var(i: int, j: int) -> int:
        return N + i * n + j + 1

    def z_var(i: int, j: int) -> int:
        return 2 * N + i * n + j + 1

    # PHP on y
    for i in range(n + 1):
        clauses.append([y_var(i, j) for j in range(n)])
    for j in range(n):
        for i1 in range(n + 1):
            for i2 in range(i1 + 1, n + 1):
                clauses.append([-y_var(i1, j), -y_var(i2, j)])

    # Keccak 5-bit chi-layer per pigeon row
    num_blocks = n // 5
    for i in range(n + 1):
        for b in range(num_blocks):
            base = b * 5
            for r in range(5):
                x0 = x_var(i, base + r)
                x1 = x_var(i, base + (r + 1) % 5)
                x2 = x_var(i, base + (r + 2) % 5)
                z = z_var(i, base + r)
                y = y_var(i, base + r)
                # z <-> (~x1 AND x2)
                clauses.append([-z, -x1])
                clauses.append([-z, x2])
                clauses.append([z, x1, -x2])
                # y <-> (x0 XOR z)
                clauses.append([-y, -x0, -z])
                clauses.append([-y, x0, z])
                clauses.append([y, -x0, z])
                clauses.append([y, x0, -z])

    return num_vars, clauses


def emit_keccak_bijection_php_dom_pbp(n: int, num_clauses: int) -> Tuple[str, int, int]:
    """
    Emit VeriPB `dom` + `red` proof for Keccak_1Round_Bijection_PHP_{n+1}^n.
    Swapping (y_{i,*}, x_{i,*}, z_{i,*}) <-> (y_{i+1,*}, x_{i+1,*}, z_{i+1,*}) is an exact
    row-wise automorphism of PHP(y) ^ (y = chi_5(x)).
    """
    N = (n + 1) * n
    y_vars = " ".join(f"x{k}" for k in range(1, N + 1))
    lines = [
        "pseudo-Boolean proof version 2.0",
        f"f {num_clauses} 0",
        *_lex_order_block("lex_keccak_php", N),
        f"load_order lex_keccak_php {y_vars}",
    ]

    dom_steps = 0
    for i in range(n):
        subst_parts = []
        for j in range(n):
            for offset in (0, N, 2 * N):
                v1 = offset + i * n + j + 1
                v2 = offset + (i + 1) * n + j + 1
                subst_parts.append(f"x{v1} -> x{v2} x{v2} -> x{v1}")
        subst = " ".join(subst_parts)
        for j in range(n):
            prev = " ".join(f"1 x{i * n + k + 1}" for k in range(j))
            lhs = f"1 ~x{(i + 1) * n + j + 1}" + (" " + prev if prev else "")
            lines.append(f"dom {lhs} >= 1 ; {subst} ;")
            dom_steps += 1

    rup_steps = 0
    for j in range(n):
        for i in range(j + 1, n + 1):
            lines.append(f"u 1 ~x{i * n + j + 1} >= 1 ;")
            rup_steps += 1

    lines.append("u >= 1 ;")
    rup_steps += 1
    lines.append("output NONE")
    lines.append("conclusion UNSAT : -1")
    lines.append("end pseudo-Boolean proof")
    return "\n".join(lines) + "\n", dom_steps, rup_steps


# ---------------------------------------------------------------------------
# Main Benchmark Runner
# ---------------------------------------------------------------------------

def main() -> None:
    PBP_DIR.mkdir(parents=True, exist_ok=True)
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    php_results: List[Dict] = []
    weak_rank_results: List[Dict] = []

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)

        # (i) PHP_{n+1}^n for n in [6, 8, 10, 12, 16]
        for n in [6, 8, 10, 12, 16]:
            num_vars, clauses = generate_php_cnf(n)
            cnf_path = tmp / f"php_{n+1}_{n}.cnf"
            write_dimacs_cnf(cnf_path, num_vars, clauses)

            # 1. VeriPB 3.0 dom (G_1)
            t_emit0 = time.perf_counter()
            dom_pbp_text, dom_steps, rup_steps = emit_php_dom_pbp(n, len(clauses))
            dom_emit_ms = round((time.perf_counter() - t_emit0) * 1000.0, 2)
            dom_pbp_path = PBP_DIR / f"php_{n+1}_{n}_dom_g1.pbp"
            dom_pbp_path.write_text(dom_pbp_text, encoding="utf-8")
            dom_status, dom_veripb_ms, dom_log = run_veripb(cnf_path, dom_pbp_path, timeout_s=60.0)
            dom_lines = dom_pbp_text.count("\n")
            dom_bytes = dom_pbp_path.stat().st_size

            # 2. v0.4 Cutting-Planes pol
            cp_pbp_text, pol_steps = emit_php_cp_v04_pbp(n, len(clauses))
            cp_pbp_path = PBP_DIR / f"php_{n+1}_{n}_cp_v04.pbp"
            cp_pbp_path.write_text(cp_pbp_text, encoding="utf-8")
            cp_status, cp_veripb_ms, cp_log = run_veripb(cnf_path, cp_pbp_path, timeout_s=60.0)
            cp_lines = cp_pbp_text.count("\n")
            cp_bytes = cp_pbp_path.stat().st_size

            # 3. Kissat 4.0.4
            kissat_status, kissat_ms = run_kissat(cnf_path, timeout_s=30.0)

            entry = {
                "instance": f"PHP_{n+1}_{n}",
                "n": n,
                "vars": num_vars,
                "clauses": len(clauses),
                "dom_g1": {
                    "status": dom_status,
                    "emit_ms": dom_emit_ms,
                    "veripb_ms": dom_veripb_ms,
                    "dom_steps": dom_steps,
                    "rup_steps": rup_steps,
                    "pbp_lines": dom_lines,
                    "pbp_bytes": dom_bytes,
                    "pbp_file": str(dom_pbp_path.relative_to(REPO_ROOT)),
                },
                "cp_v04": {
                    "status": cp_status,
                    "veripb_ms": cp_veripb_ms,
                    "pol_steps": pol_steps,
                    "pbp_lines": cp_lines,
                    "pbp_bytes": cp_bytes,
                    "pbp_file": str(cp_pbp_path.relative_to(REPO_ROOT)),
                },
                "kissat": {
                    "status": kissat_status,
                    "time_ms": kissat_ms,
                },
            }
            php_results.append(entry)
            print(
                f"[PHP_{n+1}_{n}] dom={dom_status} ({dom_veripb_ms}ms, {dom_lines}L) | "
                f"cp_v04={cp_status} ({cp_veripb_ms}ms, {cp_lines}L) | "
                f"kissat={kissat_status} ({kissat_ms}ms)"
            )

        # (ii-a) Permuted_PHP_{n+1}^n for n in [6, 8, 10, 12]
        for n in [6, 8, 10, 12]:
            num_vars, clauses, p_perm, mask = generate_permuted_php_cnf(n)
            cnf_path = tmp / f"permuted_php_{n+1}_{n}.cnf"
            write_dimacs_cnf(cnf_path, num_vars, clauses)

            t_emit0 = time.perf_counter()
            pbp_text, dom_steps, rup_steps = emit_permuted_php_dom_pbp(n, len(clauses), p_perm, mask)
            emit_ms = round((time.perf_counter() - t_emit0) * 1000.0, 2)
            pbp_path = PBP_DIR / f"permuted_php_{n+1}_{n}_dom_g1.pbp"
            pbp_path.write_text(pbp_text, encoding="utf-8")
            status, veripb_ms, _ = run_veripb(cnf_path, pbp_path, timeout_s=60.0)
            kissat_status, kissat_ms = run_kissat(cnf_path, timeout_s=30.0)

            entry = {
                "instance": f"Permuted_PHP_{n+1}_{n}",
                "family": "Permuted_PHP",
                "n": n,
                "vars": num_vars,
                "clauses": len(clauses),
                "dom_g1": {
                    "status": status,
                    "emit_ms": emit_ms,
                    "veripb_ms": veripb_ms,
                    "dom_steps": dom_steps,
                    "rup_steps": rup_steps,
                    "pbp_lines": pbp_text.count("\n"),
                    "pbp_bytes": pbp_path.stat().st_size,
                    "pbp_file": str(pbp_path.relative_to(REPO_ROOT)),
                },
                "kissat": {
                    "status": kissat_status,
                    "time_ms": kissat_ms,
                },
            }
            weak_rank_results.append(entry)
            print(
                f"[Permuted_PHP_{n+1}_{n}] dom={status} ({veripb_ms}ms) | "
                f"kissat={kissat_status} ({kissat_ms}ms)"
            )

        # (ii-b) Keccak_1Round_Bijection_PHP_{n+1}^n for n in [5, 10]
        for n in [5, 10]:
            num_vars, clauses = generate_keccak_bijection_php_cnf(n)
            cnf_path = tmp / f"keccak_php_{n+1}_{n}.cnf"
            write_dimacs_cnf(cnf_path, num_vars, clauses)

            t_emit0 = time.perf_counter()
            pbp_text, dom_steps, rup_steps = emit_keccak_bijection_php_dom_pbp(n, len(clauses))
            emit_ms = round((time.perf_counter() - t_emit0) * 1000.0, 2)
            pbp_path = PBP_DIR / f"keccak_1round_bijection_php_{n+1}_{n}_dom_g1.pbp"
            pbp_path.write_text(pbp_text, encoding="utf-8")
            status, veripb_ms, _ = run_veripb(cnf_path, pbp_path, timeout_s=60.0)
            kissat_status, kissat_ms = run_kissat(cnf_path, timeout_s=30.0)

            entry = {
                "instance": f"Keccak_1Round_Bijection_PHP_{n+1}_{n}",
                "family": "Keccak_1Round_Bijection_PHP",
                "n": n,
                "vars": num_vars,
                "clauses": len(clauses),
                "dom_g1": {
                    "status": status,
                    "emit_ms": emit_ms,
                    "veripb_ms": veripb_ms,
                    "dom_steps": dom_steps,
                    "rup_steps": rup_steps,
                    "pbp_lines": pbp_text.count("\n"),
                    "pbp_bytes": pbp_path.stat().st_size,
                    "pbp_file": str(pbp_path.relative_to(REPO_ROOT)),
                },
                "kissat": {
                    "status": kissat_status,
                    "time_ms": kissat_ms,
                },
            }
            weak_rank_results.append(entry)
            print(
                f"[Keccak_1Round_Bijection_PHP_{n+1}_{n}] dom={status} ({veripb_ms}ms) | "
                f"kissat={kissat_status} ({kissat_ms}ms)"
            )

    summary = {
        "veripb_version": "3.0.2",
        "kissat_version": "4.0.4",
        "php_suite": php_results,
        "weak_rank_and_bijection_suite": weak_rank_results,
    }
    RESULTS_JSON.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Saved results to {RESULTS_JSON}")


if __name__ == "__main__":
    main()
