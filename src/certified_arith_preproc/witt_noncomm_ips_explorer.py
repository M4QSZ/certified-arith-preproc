"""
ATAQUE-06: Non-Commutative IPS over Truncated Witt Rings W_k(F_2) ≅ Z / 2^k Z
=============================================================================
Computes exact Nisan non-commutative bimodal matrix ranks:
  - rank_{F_2}(M_f)
  - rank_{Q}(M_f)
  - Smith Normal Form (SNF) over Z and Fitting/Smith invariant factors (d_1, ..., d_r)
    over Z/4Z (k=2) and Z/8Z (k=3)
for n in [2, 3, 4, 5, 6] across:
  (i)  Non-commutative Binary Value / Witt Carry polynomial:
         - f_Witt(x_1..x_n) = sum_{i=1}^n 2^{i-1} x_i + 1 (mod 2^k)
         - Ordered & Symmetrized carry e_2(x) over Z, Z/4Z, Z/8Z, plus Witt-scaled 2*e_2(x)
  (ii) Commutative vs Non-Commutative parity/carry powers:
         - (x_1 + ... + x_n)^2 mod 4 (and mod 8)
         - (x_1 + ... + x_n)^3 mod 4 (and mod 8)
       measuring exact Nisan ABP lower bound sum_d rank(M_d) and separation ratios.

Saves verified JSON results to:
  certified-arith-preproc/results/witt_noncomm_ips_results.json
"""

from __future__ import annotations

import itertools
import json
import math
from pathlib import Path
from typing import Dict, List, Tuple


# ---------------------------------------------------------------------------
# 1. Exact Linear Algebra: F_2 Rank, Integer Smith Normal Form, Z/2^k Z Fitting
# ---------------------------------------------------------------------------

def rank_f2(matrix: List[List[int]]) -> int:
    """Exact rank over F_2 via Gaussian elimination."""
    if not matrix or not matrix[0]:
        return 0
    rows = [[v % 2 for v in row] for row in matrix]
    m, n = len(rows), len(rows[0])
    r = 0
    for c in range(n):
        pivot = None
        for i in range(r, m):
            if rows[i][c] == 1:
                pivot = i
                break
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(m):
            if i != r and rows[i][c] == 1:
                rows[i] = [rows[i][j] ^ rows[r][j] for j in range(n)]
        r += 1
        if r == m:
            break
    return r


def _xgcd(a: int, b: int) -> Tuple[int, int, int]:
    """Extended GCD: returns (g, x, y) with g >= 0 and a*x + b*y = g."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def smith_normal_form_diag(matrix: List[List[int]]) -> List[int]:
    """
    Compute the exact positive diagonal entries (s_1, ..., s_r) of the
    Smith Normal Form over Z, satisfying s_1 | s_2 | ... | s_r and s_i > 0.
    """
    if not matrix or not matrix[0]:
        return []
    M = [[int(v) for v in row] for row in matrix]
    m, n = len(M), len(M[0])
    diag: List[int] = []
    k = 0

    while k < m and k < n:
        # Find smallest non-zero entry in submatrix M[k:, k:]
        best_pos = None
        best_val = None
        for i in range(k, m):
            for j in range(k, n):
                v = abs(M[i][j])
                if v != 0 and (best_val is None or v < best_val):
                    best_val = v
                    best_pos = (i, j)
        if best_pos is None:
            break

        pi, pj = best_pos
        if pi != k:
            M[k], M[pi] = M[pi], M[k]
        if pj != k:
            for row in M:
                row[k], row[pj] = row[pj], row[k]
        if M[k][k] < 0:
            M[k] = [-x for x in M[k]]

        # Reduce row k and column k until all off-pivot entries in row k / col k are 0
        # and M[k][k] divides every entry in M[k+1:, k+1:].
        while True:
            changed = False
            piv = M[k][k]
            # Eliminate column k below k
            for i in range(k + 1, m):
                if M[i][k] != 0:
                    if M[i][k] % piv == 0:
                        q = M[i][k] // piv
                        for j in range(k, n):
                            M[i][j] -= q * M[k][j]
                    else:
                        g, x, y = _xgcd(piv, M[i][k])
                        a_k = piv // g
                        a_i = M[i][k] // g
                        for j in range(k, n):
                            rkj, rij = M[k][j], M[i][j]
                            M[k][j] = x * rkj + y * rij
                            M[i][j] = -a_i * rkj + a_k * rij
                        piv = M[k][k]
                    changed = True

            # Eliminate row k right of k
            piv = M[k][k]
            for j in range(k + 1, n):
                if M[k][j] != 0:
                    if M[k][j] % piv == 0:
                        q = M[k][j] // piv
                        for i in range(k, m):
                            M[i][j] -= q * M[i][k]
                    else:
                        g, x, y = _xgcd(piv, M[k][j])
                        a_k = piv // g
                        a_j = M[k][j] // g
                        for i in range(k, m):
                            rik, rij = M[i][k], M[i][j]
                            M[i][k] = x * rik + y * rij
                            M[i][j] = -a_j * rik + a_k * rij
                        piv = M[k][k]
                    changed = True

            if M[k][k] < 0:
                M[k] = [-x for x in M[k]]

            if changed:
                continue

            # Check divisibility in submatrix M[k+1:, k+1:]
            piv = M[k][k]
            bad = None
            for i in range(k + 1, m):
                for j in range(k + 1, n):
                    if M[i][j] % piv != 0:
                        bad = (i, j)
                        break
                if bad is not None:
                    break
            if bad is not None:
                bi, _ = bad
                for j in range(k, n):
                    M[k][j] += M[bi][j]
                continue
            break

        diag.append(abs(M[k][k]))
        k += 1

    return diag


def analyze_matrix(matrix: List[List[int]]) -> Dict[str, object]:
    """
    Compute exact rank_{F_2}, rank_{Q}, SNF over Z, and Fitting/Smith
    invariant factors over Z/4Z and Z/8Z.
    """
    r_f2 = rank_f2(matrix)
    snf = smith_normal_form_diag(matrix)
    r_q = len(snf)
    r_f2_from_snf = sum(1 for s in snf if s % 2 != 0)
    assert r_f2 == r_f2_from_snf, f"F_2 rank mismatch: {r_f2} vs {r_f2_from_snf}"

    inv_z4 = [math.gcd(s, 4) for s in snf if math.gcd(s, 4) < 4]
    inv_z8 = [math.gcd(s, 8) for s in snf if math.gcd(s, 8) < 8]

    return {
        "rows": len(matrix),
        "cols": len(matrix[0]) if matrix else 0,
        "rank_F2": r_f2,
        "rank_Q": r_q,
        "snf_Z": snf,
        "invariant_factors_Z4": inv_z4,
        "module_rank_Z4": len(inv_z4),
        "zero_divisor_gap_Z4": len(inv_z4) - r_f2,
        "invariant_factors_Z8": inv_z8,
        "module_rank_Z8": len(inv_z8),
        "zero_divisor_gap_Z8": len(inv_z8) - r_f2,
    }


# ---------------------------------------------------------------------------
# 2. Non-Commutative Bimodal Nisan Matrix Construction
# ---------------------------------------------------------------------------

Word = Tuple[int, ...]
NCPoly = Dict[Word, int]


def build_nisan_matrix(poly: NCPoly, n: int, degree: int, cut: int) -> List[List[int]]:
    """
    Build Nisan's bimodal communication/partial-derivative matrix M_{cut}(poly)
    for homogeneous degree `degree` in variables {1, ..., n}.
    Rows: words u of length `cut`.
    Cols: words v of length `degree - cut`.
    Entry (u, v) = coeff of u + v in `poly`.
    """
    row_words = list(itertools.product(range(1, n + 1), repeat=cut))
    col_words = list(itertools.product(range(1, n + 1), repeat=degree - cut))
    mat: List[List[int]] = []
    for u in row_words:
        row = [poly.get(u + v, 0) for v in col_words]
        mat.append(row)
    return mat


def analyze_homogeneous_nc(poly: NCPoly, n: int, degree: int) -> Dict[str, object]:
    """Analyze M_d for all cuts d = 0..degree and aggregate Nisan ABP lower bounds."""
    cuts: Dict[str, Dict[str, object]] = {}
    sum_f2 = 0
    sum_q = 0
    sum_z4 = 0
    sum_z8 = 0
    for d in range(degree + 1):
        mat = build_nisan_matrix(poly, n, degree, d)
        info = analyze_matrix(mat)
        cuts[f"d={d}"] = info
        sum_f2 += int(info["rank_F2"])
        sum_q += int(info["rank_Q"])
        sum_z4 += int(info["module_rank_Z4"])
        sum_z8 += int(info["module_rank_Z8"])
    return {
        "degree": degree,
        "cuts": cuts,
        "nisan_abp_bound_F2": sum_f2,
        "nisan_abp_bound_Q": sum_q,
        "nisan_abp_bound_Z4": sum_z4,
        "nisan_abp_bound_Z8": sum_z8,
    }


# ---------------------------------------------------------------------------
# 3. Polynomial Families (i) and (ii)
# ---------------------------------------------------------------------------

def poly_witt_binary_value(n: int) -> NCPoly:
    """f_Witt(x_1..x_n) = sum_{i=1}^n 2^{i-1} x_i + 1 (degree 1 + constant)."""
    p: NCPoly = {(): 1}
    for i in range(1, n + 1):
        p[(i,)] = 1 << (i - 1)
    return p


def analyze_witt_binary_value(n: int) -> Dict[str, object]:
    """
    Nisan bimodal matrix for f_Witt over words of length <= 1:
    Split total degree <= 1 at cut d=0 (1 x (n+1)) and d=1 ((n+1) x 1),
    and homogeneous degree-1 part at d=0, d=1.
    """
    p = poly_witt_binary_value(n)
    # Homogeneous degree-1 part:
    p_deg1: NCPoly = {(i,): 1 << (i - 1) for i in range(1, n + 1)}
    deg1_analysis = analyze_homogeneous_nc(p_deg1, n, 1)
    # Full bimodal (constant + linear) matrix: rows {(), (1,), ..., (n,)}, cols {(), (1,), ..., (n,)}
    words = [()] + [(i,) for i in range(1, n + 1)]
    bimodal = [[p.get(u + v, 0) if len(u) + len(v) <= 1 else 0 for v in words] for u in words]
    return {
        "homogeneous_deg1": deg1_analysis,
        "inhomogeneous_bimodal_le1": analyze_matrix(bimodal),
    }


def poly_e2_ordered(n: int, scale: int = 1) -> NCPoly:
    """Ordered lift e_2^{ord}(x) = scale * sum_{1 <= i < j <= n} x_i x_j."""
    p: NCPoly = {}
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            p[(i, j)] = scale
    return p


def poly_e2_symmetrized(n: int, scale: int = 1) -> NCPoly:
    """Symmetrized NC lift e_2^{sym}(x) = scale * sum_{1 <= i < j <= n} (x_i x_j + x_j x_i)."""
    p: NCPoly = {}
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            p[(i, j)] = scale
            p[(j, i)] = scale
    return p


def poly_sum_power_nc(n: int, power: int) -> NCPoly:
    """Non-commutative (x_1 + ... + x_n)^power."""
    p: NCPoly = {}
    for w in itertools.product(range(1, n + 1), repeat=power):
        p[w] = p.get(w, 0) + 1
    return p


def poly_sum_power_comm_ordered(n: int, power: int) -> NCPoly:
    """
    Commutative (x_1 + ... + x_n)^power canonicalized to sorted words
    (i_1 <= i_2 <= ... <= i_power) in the free monoid.
    """
    p: NCPoly = {}
    for w in itertools.product(range(1, n + 1), repeat=power):
        sw = tuple(sorted(w))
        p[sw] = p.get(sw, 0) + 1
    return p


def run_explorer() -> Dict[str, object]:
    results: Dict[str, object] = {
        "metadata": {
            "attack": "ATAQUE-06",
            "title": "Non-Commutative IPS over Truncated Witt Rings W_k(F_2) ~= Z/2^kZ",
            "n_values": [2, 3, 4, 5, 6],
            "rings": ["F_2", "Q", "Z/4Z (W_2(F_2))", "Z/8Z (W_3(F_2))"],
        },
        "by_n": {},
    }

    for n in [2, 3, 4, 5, 6]:
        witt_bv = analyze_witt_binary_value(n)
        e2_ord = analyze_homogeneous_nc(poly_e2_ordered(n, 1), n, 2)
        e2_sym = analyze_homogeneous_nc(poly_e2_symmetrized(n, 1), n, 2)
        e2_sym_witt2 = analyze_homogeneous_nc(poly_e2_symmetrized(n, 2), n, 2)

        sq_nc = analyze_homogeneous_nc(poly_sum_power_nc(n, 2), n, 2)
        sq_comm = analyze_homogeneous_nc(poly_sum_power_comm_ordered(n, 2), n, 2)

        cube_nc = analyze_homogeneous_nc(poly_sum_power_nc(n, 3), n, 3)
        cube_comm = analyze_homogeneous_nc(poly_sum_power_comm_ordered(n, 3), n, 3)

        sq_sep = {
            "F2_ratio_comm_over_nc": round(sq_comm["nisan_abp_bound_F2"] / sq_nc["nisan_abp_bound_F2"], 6),
            "Q_ratio_comm_over_nc": round(sq_comm["nisan_abp_bound_Q"] / sq_nc["nisan_abp_bound_Q"], 6),
            "Z4_ratio_comm_over_nc": round(sq_comm["nisan_abp_bound_Z4"] / sq_nc["nisan_abp_bound_Z4"], 6),
            "Z8_ratio_comm_over_nc": round(sq_comm["nisan_abp_bound_Z8"] / sq_nc["nisan_abp_bound_Z8"], 6),
        }
        cube_sep = {
            "F2_ratio_comm_over_nc": round(cube_comm["nisan_abp_bound_F2"] / cube_nc["nisan_abp_bound_F2"], 6),
            "Q_ratio_comm_over_nc": round(cube_comm["nisan_abp_bound_Q"] / cube_nc["nisan_abp_bound_Q"], 6),
            "Z4_ratio_comm_over_nc": round(cube_comm["nisan_abp_bound_Z4"] / cube_nc["nisan_abp_bound_Z4"], 6),
            "Z8_ratio_comm_over_nc": round(cube_comm["nisan_abp_bound_Z8"] / cube_nc["nisan_abp_bound_Z8"], 6),
        }

        results["by_n"][str(n)] = {
            "witt_binary_value": witt_bv,
            "e2_ordered": e2_ord,
            "e2_symmetrized": e2_sym,
            "e2_symmetrized_witt_carry_2x": e2_sym_witt2,
            "power2_noncomm": sq_nc,
            "power2_comm_ordered": sq_comm,
            "power2_separation": sq_sep,
            "power3_noncomm": cube_nc,
            "power3_comm_ordered": cube_comm,
            "power3_separation": cube_sep,
        }

    return results


def main() -> None:
    results = run_explorer()
    out_path = Path("/home/miguel/certified-arith-preproc/results/witt_noncomm_ips_results.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    print("=== ATAQUE-06: Nisan Non-Commutative Rank & Witt Z/4Z, Z/8Z Invariant Factors ===")
    for n_str, entry in results["by_n"].items():
        e2_sym_d1 = entry["e2_symmetrized"]["cuts"]["d=1"]
        e2_2x_d1 = entry["e2_symmetrized_witt_carry_2x"]["cuts"]["d=1"]
        sq_nc = entry["power2_noncomm"]
        sq_cm = entry["power2_comm_ordered"]
        cb_nc = entry["power3_noncomm"]
        cb_cm = entry["power3_comm_ordered"]
        print(
            f"n={n_str} | "
            f"e2_sym M1: F2={e2_sym_d1['rank_F2']} Q={e2_sym_d1['rank_Q']} "
            f"Z4={e2_sym_d1['invariant_factors_Z4']} Z8={e2_sym_d1['invariant_factors_Z8']} | "
            f"2*e2_sym M1: F2={e2_2x_d1['rank_F2']} Z4={e2_2x_d1['invariant_factors_Z4']} | "
            f"(sum x)^2 ABP[Z4]: NC={sq_nc['nisan_abp_bound_Z4']} vs Comm={sq_cm['nisan_abp_bound_Z4']} "
            f"(ratio={entry['power2_separation']['Z4_ratio_comm_over_nc']}) | "
            f"(sum x)^3 ABP[Z4]: NC={cb_nc['nisan_abp_bound_Z4']} vs Comm={cb_cm['nisan_abp_bound_Z4']} "
            f"(ratio={entry['power3_separation']['Z4_ratio_comm_over_nc']})"
        )
    print(f"Saved JSON to {out_path}")


if __name__ == "__main__":
    main()
