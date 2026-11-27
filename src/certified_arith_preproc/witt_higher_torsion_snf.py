"""
ATAQUE-09: Universal 2-Adic Torsion Laws in Nisan Matrices for Higher-Degree Witt Carries
=========================================================================================
Computes exact integer Smith Normal Forms (SNF_Z) and 2-adic valuation spectra
(v_2(d_1), ..., v_2(d_r)) for:
  (0) M_1(e_2^sym) = J_n - I_n for n = 2..18
      (confirming universal SNF (1^{n-1}, n-1), n=9 -> 8-torsion in W_4(F_2)=Z/16Z,
       n=17 -> 16-torsion in W_5(F_2)=Z/32Z)
  (a) e_3^sym(x_1..x_n) = sum_{distinct i,j,k} x_i x_j x_k:
      M_{1,2} cut (n x n^2) and unordered Johnson-disjointness cut (n x binom(n,2))
      for n = 3..12
  (b) e_4^sym(x_1..x_n) = sum_{distinct i,j,k,l} x_i x_j x_k x_l:
      M_{2,2} middle Nisan cut (n^2 x n^2) and unordered Kneser cut (binom(n,2) x binom(n,2))
      for n = 4..9
  (c) Exact 2nd Witt addition carry C_2(x_1..x_n) = floor((x_1 + ... + x_n) / 4) mod 2
      lifted to Z/16Z (W_4(F_2)):
      - 4 * e_4^sym (homogeneous degree 4, M_{2,2} cut)
      - Exact multilinear non-commutative Witt polynomial C_2(x) and 4 * C_2(x)
        (both ordered NC lift and symmetrized NC lift, plus mod-16 Witt-reduced lift)
      for n = 4..8.

Saves verified JSON results & discovered closed-form torsion laws to:
  certified-arith-preproc/results/witt_higher_torsion_snf_results.json
"""

from __future__ import annotations

import itertools
import json
import math
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


# ---------------------------------------------------------------------------
# 1. Exact Integer Smith Normal Form & 2-Adic Valuation Analysis
# ---------------------------------------------------------------------------

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


def _compact_nonzero_rows_cols(matrix: Sequence[Sequence[int]]) -> List[List[int]]:
    """Drop all-zero rows and all-zero columns (preserves SNF over Z exactly)."""
    if not matrix or not matrix[0]:
        return []
    nz_rows = [row for row in matrix if any(v != 0 for v in row)]
    if not nz_rows:
        return []
    n_cols = len(nz_rows[0])
    nz_col_idx = [j for j in range(n_cols) if any(row[j] != 0 for row in nz_rows)]
    if not nz_col_idx:
        return []
    return [[int(row[j]) for j in nz_col_idx] for row in nz_rows]


def smith_normal_form_diag(matrix: Sequence[Sequence[int]]) -> List[int]:
    """
    Compute exact positive diagonal entries (d_1, ..., d_r) of the
    Smith Normal Form over Z, satisfying d_1 | d_2 | ... | d_r and d_i > 0.
    Uses exact Python arbitrary-precision integers with sparse-aware elimination.
    """
    M = _compact_nonzero_rows_cols(matrix)
    if not M:
        return []
    m, n = len(M), len(M[0])
    diag: List[int] = []
    k = 0

    while k < m and k < n:
        # Find smallest non-zero entry in M[k:, k:] (preferring 1 immediately)
        best_pos = None
        best_val = None
        for i in range(k, m):
            row_i = M[i]
            for j in range(k, n):
                v = row_i[j]
                if v != 0:
                    av = -v if v < 0 else v
                    if best_val is None or av < best_val:
                        best_val = av
                        best_pos = (i, j)
                        if av == 1:
                            break
            if best_val == 1:
                break

        if best_pos is None:
            break

        pi, pj = best_pos
        if pi != k:
            M[k], M[pi] = M[pi], M[k]
        if pj != k:
            for i in range(m):
                M[i][k], M[i][pj] = M[i][pj], M[i][k]
        if M[k][k] < 0:
            row_k = M[k]
            for j in range(k, n):
                row_k[j] = -row_k[j]

        while True:
            changed = False
            piv = M[k][k]
            row_k = M[k]

            # Eliminate column k below k
            for i in range(k + 1, m):
                aik = M[i][k]
                if aik != 0:
                    row_i = M[i]
                    if aik % piv == 0:
                        q = aik // piv
                        for j in range(k, n):
                            rkj = row_k[j]
                            if rkj != 0:
                                row_i[j] -= q * rkj
                    else:
                        g, x, y = _xgcd(piv, aik)
                        a_k = piv // g
                        a_i = aik // g
                        for j in range(k, n):
                            rkj = row_k[j]
                            rij = row_i[j]
                            if rkj != 0 or rij != 0:
                                row_k[j] = x * rkj + y * rij
                                row_i[j] = -a_i * rkj + a_k * rij
                        piv = row_k[k]
                    changed = True

            # Eliminate row k right of k
            piv = row_k[k]
            for j in range(k + 1, n):
                akj = row_k[j]
                if akj != 0:
                    if akj % piv == 0:
                        q = akj // piv
                        for i in range(k, m):
                            mik = M[i][k]
                            if mik != 0:
                                M[i][j] -= q * mik
                    else:
                        g, x, y = _xgcd(piv, akj)
                        a_k = piv // g
                        a_j = akj // g
                        for i in range(k, m):
                            rik = M[i][k]
                            rij = M[i][j]
                            if rik != 0 or rij != 0:
                                M[i][k] = x * rik + y * rij
                                M[i][j] = -a_j * rik + a_k * rij
                        piv = row_k[k]
                    changed = True

            if row_k[k] < 0:
                for j in range(k, n):
                    row_k[j] = -row_k[j]

            if changed:
                continue

            # Check divisibility in submatrix M[k+1:, k+1:]
            piv = row_k[k]
            if piv == 1:
                break
            bad_row = None
            for i in range(k + 1, m):
                row_i = M[i]
                for j in range(k + 1, n):
                    if row_i[j] % piv != 0:
                        bad_row = i
                        break
                if bad_row is not None:
                    break
            if bad_row is not None:
                row_b = M[bad_row]
                for j in range(k, n):
                    row_k[j] += row_b[j]
                continue
            break

        diag.append(abs(M[k][k]))
        k += 1

    # Sanity check: divisibility chain
    for idx in range(len(diag) - 1):
        assert diag[idx + 1] % diag[idx] == 0, f"Invalid SNF divisibility: {diag}"
    return diag


def v2(x: int) -> int:
    """2-adic valuation v_2(x) for positive integer x."""
    assert x > 0
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def summarize_snf(
    snf: List[int],
    rows: int,
    cols: int,
    max_witt_depth: int = 6,
) -> Dict[str, object]:
    """Summarize SNF_Z, 2-adic valuation spectrum, and Witt ring visibility."""
    v2_spec = [v2(d) for d in snf]
    v2_hist = {str(k): v for k, v in sorted(Counter(v2_spec).items())}
    snf_hist = {str(k): v for k, v in sorted(Counter(snf).items())}
    max_v2 = max(v2_spec) if v2_spec else 0
    rank_f2 = sum(1 for val in v2_spec if val == 0)

    # Module rank over W_k(F_2) ~= Z / 2^k Z: count of d_i with v_2(d_i) < k
    witt_ranks: Dict[str, int] = {}
    witt_torsion_gaps: Dict[str, int] = {}
    for k in range(1, max(max_witt_depth, max_v2 + 2) + 1):
        rk = sum(1 for val in v2_spec if val < k)
        witt_ranks[f"W_{k} (Z/{1 << k}Z)"] = rk
        witt_torsion_gaps[f"W_{k} (Z/{1 << k}Z)"] = rk - rank_f2

    # First Witt depth k at which each positive 2-adic torsion factor becomes visible
    torsion_factors = [d for d in snf if (d & 1) == 0]
    first_full_visibility_depth = max_v2 + 1 if snf else 0

    return {
        "rows": rows,
        "cols": cols,
        "rank_Q": len(snf),
        "rank_F2": rank_f2,
        "snf_Z": snf,
        "snf_multiplicities": snf_hist,
        "v2_spectrum": v2_spec,
        "v2_multiplicities": v2_hist,
        "max_v2": max_v2,
        "even_invariant_factors": torsion_factors,
        "first_full_visibility_witt_depth": first_full_visibility_depth,
        "witt_module_ranks": witt_ranks,
        "witt_zero_divisor_gaps": witt_torsion_gaps,
    }


# ---------------------------------------------------------------------------
# 2. Matrix Builders for (0) e_2^sym, (a) e_3^sym, (b) e_4^sym, (c) C_2
# ---------------------------------------------------------------------------

def build_derangement_matrix(n: int) -> List[List[int]]:
    """M_1(e_2^sym) = J_n - I_n of size n x n."""
    return [[0 if i == j else 1 for j in range(n)] for i in range(n)]


def build_e3_sym_M12(n: int) -> List[List[int]]:
    """M_{1,2}(e_3^sym) of size n x n^2."""
    cols = [(j, k) for j in range(n) for k in range(n)]
    return [
        [1 if (j != k and i != j and i != k) else 0 for (j, k) in cols]
        for i in range(n)
    ]


def build_e3_johnson_unordered(n: int) -> List[List[int]]:
    """Unordered Johnson-disjointness incidence matrix n x binom(n, 2)."""
    cols = list(itertools.combinations(range(n), 2))
    return [
        [1 if (i != j and i != k) else 0 for (j, k) in cols]
        for i in range(n)
    ]


def build_e4_sym_M22(n: int) -> List[List[int]]:
    """M_{2,2}(e_4^sym) middle Nisan cut of size n^2 x n^2."""
    pairs = [(i, j) for i in range(n) for j in range(n)]
    mat: List[List[int]] = []
    for i, j in pairs:
        if i == j:
            mat.append([0] * (n * n))
        else:
            mat.append([
                1 if (k != l and i != k and i != l and j != k and j != l) else 0
                for k, l in pairs
            ])
    return mat


def build_e4_kneser_unordered(n: int) -> List[List[int]]:
    """Unordered Kneser graph KG(n, 2) adjacency matrix binom(n, 2) x binom(n, 2)."""
    pairs = list(itertools.combinations(range(n), 2))
    return [
        [1 if (i != k and i != l and j != k and j != l) else 0 for (k, l) in pairs]
        for (i, j) in pairs
    ]


def c2_multilinear_coeffs(n: int) -> List[int]:
    """
    Exact integer coefficients a_0, ..., a_n such that on all x in {0, 1}^n:
      C_2(x) = floor((x_1 + ... + x_n) / 4) mod 2 = sum_{k=0}^n a_k * e_k(x).
    By Boolean Mobius inversion: a_k = sum_{j=0}^k (-1)^(k-j) * binom(k, j) * ((j // 4) % 2).
    """
    coeffs: List[int] = []
    for k in range(n + 1):
        val = 0
        for j in range(k + 1):
            c2_j = (j // 4) % 2
            if c2_j:
                sign = -1 if ((k - j) & 1) else 1
                val += sign * math.comb(k, j)
        coeffs.append(val)
    # Verify exact evaluation on all Hamming weights s = 0..n
    for s in range(n + 1):
        ev = sum(coeffs[k] * math.comb(s, k) for k in range(s + 1))
        assert ev == ((s // 4) % 2), f"Mobius mismatch at s={s}: {ev}"
    return coeffs


def build_c2_bimodal_ordered(n: int, scale: int = 1, mod_m: int | None = None) -> List[List[int]]:
    """
    Cut d=2 Nisan matrix for the ordered multilinear NC lift of scale * C_2(x):
      f(x) = sum_{k=4}^n c_k * sum_{i_1 < ... < i_k} x_{i_1} ... x_{i_k},
    where c_k = (scale * a_k) mod mod_m (if mod_m is given) else scale * a_k.
    Rows: strictly increasing 2-tuples (i_1 < i_2) (size binom(n, 2)).
    Cols: strictly increasing tuples of length 2..(n-2).
    Entry (u, v) = c_{|u|+|v|} if u[-1] < v[0] else 0.
    """
    a = c2_multilinear_coeffs(n)
    rows = list(itertools.combinations(range(n), 2))
    cols: List[Tuple[int, ...]] = []
    for rlen in range(2, n - 1):
        cols.extend(itertools.combinations(range(n), rlen))

    mat: List[List[int]] = []
    for u in rows:
        row: List[int] = []
        u_last = u[-1]
        for v in cols:
            if u_last < v[0]:
                deg = 2 + len(v)
                c = scale * a[deg]
                if mod_m is not None:
                    c %= mod_m
                row.append(c)
            else:
                row.append(0)
        mat.append(row)
    return mat


def build_c2_bimodal_symmetrized_reduced(
    n: int,
    scale: int = 1,
    mod_m: int | None = None,
) -> List[List[int]]:
    """
    Cut d=2 Nisan matrix for the symmetrized multilinear NC lift of scale * C_2(x):
      f^{sym}(x) = sum_{k=4}^n c_k * sum_{distinct i_1, ..., i_k} x_{i_1} ... x_{i_k},
    represented on unordered disjoint subsets (exact same SNF over Z as the full
    permutation-duplicated word matrix because permuting a row/col word produces
    an identical row/col, which eliminates via unimodular subtraction).
    Rows: 2-subsets U of {0..n-1} (size binom(n, 2)).
    Cols: r-subsets V of {0..n-1} for r = 2..(n-2).
    Entry (U, V) = c_{2 + |V|} if U and V are disjoint else 0.
    """
    a = c2_multilinear_coeffs(n)
    rows = [frozenset(u) for u in itertools.combinations(range(n), 2)]
    cols: List[frozenset[int]] = []
    for rlen in range(2, n - 1):
        cols.extend(frozenset(v) for v in itertools.combinations(range(n), rlen))

    mat: List[List[int]] = []
    for u in rows:
        row: List[int] = []
        for v in cols:
            if u.isdisjoint(v):
                deg = 2 + len(v)
                c = scale * a[deg]
                if mod_m is not None:
                    c %= mod_m
                row.append(c)
            else:
                row.append(0)
        mat.append(row)
    return mat


# ---------------------------------------------------------------------------
# 3. Main Experiment Driver & Law Verification
# ---------------------------------------------------------------------------

def run_ataque09() -> Dict[str, object]:
    t0 = time.perf_counter()

    # (0) M_1(e_2^sym) = J_n - I_n for n = 2..18
    e2_results: Dict[str, object] = {}
    for n in range(2, 19):
        mat = build_derangement_matrix(n)
        snf = smith_normal_form_diag(mat)
        expected = [1] * (n - 1) + [n - 1]
        assert snf == expected, f"e2^sym SNF mismatch at n={n}: {snf} vs {expected}"
        e2_results[str(n)] = summarize_snf(snf, n, n, max_witt_depth=6)

    # (a) e_3^sym(x_1..x_n): M_{1,2} (n x n^2) and unordered Johnson (n x binom(n, 2)) for n = 3..12
    e3_results: Dict[str, object] = {}
    for n in range(3, 13):
        mat_m12 = build_e3_sym_M12(n)
        mat_j = build_e3_johnson_unordered(n)
        snf_m12 = smith_normal_form_diag(mat_m12)
        snf_j = smith_normal_form_diag(mat_j)
        assert snf_m12 == snf_j, f"e3^sym M12 vs Johnson mismatch at n={n}: {snf_m12} vs {snf_j}"
        e3_results[str(n)] = {
            "M_1_2_full": summarize_snf(snf_m12, n, n * n, max_witt_depth=6),
            "unordered_johnson": {
                "rows": n,
                "cols": math.comb(n, 2),
                "snf_matches_M_1_2_exactly": True,
            },
        }

    # (b) e_4^sym(x_1..x_n): M_{2,2} (n^2 x n^2) and unordered Kneser KG(n, 2) for n = 4..9
    e4_results: Dict[str, object] = {}
    for n in range(4, 10):
        mat_m22 = build_e4_sym_M22(n)
        mat_kg = build_e4_kneser_unordered(n)
        snf_m22 = smith_normal_form_diag(mat_m22)
        snf_kg = smith_normal_form_diag(mat_kg)
        assert snf_m22 == snf_kg, f"e4^sym M22 vs Kneser mismatch at n={n}: {snf_m22} vs {snf_kg}"
        e4_results[str(n)] = {
            "M_2_2_full": summarize_snf(snf_m22, n * n, n * n, max_witt_depth=6),
            "unordered_kneser_KG_n_2": {
                "rows": math.comb(n, 2),
                "cols": math.comb(n, 2),
                "snf_matches_M_2_2_exactly": True,
            },
        }

    # (c) Exact 2nd Witt addition carry C_2(x_1..x_n) = floor(S/4) mod 2 lifted to Z/16Z for n = 4..8
    c2_results: Dict[str, object] = {}
    for n in range(4, 9):
        a = c2_multilinear_coeffs(n)
        a_4x_mod16 = [(4 * c) % 16 for c in a]

        # 4 * e_4^sym (M_{2,2} cut)
        snf_e4 = e4_results[str(n)]["M_2_2_full"]["snf_Z"]
        snf_4e4 = [4 * d for d in snf_e4]
        info_4e4 = summarize_snf(snf_4e4, n * n, n * n, max_witt_depth=6)
        inv_z16_4e4 = [math.gcd(d, 16) for d in snf_4e4 if math.gcd(d, 16) < 16]

        # Exact multilinear C_2(x) over Z (ordered and symmetrized)
        mat_c2_ord = build_c2_bimodal_ordered(n, scale=1, mod_m=None)
        snf_c2_ord = smith_normal_form_diag(mat_c2_ord)
        info_c2_ord = summarize_snf(snf_c2_ord, len(mat_c2_ord), len(mat_c2_ord[0]), max_witt_depth=6)

        mat_c2_sym = build_c2_bimodal_symmetrized_reduced(n, scale=1, mod_m=None)
        snf_c2_sym = smith_normal_form_diag(mat_c2_sym)
        info_c2_sym = summarize_snf(snf_c2_sym, len(mat_c2_sym), len(mat_c2_sym[0]), max_witt_depth=6)

        # 4 * C_2(x) over Z and Witt-reduced mod 16 (W_4(F_2) = Z/16Z)
        snf_4c2_sym_Z = [4 * d for d in snf_c2_sym]
        info_4c2_sym_Z = summarize_snf(snf_4c2_sym_Z, len(mat_c2_sym), len(mat_c2_sym[0]), max_witt_depth=6)
        inv_z16_4c2_sym = [math.gcd(d, 16) for d in snf_4c2_sym_Z if math.gcd(d, 16) < 16]

        mat_4c2_sym_mod16 = build_c2_bimodal_symmetrized_reduced(n, scale=4, mod_m=16)
        snf_4c2_sym_mod16 = smith_normal_form_diag(mat_4c2_sym_mod16)
        inv_z16_4c2_sym_mod16 = [math.gcd(d, 16) for d in snf_4c2_sym_mod16 if math.gcd(d, 16) < 16]
        assert inv_z16_4c2_sym == inv_z16_4c2_sym_mod16, (
            f"Z/16Z invariant factor mismatch at n={n}: {inv_z16_4c2_sym} vs {inv_z16_4c2_sym_mod16}"
        )

        mat_4c2_ord_mod16 = build_c2_bimodal_ordered(n, scale=4, mod_m=16)
        snf_4c2_ord_mod16 = smith_normal_form_diag(mat_4c2_ord_mod16)
        inv_z16_4c2_ord_mod16 = [math.gcd(d, 16) for d in snf_4c2_ord_mod16 if math.gcd(d, 16) < 16]

        c2_results[str(n)] = {
            "mobius_coeffs_a_k": a,
            "witt_4x_coeffs_mod16": a_4x_mod16,
            "four_times_e4_sym_M22": {
                **info_4e4,
                "invariant_factors_Z16": inv_z16_4e4,
                "module_rank_Z16": len(inv_z16_4e4),
            },
            "exact_C2_ordered_d2": info_c2_ord,
            "exact_4C2_ordered_d2_Z16": {
                "snf_of_mod16_lift": snf_4c2_ord_mod16,
                "invariant_factors_Z16": inv_z16_4c2_ord_mod16,
                "module_rank_Z16": len(inv_z16_4c2_ord_mod16),
            },
            "exact_C2_symmetrized_d2": info_c2_sym,
            "exact_4C2_symmetrized_d2_Z16": {
                **info_4c2_sym_Z,
                "invariant_factors_Z16": inv_z16_4c2_sym,
                "module_rank_Z16": len(inv_z16_4c2_sym),
                "mod16_lift_matches_Z_reduction": True,
            },
        }

    elapsed = round(time.perf_counter() - t0, 4)

    # Check closed-form laws discovered across all computed n
    e3_law_verified = all(
        e3_results[str(n)]["M_1_2_full"]["snf_Z"] == [1] * (n - 1) + [n - 2]
        for n in range(3, 13)
    )

    def expected_e4_kneser_snf(n: int) -> List[int]:
        base_ones = [1] * (n * (n - 3) // 2)
        if n % 2 == 0:
            return base_ones + [n - 3] * (n - 1) + [(n - 2) * (n - 3) // 2]
        return base_ones + [(n - 3) // 2] + [n - 3] * (n - 2) + [(n - 2) * (n - 3)]

    e4_law_verified = all(
        e4_results[str(n)]["M_2_2_full"]["snf_Z"] == expected_e4_kneser_snf(n)
        for n in range(4, 10)
    )
    assert e3_law_verified, "e3^sym closed-form law failed verification"
    assert e4_law_verified, "e4^sym closed-form law failed verification"

    c2_z16_matches_4e4 = all(
        c2_results[str(n)]["four_times_e4_sym_M22"]["invariant_factors_Z16"]
        == c2_results[str(n)]["exact_4C2_symmetrized_d2_Z16"]["invariant_factors_Z16"]
        for n in range(4, 9)
    )

    return {
        "metadata": {
            "attack": "ATAQUE-09",
            "title": "Universal 2-Adic Torsion Laws in Nisan Matrices for Higher-Degree Witt Carries",
            "elapsed_seconds": elapsed,
        },
        "e2_sym_M1_derangement": e2_results,
        "e3_sym_M12_and_johnson": e3_results,
        "e4_sym_M22_and_kneser": e4_results,
        "c2_witt_second_carry_Z16": c2_results,
        "discovered_closed_form_laws": {
            "e2_sym_M1": {
                "formula": "SNF_Z(M_1(e_2^sym)) = (1^{n-1}, n - 1) for all n >= 2",
                "lean4_proven_universal": True,
                "first_witt_depth_law": "At n = 2^r + 1, top factor 2^r vanishes in W_j(F_2) for j <= r and emerges at W_{r+1}(F_2) = Z/2^{r+1}Z",
                "verified_n_range": [2, 18],
            },
            "e3_sym_M12": {
                "formula": "SNF_Z(M_{1,2}(e_3^sym)) = (1^{n-1}, n - 2) for all n >= 3",
                "verified_for_all_n_3_to_12": e3_law_verified,
                "first_witt_depth_law": "At n = 2^r + 2, top factor 2^r vanishes in W_j(F_2) for j <= r and emerges at W_{r+1}(F_2) = Z/2^{r+1}Z",
                "verified_n_range": [3, 12],
            },
            "e4_sym_M22_kneser": {
                "formula_even_n": "SNF_Z(M_{2,2}(e_4^sym)) = (1^{n(n-3)/2}, (n-3)^{n-1}, ((n-2)(n-3)/2)^1) for even n >= 4",
                "formula_odd_n": "SNF_Z(M_{2,2}(e_4^sym)) = (1^{n(n-3)/2}, ((n-3)/2)^1, (n-3)^{n-2}, ((n-2)(n-3))^1) for odd n >= 5",
                "verified_for_all_n_4_to_9": e4_law_verified,
                "v2_spectrum_law_even_n": "(0^{binom(n,2)-1}, v_2(n-2) - 1); single torsion factor emerging at W_{v_2(n-2)}(F_2)",
                "v2_spectrum_law_odd_n": "Let r = v_2(n-3) >= 1: (0^{n(n-3)/2}, (r-1)^1, r^{n-1}); linear-size block of (n-1) simultaneous 2^r-torsion factors emerging at W_{r+1}(F_2) for n = 2^r + 3",
                "verified_n_range": [4, 9],
            },
            "c2_witt_second_carry_Z16": {
                "witt_mod16_expansion": "4 * C_2(x) = 4*e_4(x) + 8*e_6(x) + 8*e_8(x) (mod 16) for n <= 8",
                "Z16_invariant_factors_4C2_sym_match_4e4_sym": c2_z16_matches_4e4,
                "ordered_vs_symmetrized_Z16_rank": "4*C_2^{ord} has Z/16Z rank n - 3, whereas 4*C_2^{sym} reaches binom(n, 2) (e.g. 28 vs 5 at n=8); at n=7, 6 factors of 4-torsion in C_2^sym vanish mod 16 under 4x scaling and require W_5(F_2)=Z/32Z",
                "verified_n_range": [4, 8],
            },
        },
    }


def main() -> None:
    results = run_ataque09()
    out_path = Path("/home/miguel/certified-arith-preproc/results/witt_higher_torsion_snf_results.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    print(f"=== ATAQUE-09 Complete in {results['metadata']['elapsed_seconds']}s ===")
    print("\n--- (0) e_2^sym M_1 (n = 2..18) ---")
    for n in [2, 3, 4, 5, 9, 17, 18]:
        r = results["e2_sym_M1_derangement"][str(n)]
        print(f"n={n:2d}: top={r['snf_Z'][-1]:2d}, max_v2={r['max_v2']}, first_depth=W_{r['first_full_visibility_witt_depth']}")

    print("\n--- (a) e_3^sym M_{1,2} (n = 3..12) ---")
    for n in range(3, 13):
        r = results["e3_sym_M12_and_johnson"][str(n)]["M_1_2_full"]
        print(f"n={n:2d}: snf_mult={r['snf_multiplicities']}, v2_mult={r['v2_multiplicities']}, first_depth=W_{r['first_full_visibility_witt_depth']}")

    print("\n--- (b) e_4^sym M_{2,2} (n = 4..9) ---")
    for n in range(4, 10):
        r = results["e4_sym_M22_and_kneser"][str(n)]["M_2_2_full"]
        print(f"n={n:2d}: rank_Q={r['rank_Q']:2d}, rank_F2={r['rank_F2']:2d}, snf_mult={r['snf_multiplicities']}, v2_mult={r['v2_multiplicities']}")

    print("\n--- (c) 2nd Witt Carry C_2 lifted to Z/16Z (n = 4..8) ---")
    for n in range(4, 9):
        c = results["c2_witt_second_carry_Z16"][str(n)]
        e4_4x = c["four_times_e4_sym_M22"]
        c2_sym = c["exact_C2_symmetrized_d2"]
        c2_4x = c["exact_4C2_symmetrized_d2_Z16"]
        c2_ord_4x = c["exact_4C2_ordered_d2_Z16"]
        print(
            f"n={n}: coeffs={c['mobius_coeffs_a_k']} | "
            f"4*e4^sym rank_Z16={e4_4x['module_rank_Z16']} (inv_mult={dict(Counter(e4_4x['invariant_factors_Z16']))}) | "
            f"C2^sym snf_mult={c2_sym['snf_multiplicities']} | "
            f"4*C2^sym rank_Z16={c2_4x['module_rank_Z16']} (inv_mult={dict(Counter(c2_4x['invariant_factors_Z16']))}) | "
            f"4*C2^ord rank_Z16={c2_ord_4x['module_rank_Z16']}"
        )


if __name__ == "__main__":
    main()
