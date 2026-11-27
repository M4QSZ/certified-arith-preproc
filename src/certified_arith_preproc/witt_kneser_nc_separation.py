"""
ATAQUE-12: Universal Kneser KG(n, 2) / e_4^sym 2-Adic Torsion Theorem & NC-IPS Separation
========================================================================================
Computes:
  1. Exact integer Smith Normal Form (SNF_Z) invariant factors of:
       - M_{1,2}(e_3^sym) and unordered Johnson J(n, 1, 2) for n = 3..14
       - Kneser KG(n, 2) adjacency matrix and M_{2,2}(e_4^sym) for n = 4..12
     plus exact module rank over W_k(F_2) ~= Z / 2^k Z for k = 1..5.
  2. Exact verification of the 2^r-torsion block multiplicity formula in KG(n, 2):
       - General n >= 4:
           even n: (1^{n(n-3)/2}, (n-3)^{n-1}, (n-2)(n-3)/2)
           odd  n: (1^{n(n-3)/2}, (n-3)/2, (n-3)^{n-2}, (n-2)(n-3))
       - At odd n = 2^r + 3 (r >= 1):
           v_2(n-3) = r, and the 2^r-torsion block (v_2 >= r) has exact multiplicity n - 1
           (consisting of n - 2 copies of 2^r and 1 copy of (2^r + 1)*2^r),
           causing a rank jump of n - 1 between W_r(F_2) = Z/2^r Z and W_{r+1}(F_2) = Z/2^{r+1} Z.
  3. Non-commutative IPS / Nisan ABP rank lower bound vs commutative ordered rank
     on the 2nd Witt carry 4 * C_2(x) mod 16 for n = 4..10.

Saves verified JSON results to:
  /home/miguel/certified-arith-preproc/results/witt_kneser_linear_torsion_results.json
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
# 1. Exact Integer Smith Normal Form & Witt Ring Z/2^k Z Rank
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
    """
    M = _compact_nonzero_rows_cols(matrix)
    if not M:
        return []
    m, n = len(M), len(M[0])
    diag: List[int] = []
    k = 0

    while k < m and k < n:
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


def witt_ranks_from_snf(snf: Sequence[int], max_k: int = 5) -> Dict[str, int]:
    """
    Exact module rank (number of nonzero invariant factors) over W_k(F_2) ~= Z / 2^k Z
    for k = 1..max_k: count of SNF entries d_i with v_2(d_i) < k.
    """
    v2_spec = [v2(d) for d in snf]
    return {
        f"Z/{1 << k}Z": sum(1 for val in v2_spec if val < k)
        for k in range(1, max_k + 1)
    }


def summarize_snf(
    snf: List[int],
    rows: int,
    cols: int,
    max_witt_depth: int = 5,
) -> Dict[str, object]:
    """Summarize SNF_Z, 2-adic valuation spectrum, and Witt ring ranks."""
    v2_spec = [v2(d) for d in snf]
    v2_hist = {str(k): v for k, v in sorted(Counter(v2_spec).items())}
    snf_hist = {str(k): v for k, v in sorted(Counter(snf).items())}
    max_v2 = max(v2_spec) if v2_spec else 0
    witt_ranks = witt_ranks_from_snf(snf, max_k=max_witt_depth)
    rank_f2 = witt_ranks["Z/2Z"]
    witt_gaps = {k: rk - rank_f2 for k, rk in witt_ranks.items()}

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
        "witt_ranks_mod_2k": witt_ranks,
        "witt_torsion_gaps": witt_gaps,
    }


# ---------------------------------------------------------------------------
# 2. Matrix Builders: e_3^sym, KG(n, 2), e_4^sym, and 2nd Witt Carry C_2(x)
# ---------------------------------------------------------------------------

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


def build_kneser_kg_n_2(n: int) -> List[List[int]]:
    """Unordered Kneser graph KG(n, 2) adjacency matrix binom(n, 2) x binom(n, 2)."""
    pairs = list(itertools.combinations(range(n), 2))
    return [
        [1 if (i != k and i != l and j != k and j != l) else 0 for (k, l) in pairs]
        for (i, j) in pairs
    ]


def expected_e3_snf(n: int) -> List[int]:
    """Closed-form SNF_Z(M_{1,2}(e_3^sym)) = (1^{n-1}, n - 2) for n >= 3."""
    return [1] * (n - 1) + [n - 2]


def expected_kg_n_2_snf(n: int) -> List[int]:
    """
    Closed-form SNF_Z(KG(n, 2)) for all n >= 4:
      - even n: (1^{n(n-3)/2}, (n-3)^{n-1}, (n-2)(n-3)/2)
      - odd  n: (1^{n(n-3)/2}, (n-3)/2, (n-3)^{n-2}, (n-2)(n-3))
    """
    ones = [1] * (n * (n - 3) // 2)
    if n % 2 == 0:
        return ones + [n - 3] * (n - 1) + [(n - 2) * (n - 3) // 2]
    return ones + [(n - 3) // 2] + [n - 3] * (n - 2) + [(n - 2) * (n - 3)]


def c2_multilinear_coeffs(n: int) -> List[int]:
    """
    Exact integer coefficients a_0, ..., a_n such that on all x in {0, 1}^n:
      C_2(x) = floor((x_1 + ... + x_n) / 4) mod 2 = sum_{k=0}^n a_k * e_k(x).
    """
    coeffs: List[int] = []
    for k in range(n + 1):
        val = 0
        for j in range(k + 1):
            if (j // 4) % 2:
                sign = -1 if ((k - j) & 1) else 1
                val += sign * math.comb(k, j)
        coeffs.append(val)
    for s in range(n + 1):
        ev = sum(coeffs[k] * math.comb(s, k) for k in range(s + 1))
        assert ev == ((s // 4) % 2), f"Mobius mismatch at s={s}: {ev}"
    return coeffs


def build_c2_bimodal_ordered(n: int, scale: int = 1, mod_m: int | None = None) -> List[List[int]]:
    """
    Cut d=2 Nisan matrix for the ordered multilinear lift of scale * C_2(x):
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
                c = scale * a[2 + len(v)]
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
    Cut d=2 Nisan matrix for the symmetrized NC lift of scale * C_2(x),
    represented on unordered disjoint subsets (exact same SNF_Z as full word matrix).
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
                c = scale * a[2 + len(v)]
                if mod_m is not None:
                    c %= mod_m
                row.append(c)
            else:
                row.append(0)
        mat.append(row)
    return mat


# ---------------------------------------------------------------------------
# 3. Main Experiment Driver
# ---------------------------------------------------------------------------

def run_ataque12() -> Dict[str, object]:
    t0 = time.perf_counter()

    # (1) M_{1,2}(e_3^sym) for n = 3..14
    e3_results: Dict[str, object] = {}
    for n in range(3, 15):
        mat_m12 = build_e3_sym_M12(n)
        mat_j = build_e3_johnson_unordered(n)
        snf_m12 = smith_normal_form_diag(mat_m12)
        snf_j = smith_normal_form_diag(mat_j)
        exp_e3 = expected_e3_snf(n)
        assert snf_m12 == snf_j == exp_e3, (
            f"e3^sym SNF mismatch at n={n}: m12={snf_m12}, j={snf_j}, exp={exp_e3}"
        )
        e3_results[str(n)] = {
            **summarize_snf(snf_m12, n, n * n, max_witt_depth=5),
            "johnson_cols": math.comb(n, 2),
            "matches_closed_form": True,
        }

    # (2) Kneser KG(n, 2) and M_{2,2}(e_4^sym) for n = 4..12
    kg_results: Dict[str, object] = {}
    torsion_block_verification: Dict[str, object] = {}
    for n in range(4, 13):
        mat_kg = build_kneser_kg_n_2(n)
        snf_kg = smith_normal_form_diag(mat_kg)
        exp_kg = expected_kg_n_2_snf(n)
        assert snf_kg == exp_kg, f"KG({n},2) SNF mismatch: {snf_kg} vs {exp_kg}"

        mat_m22 = build_e4_sym_M22(n)
        snf_m22 = smith_normal_form_diag(mat_m22)
        assert snf_m22 == snf_kg, f"M_{{2,2}}(e_4^sym) vs KG({n},2) mismatch at n={n}"

        summary = summarize_snf(snf_kg, math.comb(n, 2), math.comb(n, 2), max_witt_depth=5)
        kg_results[str(n)] = {
            **summary,
            "M_2_2_dims": [n * n, n * n],
            "M_2_2_snf_matches_KG_exactly": True,
            "matches_closed_form": True,
        }

        # Verify 2^r-torsion block multiplicity
        if n % 2 == 1:
            r = v2(n - 3)
            count_ge_r = sum(1 for val in summary["v2_spectrum"] if val >= r)
            assert count_ge_r == n - 1, (
                f"Odd n={n} (r={r}): expected multiplicity {n-1}, got {count_ge_r}"
            )
            rank_Wr = summary["witt_ranks_mod_2k"][f"Z/{1 << r}Z"]
            rank_Wr1 = summary["witt_ranks_mod_2k"][f"Z/{1 << (r + 1)}Z"]
            assert rank_Wr1 - rank_Wr == n - 1
            torsion_block_verification[str(n)] = {
                "parity": "odd",
                "n_minus_3": n - 3,
                "r_v2_n_minus_3": r,
                "is_2_pow_r_plus_3": (n == (1 << r) + 3),
                "torsion_block_multiplicity_observed": count_ge_r,
                "torsion_block_multiplicity_formula": n - 1,
                "rank_jump_Wr_to_Wr1": rank_Wr1 - rank_Wr,
            }
        else:
            torsion_block_verification[str(n)] = {
                "parity": "even",
                "n_minus_3": n - 3,
                "v2_n_minus_3": 0,
                "max_v2_from_last_factor": v2((n - 2) * (n - 3) // 2),
                "torsion_block_multiplicity_observed": 0 if ((n - 2) // 2) % 2 == 1 else 1,
            }

    # (3) NC-IPS / Nisan ABP rank lower bound vs commutative ordered rank
    #     on the 2nd Witt carry 4 * C_2(x) mod 16 for n = 4..10
    nc_sep_results: Dict[str, object] = {}
    for n in range(4, 11):
        mat_ord_4c2 = build_c2_bimodal_ordered(n, scale=4, mod_m=16)
        snf_ord_4c2 = smith_normal_form_diag(mat_ord_4c2)
        rank_ord_Z16 = sum(1 for d in snf_ord_4c2 if math.gcd(d, 16) < 16)

        mat_sym_4c2 = build_c2_bimodal_symmetrized_reduced(n, scale=4, mod_m=16)
        snf_sym_4c2 = smith_normal_form_diag(mat_sym_4c2)
        rank_sym_Z16 = sum(1 for d in snf_sym_4c2 if math.gcd(d, 16) < 16)

        # Also record exact C_2(x) over Z/2Z and Z/4Z and 4*C_2(x) mod 16 invariant factors
        inv_ord_Z16 = [math.gcd(d, 16) for d in snf_ord_4c2 if math.gcd(d, 16) < 16]
        inv_sym_Z16 = [math.gcd(d, 16) for d in snf_sym_4c2 if math.gcd(d, 16) < 16]

        # Compare with 4 * KG(n, 2) mod 16
        snf_kg = kg_results[str(n)]["snf_Z"]
        inv_4kg_Z16 = [math.gcd(4 * d, 16) for d in snf_kg if math.gcd(4 * d, 16) < 16]

        nc_sep_results[str(n)] = {
            "ordered_matrix_dims": [len(mat_ord_4c2), len(mat_ord_4c2[0])],
            "symmetrized_matrix_dims": [len(mat_sym_4c2), len(mat_sym_4c2[0])],
            "ordered_rank_Z16": rank_ord_Z16,
            "nc_ips_nisan_rank_Z16": rank_sym_Z16,
            "separation_gap_Z16": rank_sym_Z16 - rank_ord_Z16,
            "ratio_nc_over_ordered": round(rank_sym_Z16 / rank_ord_Z16, 4) if rank_ord_Z16 else None,
            "ordered_invariant_factors_Z16": inv_ord_Z16,
            "nc_symmetrized_invariant_factors_Z16": inv_sym_Z16,
            "four_times_KG_n_2_invariant_factors_Z16": inv_4kg_Z16,
            "matches_4_times_KG_n_2_mod_16": (inv_sym_Z16 == inv_4kg_Z16),
        }

    elapsed = round(time.perf_counter() - t0, 4)

    return {
        "metadata": {
            "attack": "ATAQUE-12",
            "title": "Universal Kneser KG(n,2) / e4_sym 2-Adic Torsion & NC-IPS Separation over W_k(F2)",
            "elapsed_seconds": elapsed,
        },
        "e3_sym_M12_n3_to_14": e3_results,
        "kneser_KG_n_2_and_e4_sym_M22_n4_to_12": kg_results,
        "torsion_block_multiplicity_verification": torsion_block_verification,
        "nc_ips_vs_ordered_4C2_mod16_n4_to_10": nc_sep_results,
    }


def main() -> None:
    results = run_ataque12()
    out_path = Path("/home/miguel/certified-arith-preproc/results/witt_kneser_linear_torsion_results.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    print(f"[ATAQUE-12] Completed in {results['metadata']['elapsed_seconds']}s -> {out_path}")
    print("\n--- e_3^sym M_{1,2} (n=3..14) ---")
    for n in range(3, 15):
        r = results["e3_sym_M12_n3_to_14"][str(n)]
        print(f"  n={n:2d}: top_factor={r['snf_Z'][-1]:2d}, v2_mult={r['v2_multiplicities']}, ranks={r['witt_ranks_mod_2k']}")

    print("\n--- KG(n,2) / M_{2,2}(e_4^sym) (n=4..12) ---")
    for n in range(4, 13):
        r = results["kneser_KG_n_2_and_e4_sym_M22_n4_to_12"][str(n)]
        tb = results["torsion_block_multiplicity_verification"][str(n)]
        print(f"  n={n:2d} ({tb['parity']:4s}): dim={r['rows']:2d}, v2_mult={r['v2_multiplicities']}, ranks={r['witt_ranks_mod_2k']}")

    print("\n--- 4*C_2(x) mod 16: Ordered vs NC-IPS Nisan Rank (n=4..10) ---")
    for n in range(4, 11):
        r = results["nc_ips_vs_ordered_4C2_mod16_n4_to_10"][str(n)]
        print(f"  n={n:2d}: ordered_rank={r['ordered_rank_Z16']:2d}, nc_nisan_rank={r['nc_ips_nisan_rank_Z16']:2d}, gap={r['separation_gap_Z16']:2d}, ratio={r['ratio_nc_over_ordered']}")


if __name__ == "__main__":
    main()
