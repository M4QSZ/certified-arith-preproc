"""Protocolo XXI (ATAQUE-03): Schoenebeck Random 3-SAT Adelic Scaling RM(2, 3) (+) CG-Witt.

Benchmarks 0-branch refutation rates and wall-clock runtimes across n in [64, 75, 90, 105, 120]
at clause density alpha = 6.2 (8 deterministic verified-UNSAT seeds per n), comparing:
  1) Algebra-only: pure RM(2, 3) / width-3 diamond collisions + 4-var petals + sparse Macaulay
  2) CG-LP-only: pure Chvatal-Gomory / Witt modular & guarded cutting-planes LP
  3) Adelic RM(2, 3) (+) CG-Witt: coupled 0-branch cascade
  4) CDCL baselines: Kissat 4.0.4, CryptoMiniSat 5 (if available), and CaDiCaL 1.9.5

Also emits and verifies with `veripb --cnf` concrete VeriPB 3.0 `.pbp` proofs for random 3-SAT
instances solved purely by the 0-branch Adelic RM(2, 3) (+) CG-Witt cascade.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import itertools
import json
import math
import shutil
import subprocess
import tempfile
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np
from pysat.solvers import Cadical195
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from .benchmark_solvers import run_cryptominisat_wallclock, run_kissat_wallclock
from .cnf_utils import (
    apply_fixed_and_equivs_to_clauses,
    propagate_bcp_2clause_and_2xor,
    write_dimacs,
)
from .macaulay_cp import (
    diamond_petal_sparse_macaulay,
    extract_local_vanishing_ideal,
    extract_modular_hyperplanes,
    fast_unroll_11_chains,
    guarded_cutting_planes_lp,
    mul_var_poly,
    rref_mod_p,
    solve_hybrid_preproc,
    sparse_gf2_rref_deg_lex,
)
from .veripb_emitter import VeriPBLogger, lit_str
from .veripb_veronese_prg import (
    _emit_red_constraint,
    _try_certify_guarded_veronese_rm2,
)

SCHOENEBECK_NS = [64, 75, 90, 105, 120]
ALPHA = 6.2
SEEDS_PER_N = 8
BASE_SEED = 2026112600


def generate_verified_unsat_3sat(n_vars: int, seed: int, alpha: float = ALPHA) -> tuple[int, list[list[int]], int]:
    """Deterministically sample random 3-SAT at density `alpha` until CaDiCaL195 certifies UNSAT."""
    m_clauses = int(round(alpha * n_vars))
    rng = np.random.default_rng(seed)
    vars_pool = np.arange(1, n_vars + 1)
    attempts = 0
    while True:
        attempts += 1
        clauses = [
            [
                int(v * s)
                for v, s in zip(
                    rng.choice(vars_pool, size=3, replace=False),
                    rng.choice([-1, 1], size=3),
                )
            ]
            for _ in range(m_clauses)
        ]
        with Cadical195(bootstrap_with=clauses) as solver:
            if not solver.solve():
                return m_clauses, clauses, attempts


def run_cadical_wallclock(clauses: list[list[int]]) -> tuple[str, float]:
    t0 = time.perf_counter()
    with Cadical195(bootstrap_with=clauses) as solver:
        sat = solver.solve()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    return ("SAT" if sat else "UNSAT"), round(dt_ms, 2)


def _eval_single_instance(task: tuple[int, int, int, str, float]) -> dict[str, Any]:
    n_vars, idx, seed, kissat_bin, timeout_s = task
    m_clauses, clauses, attempts = generate_verified_unsat_3sat(n_vars, seed, ALPHA)

    # 1) Algebra-only: RM(2,3) / width-3 diamond collisions + 4-var petals + sparse Macaulay
    t0 = time.perf_counter()
    st_alg, _ = diamond_petal_sparse_macaulay(
        clauses, {}, {}, max_deg=3, max_diamond_3cls=2400, max_mac_vars=160
    )
    ms_alg = (time.perf_counter() - t0) * 1000.0
    alg_unsat = st_alg != "OK"

    # 2) CG-LP-only: pure Chvatal-Gomory / Witt LP cuts
    t0 = time.perf_counter()
    st_lp, _, _, _ = guarded_cutting_planes_lp(n_vars, clauses, max_rounds=5)
    ms_lp = (time.perf_counter() - t0) * 1000.0
    lp_unsat = st_lp != "FEASIBLE"

    # 3) Adelic RM(2,3) (+) CG-Witt: coupled 0-branch cascade
    t0 = time.perf_counter()
    st_ad, lvl_ad, _ = solve_hybrid_preproc(
        n_vars, clauses, max_rm_deg=2, max_mac_deg=3, allow_lift1=False
    )
    ms_ad = (time.perf_counter() - t0) * 1000.0
    ad_unsat = not st_ad.startswith("FEASIBLE")

    # 4) CDCL baselines (Kissat 4.0.4, CryptoMiniSat 5, CaDiCaL 1.9.5)
    with tempfile.TemporaryDirectory() as tmpdir:
        cnf_path = Path(tmpdir) / f"schoenebeck_n{n_vars}_s{idx}.cnf"
        write_dimacs(cnf_path, n_vars, clauses)
        kissat_res, kissat_ms = run_kissat_wallclock(kissat_bin, cnf_path, timeout_s)
        cms_res, cms_ms = run_cryptominisat_wallclock(cnf_path, timeout_s)
    cadical_res, cadical_ms = run_cadical_wallclock(clauses)

    return {
        "n": n_vars,
        "m": m_clauses,
        "seed_idx": idx,
        "seed": seed,
        "sampling_attempts": attempts,
        "algebra_only": {"unsat": alg_unsat, "status": st_alg, "ms": round(ms_alg, 2)},
        "cg_lp_only": {"unsat": lp_unsat, "status": st_lp, "ms": round(ms_lp, 2)},
        "adelic_coupled": {"unsat": ad_unsat, "status": st_ad, "level": lvl_ad, "ms": round(ms_ad, 2)},
        "kissat": {"result": kissat_res, "ms": kissat_ms},
        "cryptominisat5": {"result": cms_res, "ms": cms_ms},
        "cadical195": {"result": cadical_res, "ms": cadical_ms},
    }


# ---------------------------------------------------------------------------
# VeriPB 3.0 Proof Emitter for 0-Branch Adelic RM(2,3) (+) CG-Witt Cascade
# ---------------------------------------------------------------------------

def _clause_key(cl: list[int]) -> tuple[int, ...]:
    return tuple(sorted(cl, key=lambda z: (abs(z), z)))


def _derive_3clause_row_via_local_lp(
    l1: int,
    l2: int,
    l3: int,
    cl_cid: int,
    target_terms: dict[int, float],
    get_pair_witness_fn,
    logger: VeriPBLogger,
) -> int:
    """Derive a 3-clause LP inequality `sum coeff * x >= rhs` from `cl_cid` and McCormick `red` constraints."""
    vs = sorted({abs(l1), abs(l2), abs(l3)})
    pairs = [(vs[0], vs[1]), (vs[0], vs[2]), (vs[1], vs[2])]
    col_of_var = {v: i for i, v in enumerate(vs)}
    col_of_pair = {pr: 3 + i for i, pr in enumerate(pairs)}

    local_rows: list[tuple[dict[int, int], int, int]] = []
    cl_d: dict[int, int] = {}
    cl_r = 1
    for l in (l1, l2, l3):
        c_idx = col_of_var[abs(l)]
        if l > 0:
            cl_d[c_idx] = 1
        else:
            cl_d[c_idx] = -1
            cl_r -= 1
    local_rows.append((cl_d, cl_r, cl_cid))

    for i, j in pairs:
        _, and_11, and_0x, and_x0 = get_pair_witness_fn(i, j)
        ci, cj, cp = col_of_var[i], col_of_var[j], col_of_pair[(i, j)]
        local_rows.append(({ci: 1, cp: -1}, 0, and_0x))
        local_rows.append(({cj: 1, cp: -1}, 0, and_x0))
        local_rows.append(({ci: -1, cj: -1, cp: 1}, -1, and_11))

    n_loc = 6
    A_ub = np.zeros((len(local_rows), n_loc), dtype=np.float64)
    b_ub = np.zeros(len(local_rows), dtype=np.float64)
    for r_i, (d, r_val, _) in enumerate(local_rows):
        for c_i, val in d.items():
            A_ub[r_i, c_i] = -float(val)
        b_ub[r_i] = -float(r_val)

    c_obj = np.zeros(n_loc, dtype=np.float64)
    for c_i, val in target_terms.items():
        c_obj[c_i] = float(val)

    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=[(0.0, 1.0)] * n_loc, method="highs")
    assert res.success, "Local 3-clause LP failed"
    lam = np.maximum(0.0, -res.ineqlin.marginals)
    D = 12
    mults = [int(round(float(x) * D)) for x in lam]
    rpn: list[int | str] = []
    first = True
    acc = np.zeros(n_loc, dtype=np.int64)
    for m_i, (d, _, pb_cid) in zip(mults, local_rows):
        if m_i <= 0:
            continue
        if first:
            rpn.append(pb_cid)
            if m_i != 1:
                rpn.extend([m_i, "*"])
            first = False
        else:
            rpn.append(pb_cid)
            if m_i != 1:
                rpn.extend([m_i, "*"])
            rpn.append("+")
        for c_i, val in d.items():
            acc[c_i] += m_i * val

    all_vars = vs + [get_pair_witness_fn(i, j)[0] for i, j in pairs]
    for c_i, v_id in enumerate(all_vars):
        want = int(round(D * target_terms.get(c_i, 0.0)))
        diff = want - int(acc[c_i])
        if diff > 0:
            rpn.extend([f"x{v_id}", diff, "*", "+"] if diff != 1 else [f"x{v_id}", "+"])
        elif diff < 0:
            rpn.extend([f"~x{v_id}", -diff, "*", "+"] if -diff != 1 else [f"~x{v_id}", "+"])
    if D > 1:
        rpn.extend([D, "d"])
    return logger.emit_pol(rpn)


def _certify_cg_lp_and_emit(
    n_vars: int,
    clauses_with_cids: list[tuple[list[int], int]],
    fixed: dict[int, int],
    fixed_cids: dict[int, int],
    equiv: dict[int, tuple[int, int]],
    logger: VeriPBLogger,
    alloc_var_fn,
    pair_witness: dict[tuple[int, int], tuple[int, int, int, int]],
) -> tuple[str, dict[int, int], dict[int, tuple[int, int]], list[list[int]], dict[tuple[int, ...], int]]:
    """Run guarded CG-Witt LP and certify every derived unit / 2-XOR / 2-clause in VeriPB 3.0."""
    new_fixed: dict[int, int] = {}
    new_equiv: dict[int, tuple[int, int]] = {}
    new_2cls: list[list[int]] = []
    new_cids: dict[tuple[int, ...], int] = {}

    def get_pair_witness(i: int, j: int) -> tuple[int, int, int, int]:
        if i > j:
            i, j = j, i
        if (i, j) not in pair_witness:
            p_var = alloc_var_fn()
            and_11 = _emit_red_constraint([(1, -i), (1, -j), (1, p_var)], 1, p_var, 1, logger)
            and_0x = _emit_red_constraint([(1, i), (1, -p_var)], 1, p_var, 0, logger)
            and_x0 = _emit_red_constraint([(1, j), (1, -p_var)], 1, p_var, 0, logger)
            pair_witness[(i, j)] = (p_var, and_11, and_0x, and_x0)
        return pair_witness[(i, j)]

    pair_idx: dict[tuple[int, int], int] = {}

    def get_pair_col(i: int, j: int) -> int:
        if i > j:
            i, j = j, i
        if (i, j) not in pair_idx:
            pair_idx[(i, j)] = n_vars + len(pair_idx)
        return pair_idx[(i, j)]

    work = [c for c, _ in clauses_with_cids]
    for cl in work:
        if len(cl) == 3:
            vs = [abs(x) for x in cl]
            for a in range(3):
                for b in range(a + 1, 3):
                    get_pair_col(vs[a], vs[b])

    total_cols = n_vars + len(pair_idx)
    rows_dict: list[dict[int, float]] = []
    rhs_list: list[float] = []
    row_builders: list[Any] = []

    def add_le(terms: dict[int, float], rhs_val: float, builder) -> None:
        rows_dict.append(terms)
        rhs_list.append(float(rhs_val))
        row_builders.append(builder)

    bounds = [(0.0, 1.0)] * total_cols
    for v, val in fixed.items():
        if 1 <= v <= n_vars:
            bounds[v - 1] = (float(val), float(val))

    for (i, j), pij in pair_idx.items():
        xi, xj = i - 1, j - 1
        add_le({pij: 1.0, xi: -1.0}, 0.0, lambda i=i, j=j: get_pair_witness(i, j)[2])
        add_le({pij: 1.0, xj: -1.0}, 0.0, lambda i=i, j=j: get_pair_witness(i, j)[3])
        add_le({xi: 1.0, xj: 1.0, pij: -1.0}, 1.0, lambda i=i, j=j: get_pair_witness(i, j)[1])

    def u_expr(lit: int) -> tuple[float, dict[int, float]]:
        v = abs(lit) - 1
        return (1.0, {v: -1.0}) if lit > 0 else (0.0, {v: 1.0})

    def c_expr(l1: int, l2: int) -> tuple[float, dict[int, float]]:
        v1, v2 = abs(l1) - 1, abs(l2) - 1
        p12 = get_pair_col(abs(l1), abs(l2))
        if l1 < 0 and l2 < 0:
            return 0.0, {p12: 1.0}
        if l1 < 0 and l2 > 0:
            return 0.0, {v1: 1.0, p12: -1.0}
        if l1 > 0 and l2 < 0:
            return 0.0, {v2: 1.0, p12: -1.0}
        return 1.0, {v1: -1.0, v2: -1.0, p12: 1.0}

    def derive_c_le_zero(l1: int, l2: int, cl_cid: int) -> int:
        p_var, and_11, and_0x, and_x0 = get_pair_witness(abs(l1), abs(l2))
        i, j = abs(l1), abs(l2)
        if i > j:
            l1, l2 = l2, l1
        if l1 < 0 and l2 < 0:
            return logger.emit_pol([cl_cid, and_0x, "+", and_x0, "+", 2, "d"])
        if l1 < 0 and l2 > 0:
            return logger.emit_pol([cl_cid, and_11, "+", f"x{p_var}", "+", 2, "d"])
        if l1 > 0 and l2 < 0:
            return logger.emit_pol([cl_cid, and_11, "+", f"x{p_var}", "+", 2, "d"])
        return logger.emit_pol([cl_cid, and_0x, "+", and_x0, "+", 2, "d"])

    deg_cnt: dict[int, int] = defaultdict(int)
    pair_activity: dict[tuple[int, int], int] = defaultdict(int)
    for cl, cl_cid in clauses_with_cids:
        for lit in cl:
            deg_cnt[abs(lit)] += 1
        if len(cl) == 2:
            cu1, du1 = u_expr(cl[0])
            cu2, du2 = u_expr(cl[1])
            t2c: dict[int, float] = defaultdict(float)
            for k, vc in du1.items():
                t2c[k] += vc
            for k, vc in du2.items():
                t2c[k] += vc
            add_le(t2c, 1.0 - (cu1 + cu2), lambda cid=cl_cid: cid)
            a_lo, b_hi = sorted((abs(cl[0]), abs(cl[1])))
            if (a_lo, b_hi) in pair_idx:
                cc, dc = c_expr(cl[0], cl[1])
                add_le(dc, -cc, lambda l1=cl[0], l2=cl[1], cid=cl_cid: derive_c_le_zero(l1, l2, cid))
        elif len(cl) == 3:
            l1, l2, l3 = cl
            for pa, pb in ((l1, l2), (l1, l3), (l2, l3)):
                pair_activity[tuple(sorted((pa, pb), key=lambda z: (abs(z), z)))] += 1
            vs3 = sorted({abs(l1), abs(l2), abs(l3)})
            pairs3 = [(vs3[0], vs3[1]), (vs3[0], vs3[2]), (vs3[1], vs3[2])]
            g_to_loc = {v - 1: idx for idx, v in enumerate(vs3)}
            for idx_p, pr in enumerate(pairs3):
                g_to_loc[get_pair_col(pr[0], pr[1])] = 3 + idx_p

            u_list = [u_expr(l1), u_expr(l2), u_expr(l3)]
            c12, c13, c23 = c_expr(l1, l2), c_expr(l1, l3), c_expr(l2, l3)

            c0 = sum(u[0] for u in u_list) - (c12[0] + c13[0] + c23[0])
            t0: dict[int, float] = defaultdict(float)
            for _, d in u_list:
                for k, val_c in d.items():
                    t0[k] += val_c
            for _, d in (c12, c13, c23):
                for k, val_c in d.items():
                    t0[k] -= val_c
            loc_t0 = {g_to_loc[k]: -v for k, v in t0.items() if abs(v) > 1e-12}
            add_le(
                t0,
                1.0 - c0,
                lambda l1=l1, l2=l2, l3=l3, cid=cl_cid, lt=loc_t0: _derive_3clause_row_via_local_lp(
                    l1, l2, l3, cid, lt, get_pair_witness, logger
                ),
            )

            c2 = -sum(u[0] for u in u_list) + 2.0 * (c12[0] + c13[0] + c23[0])
            t2: dict[int, float] = defaultdict(float)
            for _, d in u_list:
                for k, val_c in d.items():
                    t2[k] -= val_c
            for _, d in (c12, c13, c23):
                for k, val_c in d.items():
                    t2[k] += 2.0 * val_c
            loc_t2 = {g_to_loc[k]: -v for k, v in t2.items() if abs(v) > 1e-12}
            add_le(
                t2,
                -c2,
                lambda l1=l1, l2=l2, l3=l3, cid=cl_cid, lt=loc_t2: _derive_3clause_row_via_local_lp(
                    l1, l2, l3, cid, lt, get_pair_witness, logger
                ),
            )

            for idx_u, ca, cb in [(0, c12, c13), (1, c12, c23), (2, c13, c23)]:
                cu, du = u_list[idx_u]
                cloc = ca[0] + cb[0] - cu
                tloc: dict[int, float] = defaultdict(float)
                for k, val_c in ca[1].items():
                    tloc[k] += val_c
                for k, val_c in cb[1].items():
                    tloc[k] += val_c
                for k, val_c in du.items():
                    tloc[k] -= val_c
                loc_tl = {g_to_loc[k]: -v for k, v in tloc.items() if abs(v) > 1e-12}
                add_le(
                    tloc,
                    -cloc,
                    lambda l1=l1, l2=l2, l3=l3, cid=cl_cid, lt=loc_tl: _derive_3clause_row_via_local_lp(
                        l1, l2, l3, cid, lt, get_pair_witness, logger
                    ),
                )

    A_ub = lil_matrix((len(rows_dict), total_cols), dtype=np.float64)
    for i_r, d in enumerate(rows_dict):
        for col, val_c in d.items():
            if abs(val_c) > 1e-12:
                A_ub[i_r, col] = val_c
    A_csc = A_ub.tocsc()
    b_ub = np.array(rhs_list, dtype=np.float64)

    col_to_var = {v - 1: v for v in range(1, n_vars + 1)}
    for (i, j), pij in pair_idx.items():
        col_to_var[pij] = get_pair_witness(i, j)[0]

    row_cid_cache: dict[int, int] = {}

    def get_row_cid(r_idx: int) -> int:
        if r_idx not in row_cid_cache:
            row_cid_cache[r_idx] = row_builders[r_idx]()
        return row_cid_cache[r_idx]

    def emit_farkas_cut(lp_res, target_col_coeffs: dict[int, int]) -> int:
        """Emit `pol` + `d` certifying `sum target_col_coeffs[c] * x_c >= ...` from LP duals."""
        lam = np.maximum(0.0, -lp_res.ineqlin.marginals)
        D = 120_000_000 if abs(float(lp_res.fun)) < 1e-3 else 12_000_000
        mults = [int(round(float(x) * D)) for x in lam]
        rpn: list[int | str] = []
        first = True
        acc: dict[int, int] = defaultdict(int)
        for r_i, m_i in enumerate(mults):
            if m_i <= 0:
                continue
            cid = get_row_cid(r_i)
            if first:
                rpn.append(cid)
                if m_i != 1:
                    rpn.extend([m_i, "*"])
                first = False
            else:
                rpn.append(cid)
                if m_i != 1:
                    rpn.extend([m_i, "*"])
                rpn.append("+")
            for col, val in rows_dict[r_i].items():
                acc[col] -= m_i * int(round(val))

        lo_m = np.maximum(0.0, lp_res.lower.marginals)
        hi_m = np.maximum(0.0, -lp_res.upper.marginals)
        for c_i in range(n_vars):
            v_id = c_i + 1
            if v_id in fixed_cids:
                if fixed[v_id] == 1 and lo_m[c_i] > 1e-9:
                    m_f = int(round(float(lo_m[c_i]) * D))
                    if m_f > 0:
                        fcid = fixed_cids[v_id]
                        rpn.append(fcid)
                        if m_f != 1:
                            rpn.extend([m_f, "*"])
                        if not first:
                            rpn.append("+")
                        first = False
                        acc[c_i] += m_f
                elif fixed[v_id] == 0 and hi_m[c_i] > 1e-9:
                    m_f = int(round(float(hi_m[c_i]) * D))
                    if m_f > 0:
                        fcid = fixed_cids[v_id]
                        rpn.append(fcid)
                        if m_f != 1:
                            rpn.extend([m_f, "*"])
                        if not first:
                            rpn.append("+")
                        first = False
                        acc[c_i] -= m_f

        all_cols = set(acc.keys()) | set(target_col_coeffs.keys())
        for c_i in sorted(all_cols):
            want = D * target_col_coeffs.get(c_i, 0)
            diff = want - acc.get(c_i, 0)
            v_id = col_to_var[c_i]
            if diff > 0:
                rpn.extend([f"x{v_id}", diff, "*", "+"] if diff != 1 else [f"x{v_id}", "+"])
            elif diff < 0:
                rpn.extend([f"~x{v_id}", -diff, "*", "+"] if -diff != 1 else [f"~x{v_id}", "+"])
        rpn.extend([D, "d"])
        return logger.emit_pol(rpn)

    res = linprog(np.zeros(total_cols), A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        return "UNSAT_LP", new_fixed, new_equiv, new_2cls, new_cids

    witness_xs = [res.x]
    cand_vars = [v for v, _ in sorted(deg_cnt.items(), key=lambda kv: -kv[1]) if 1 <= v <= n_vars and v not in fixed][:28]

    for v in cand_vars:
        col_v = v - 1
        if not any(wx[col_v] <= 1e-6 for wx in witness_xs):
            c_obj = np.zeros(total_cols)
            c_obj[col_v] = 1.0
            r_lo = linprog(c_obj, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
            if r_lo.success:
                if r_lo.fun > 1e-6:
                    cid_u = emit_farkas_cut(r_lo, {col_v: 1})
                    new_fixed[v] = 1
                    new_cids[(v,)] = cid_u
                    return "PROGRESSED", new_fixed, new_equiv, new_2cls, new_cids
                witness_xs.append(r_lo.x)
        if not any(wx[col_v] >= 1.0 - 1e-6 for wx in witness_xs):
            c_obj = np.zeros(total_cols)
            c_obj[col_v] = -1.0
            r_hi = linprog(c_obj, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
            if r_hi.success:
                if (-r_hi.fun) < 1.0 - 1e-6:
                    cid_u = emit_farkas_cut(r_hi, {col_v: -1})
                    new_fixed[v] = 0
                    new_cids[(-v,)] = cid_u
                    return "PROGRESSED", new_fixed, new_equiv, new_2cls, new_cids
                witness_xs.append(r_hi.x)

    top_var_pairs = sorted(pair_idx.keys(), key=lambda ij: -(deg_cnt[ij[0]] + deg_cnt[ij[1]]))
    tested_vp = 0
    for vi, vj in top_var_pairs:
        if vi in fixed or vj in fixed or vj in equiv:
            continue
        tested_vp += 1
        if tested_vp > 6:
            break
        pij = pair_idx[(vi, vj)]
        if not any((wx[vi - 1] + wx[vj - 1] - 2.0 * wx[pij]) <= 1e-5 for wx in witness_xs):
            c_xor = np.zeros(total_cols)
            c_xor[vi - 1] = 1.0
            c_xor[vj - 1] = 1.0
            c_xor[pij] = -2.0
            r_xlo = linprog(c_xor, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
            if r_xlo.success:
                if r_xlo.fun > 1e-5:
                    cid_ge1 = emit_farkas_cut(r_xlo, {vi - 1: 1, vj - 1: 1, pij: -2})
                    p_var, and_11, _, _ = get_pair_witness(vi, vj)
                    c_cl1 = logger.emit_pol([cid_ge1, f"x{p_var}", 2, "*", "+"])
                    c_cl2 = logger.emit_pol([cid_ge1, and_11, 2, "*", "+"])
                    new_equiv[vj] = (vi, 1)
                    new_2cls.extend([[-vi, -vj], [vi, vj]])
                    new_cids[_clause_key([vi, vj])] = c_cl1
                    new_cids[_clause_key([-vi, -vj])] = c_cl2
                    return "PROGRESSED", new_fixed, new_equiv, new_2cls, new_cids
                witness_xs.append(r_xlo.x)

    return "FEASIBLE", new_fixed, new_equiv, new_2cls, new_cids


def _certify_diamond_petal_sparse_macaulay(
    clauses: list[list[int]],
    fixed: dict[int, int],
    equiv: dict[int, tuple[int, int]],
    logger: VeriPBLogger,
    known_keys: dict[tuple[int, ...], int],
    clause_items: list[tuple[list[int], int]],
    max_deg: int = 3,
    max_diamond_3cls: int = 2400,
    max_mac_vars: int = 160,
) -> tuple[str, list[list[int]]]:
    """Certified mirror of `diamond_petal_sparse_macaulay` logging all intermediate
    unit, 2-clause, equivalence, and width-3 diamond derivations to `VeriPBLogger`.
    """
    def ensure_rup(cl: list[int]) -> int:
        ck = _clause_key(cl)
        if ck not in known_keys:
            cid = logger.emit_rup_clause(list(ck))
            known_keys[ck] = cid
            clause_items.append((list(ck), cid))
        return known_keys[ck]

    work = [list(c) for c in clauses]

    for mac_outer in range(4):
        for _ in range(14):
            st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
            if st == "UNSAT":
                ensure_rup([])
                return f"UNSAT_W3_BCP_M{mac_outer+1}", []
            for c in work:
                ensure_rup(c)

            chg = False
            cl_set = {_clause_key(c) for c in work}

            for c in list(work):
                if len(c) == 1:
                    v, val = abs(c[0]), (1 if c[0] > 0 else 0)
                    if v in fixed and fixed[v] != val:
                        ensure_rup([])
                        return f"UNSAT_W3_UNIT_M{mac_outer+1}", []
                    if v not in fixed:
                        fixed[v] = val
                        chg = True
                elif len(c) == 2:
                    a, b = c[0], c[1]
                    if _clause_key([-a, b]) in cl_set:
                        vb, valb = abs(b), (1 if b > 0 else 0)
                        ensure_rup([b])
                        if vb in fixed and fixed[vb] != valb:
                            ensure_rup([])
                            return f"UNSAT_W3_2UNIT_M{mac_outer+1}", []
                        if vb not in fixed:
                            fixed[vb] = valb
                            chg = True
                    if _clause_key([a, -b]) in cl_set:
                        va, vala = abs(a), (1 if a > 0 else 0)
                        ensure_rup([a])
                        if va in fixed and fixed[va] != vala:
                            ensure_rup([])
                            return f"UNSAT_W3_2UNIT_M{mac_outer+1}", []
                        if va not in fixed:
                            fixed[va] = vala
                            chg = True
                    if _clause_key([-a, -b]) in cl_set:
                        va, vb = abs(a), abs(b)
                        hi, lo = (va, vb) if va > vb else (vb, va)
                        fl = 1 if (a > 0) == (b > 0) else 0
                        if hi not in fixed and hi not in equiv:
                            equiv[hi] = (lo, fl)
                            chg = True
            if chg:
                continue

            two_cls = [c for c in work if len(c) == 2]
            three_cls = [c for c in work if len(c) == 3]
            by_lit2: dict[int, list[int]] = defaultdict(list)
            for a, b in two_cls:
                by_lit2[a].append(b)
                by_lit2[b].append(a)

            new_2 = []
            for b_piv, pos_list in list(by_lit2.items()):
                if b_piv < 0:
                    continue
                for a in pos_list:
                    for c_lit in by_lit2.get(-b_piv, ()):
                        if a == -c_lit:
                            continue
                        nc = _clause_key([a, c_lit])
                        if nc not in cl_set:
                            cl_set.add(nc)
                            new_2.append(list(nc))

            for c3 in three_cls:
                for idx_p in range(3):
                    piv = c3[idx_p]
                    o1, o2 = c3[(idx_p + 1) % 3], c3[(idx_p + 2) % 3]
                    for other in by_lit2.get(-piv, ()):
                        if other == o1 or other == o2:
                            nc = _clause_key([o1, o2])
                            if nc not in cl_set:
                                cl_set.add(nc)
                                new_2.append(list(nc))
            if new_2:
                for c in new_2:
                    ensure_rup(c)
                work.extend(new_2)
                continue

            if len(three_cls) > max_diamond_3cls:
                break

            supp_set = {tuple(sorted(abs(x) for x in c)) for c in three_cls}
            pair_index: dict[tuple[int, int], list[int]] = defaultdict(list)
            for l0, l1, l2 in three_cls:
                pair_index[(l0, l1)].append(l2)
                pair_index[(l0, l2)].append(l1)
                pair_index[(l1, l0)].append(l2)
                pair_index[(l1, l2)].append(l0)
                pair_index[(l2, l0)].append(l1)
                pair_index[(l2, l1)].append(l0)

            colliding_3 = []
            fresh_3 = []
            for (piv, sh), thirds_pos in list(pair_index.items()):
                if piv < 0:
                    continue
                thirds_neg = pair_index.get((-piv, sh), ())
                if not thirds_neg:
                    continue
                for b_lit in thirds_pos:
                    for c_lit in thirds_neg:
                        if b_lit == -c_lit or sh == -b_lit or sh == -c_lit:
                            continue
                        nc = tuple(sorted({sh, b_lit, c_lit}, key=lambda z: (abs(z), z)))
                        if nc not in cl_set:
                            if len(nc) <= 2:
                                cl_set.add(nc)
                                colliding_3.append(list(nc))
                            else:
                                sp = tuple(sorted(abs(x) for x in nc))
                                if sp in supp_set:
                                    cl_set.add(nc)
                                    colliding_3.append(list(nc))
                                elif len(three_cls) + len(fresh_3) < max_diamond_3cls:
                                    cl_set.add(nc)
                                    fresh_3.append(list(nc))

            added = colliding_3 + fresh_3
            if not added:
                break
            for c in added:
                ensure_rup(c)
            work.extend(added)

        st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
        if st == "UNSAT":
            ensure_rup([])
            return f"UNSAT_POST_W3_M{mac_outer+1}", []
        for c in work:
            ensure_rup(c)
        if not work or max_deg < 2:
            break

        unrolled = fast_unroll_11_chains(work)
        all_active = sorted({abs(l) for c in unrolled for l in c})
        if not all_active or len(all_active) > max_mac_vars:
            break

        by_supp: dict[tuple[int, ...], list[list[int]]] = defaultdict(list)
        for c in unrolled:
            if len(c) == 0:
                ensure_rup([])
                return f"UNSAT_EMPTY_M{mac_outer+1}", []
            if 2 <= len(c) <= 7:
                by_supp[tuple(sorted({abs(l) for l in c}))].append(c)

        petals_4: dict[tuple[int, ...], list[list[int]]] = {}
        triples_only = [sp for sp in by_supp.keys() if len(sp) == 3]
        if len(triples_only) <= 1800:
            by_pair_supp: dict[tuple[int, int], list[tuple[int, ...]]] = defaultdict(list)
            for sp in triples_only:
                by_pair_supp[(sp[0], sp[1])].append(sp)
                by_pair_supp[(sp[0], sp[2])].append(sp)
                by_pair_supp[(sp[1], sp[2])].append(sp)
            cand_u4 = set()
            for sp_list in by_pair_supp.values():
                if 2 <= len(sp_list) <= 12:
                    for i in range(len(sp_list)):
                        for j in range(i + 1, len(sp_list)):
                            u4 = tuple(sorted(set(sp_list[i]) | set(sp_list[j])))
                            if len(u4) == 4:
                                cand_u4.add(u4)
            for u4 in cand_u4:
                cls_u4 = []
                for r_sz in (2, 3):
                    for sub_sp in itertools.combinations(u4, r_sz):
                        if sub_sp in by_supp:
                            cls_u4.extend(by_supp[sub_sp])
                if len(cls_u4) >= 3:
                    petals_4[u4] = cls_u4

        deduced_mac = False
        for d_cur in ([2] if max_deg <= 2 else [2, 3]):
            polys = []
            quad_generators = []

            for supp, cl_list in by_supp.items():
                if len(supp) == 3 and len(cl_list) == 1:
                    if d_cur >= 3:
                        polys.extend(extract_local_vanishing_ideal(supp, cl_list, 3))
                else:
                    id2 = extract_local_vanishing_ideal(supp, cl_list, min(2, d_cur))
                    if id2 == [{()}]:
                        if len(supp) <= 4:
                            cid_u = logger.derive_clause_over_cube([], list(supp))
                            known_keys[()] = cid_u
                        return f"UNSAT_LOCAL_IDEAL_M{mac_outer+1}", []
                    polys.extend(id2)
                    quad_generators.extend(id2)
                    if d_cur >= 3 and len(supp) >= 3:
                        polys.extend(extract_local_vanishing_ideal(supp, cl_list, 3))

            for u4, cls_u4 in petals_4.items():
                id2_p = extract_local_vanishing_ideal(u4, cls_u4, 2)
                if id2_p == [{()}]:
                    cid_u = logger.derive_clause_over_cube([], list(u4))
                    known_keys[()] = cid_u
                    return f"UNSAT_PETAL4_LOCAL_M{mac_outer+1}", []
                if id2_p:
                    polys.extend(id2_p)
                    quad_generators.extend(id2_p)

            if d_cur >= 3 and quad_generators:
                seen_q = set()
                uniq_q = []
                for q in quad_generators:
                    fq = frozenset(q)
                    if fq not in seen_q:
                        seen_q.add(fq)
                        uniq_q.append(q)
                for p2 in uniq_q:
                    for v in all_active:
                        pr = mul_var_poly(v, p2)
                        if pr:
                            polys.append(pr)

            if not polys:
                continue

            st_r, nfx, neq = sparse_gf2_rref_deg_lex(polys)
            if st_r == "UNSAT":
                return f"UNSAT_SPARSE_MACAULAY_D{d_cur}_M{mac_outer+1}", []

            for v, b in nfx.items():
                if v in fixed and fixed[v] != b:
                    ensure_rup([])
                    return f"UNSAT_SMAC_UNIT_CONFLICT_M{mac_outer+1}", []
                if v not in fixed:
                    fixed[v] = b
                    ensure_rup([v if b == 1 else -v])
                    deduced_mac = True
            for u, (rv, fl) in neq.items():
                if u not in fixed and u not in equiv:
                    equiv[u] = (rv, fl)
                    if fl == 0:
                        ensure_rup([-u, rv])
                        ensure_rup([u, -rv])
                    else:
                        ensure_rup([u, rv])
                        ensure_rup([-u, -rv])
                    deduced_mac = True
            if deduced_mac:
                break

        if not deduced_mac:
            break

    st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
    if st == "UNSAT":
        ensure_rup([])
        return "UNSAT_SMAC_FINAL", []
    for c in work:
        ensure_rup(c)
    return "OK", work


def certify_adelic_schoenebeck_veripb(
    n_vars: int,
    clauses: list[list[int]],
    cnf_path: Path,
    pbp_path: Path,
) -> tuple[bool, str]:
    """Emit and verify a VeriPB 3.0 `.pbp` proof for a random 3-SAT UNSAT instance
    solved purely by the 0-branch Adelic RM(2,3) (+) CG-Witt cascade.
    """
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    pbp_path.parent.mkdir(parents=True, exist_ok=True)
    write_dimacs(cnf_path, n_vars, clauses)

    logger = VeriPBLogger(len(clauses))
    next_var = n_vars + 1

    def alloc_var() -> int:
        nonlocal next_var
        v = next_var
        next_var += 1
        return v

    known_keys: dict[tuple[int, ...], int] = {_clause_key(c): idx + 1 for idx, c in enumerate(clauses)}
    clause_items: list[tuple[list[int], int]] = [(list(c), idx + 1) for idx, c in enumerate(clauses)]
    pair_witness: dict[tuple[int, int], tuple[int, int, int, int]] = {}

    fixed: dict[int, int] = {}
    fixed_cids: dict[int, int] = {}
    equiv: dict[int, tuple[int, int]] = {}
    work_cls = [list(c) for c in clauses]

    for pp_rnd in range(1, 5):
        st_mac, work_after_mac = _certify_diamond_petal_sparse_macaulay(
            work_cls, fixed, equiv, logger, known_keys, clause_items,
            max_deg=3, max_diamond_3cls=2400, max_mac_vars=160,
        )

        if st_mac != "OK":
            if () in known_keys:
                pbp_text = logger.finish_unsat(known_keys[()])
                pbp_path.write_text(pbp_text, encoding="utf-8")
                if _verify_veripb(cnf_path, pbp_path):
                    return True, f"{st_mac}_PP{pp_rnd}_RUP"
            try:
                rup_empty = logger.emit_rup_clause([])
                pbp_text = logger.finish_unsat(rup_empty)
                pbp_path.write_text(pbp_text, encoding="utf-8")
                if _verify_veripb(cnf_path, pbp_path):
                    return True, f"{st_mac}_PP{pp_rnd}_RUP"
            except Exception:
                pass
            rm2_cid = _try_certify_guarded_veronese_rm2(
                clause_items, [], logger, alloc_var, max_block_arity=4
            )
            if rm2_cid is not None:
                pbp_text = logger.finish_unsat(rm2_cid)
                pbp_path.write_text(pbp_text, encoding="utf-8")
                if _verify_veripb(cnf_path, pbp_path):
                    return True, f"{st_mac}_PP{pp_rnd}_RM2"
            return False, f"CERT_FAILED_{st_mac}_PP{pp_rnd}"

        work_cls = work_after_mac

        cls_le2 = [c for c in work_cls if len(c) <= 2]
        cls_eq3 = [c for c in work_cls if len(c) == 3]
        cap_3lp = max(520, len(clauses))
        lp_cls = cls_le2 + cls_eq3[:cap_3lp]

        # Emit all diamond 3-clauses first, then 2-clauses (so 2-vs-3 subsumptions are RUP!)
        for c in cls_eq3:
            ck = _clause_key(c)
            if ck not in known_keys:
                cid = logger.emit_rup_clause(list(ck))
                known_keys[ck] = cid
                clause_items.append((list(ck), cid))
        for c in cls_le2:
            ck = _clause_key(c)
            if ck not in known_keys:
                cid = logger.emit_rup_clause(list(ck))
                known_keys[ck] = cid
                clause_items.append((list(ck), cid))

        lp_items: list[tuple[list[int], int]] = [(c, known_keys[_clause_key(c)]) for c in lp_cls]

        lp_progressed = False
        for _lp_r in range(3):
            st_lp, nfx, neq, n2, ncids = _certify_cg_lp_and_emit(
                n_vars, lp_items, fixed, fixed_cids, equiv, logger, alloc_var, pair_witness
            )
            for ck, cid in ncids.items():
                known_keys[ck] = cid
                clause_items.append((list(ck), cid))
            for v, val in nfx.items():
                fixed[v] = val
                fixed_cids[v] = ncids[(v,) if val == 1 else (-v,)]
                lp_progressed = True
            for u, (rv, fl) in neq.items():
                if u not in fixed and u not in equiv:
                    equiv[u] = (rv, fl)
                    lp_progressed = True
            for c2 in n2:
                work_cls.append(list(c2))
                lp_items.append((list(c2), known_keys[_clause_key(c2)]))
                lp_progressed = True

            if st_lp == "UNSAT_LP":
                rup_empty = logger.emit_rup_clause([])
                pbp_text = logger.finish_unsat(rup_empty)
                pbp_path.write_text(pbp_text, encoding="utf-8")
                if _verify_veripb(cnf_path, pbp_path):
                    return True, f"UNSAT_LP_PP{pp_rnd}"
                return False, f"CERT_FAILED_LP_PP{pp_rnd}"
            if st_lp == "FEASIBLE":
                break

        if not lp_progressed:
            break

    return False, "NOT_SOLVED_LVL0"


def _verify_veripb(cnf_path: Path, pbp_path: Path) -> bool:
    veripb_bin = shutil.which("veripb") or "/home/miguel/.local/bin/veripb"
    proc = subprocess.run(
        [veripb_bin, "--cnf", str(cnf_path), str(pbp_path)],
        capture_output=True,
        text=True,
        timeout=60,
    )
    comb = (proc.stdout + proc.stderr).lower()
    return proc.returncode == 0 and ("verified unsatisfiable" in comb or "succeeded" in comb)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Protocolo XXI (ATAQUE-03): Schoenebeck Random 3-SAT Adelic Scaling"
    )
    parser.add_argument("--ns", type=int, nargs="+", default=SCHOENEBECK_NS)
    parser.add_argument("--seeds", type=int, default=SEEDS_PER_N)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument(
        "--kissat",
        type=str,
        default="/home/miguel/.local/bin/kissat",
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default="results/protocol_xxi_schoenebeck_results.json",
    )
    parser.add_argument(
        "--pbp-dir",
        type=str,
        default="results/protocol_xxi_pbp",
    )
    args = parser.parse_args()

    tasks = []
    for n_vars in args.ns:
        for idx in range(args.seeds):
            seed = BASE_SEED + 1000 * n_vars + idx
            tasks.append((n_vars, idx, seed, args.kissat, args.timeout))

    print(
        f"Running Protocolo XXI (ATAQUE-03) on ns={args.ns}, alpha={ALPHA}, "
        f"{args.seeds} seeds/n ({len(tasks)} instances total), workers={args.workers}..."
    )
    t_start = time.perf_counter()
    raw_results: list[dict[str, Any]] = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        for res in pool.map(_eval_single_instance, tasks):
            raw_results.append(res)
            print(
                f"  [n={res['n']:3d} seed={res['seed_idx']}] "
                f"alg={int(res['algebra_only']['unsat'])} ({res['algebra_only']['ms']:6.1f}ms) | "
                f"lp={int(res['cg_lp_only']['unsat'])} ({res['cg_lp_only']['ms']:6.1f}ms) | "
                f"adelic={int(res['adelic_coupled']['unsat'])} ({res['adelic_coupled']['ms']:7.1f}ms) | "
                f"kissat={res['kissat']['ms']:5.2f}ms",
                flush=True,
            )

    summary_rows = []
    for n_vars in args.ns:
        rows_n = [r for r in raw_results if r["n"] == n_vars]
        k = len(rows_n)
        alg_cnt = sum(1 for r in rows_n if r["algebra_only"]["unsat"])
        lp_cnt = sum(1 for r in rows_n if r["cg_lp_only"]["unsat"])
        ad_cnt = sum(1 for r in rows_n if r["adelic_coupled"]["unsat"])

        cms_vals = [
            r["cryptominisat5"]["ms"]
            for r in rows_n
            if r["cryptominisat5"]["result"] in ("SAT", "UNSAT")
        ]
        summary_rows.append(
            {
                "n": n_vars,
                "m": int(round(ALPHA * n_vars)),
                "alpha": ALPHA,
                "trials": k,
                "algebra_only_unsat_count": alg_cnt,
                "algebra_only_unsat_rate": round(alg_cnt / k, 4),
                "algebra_only_mean_ms": round(float(np.mean([r["algebra_only"]["ms"] for r in rows_n])), 2),
                "cg_lp_only_unsat_count": lp_cnt,
                "cg_lp_only_unsat_rate": round(lp_cnt / k, 4),
                "cg_lp_only_mean_ms": round(float(np.mean([r["cg_lp_only"]["ms"] for r in rows_n])), 2),
                "adelic_coupled_unsat_count": ad_cnt,
                "adelic_coupled_unsat_rate": round(ad_cnt / k, 4),
                "adelic_coupled_mean_ms": round(float(np.mean([r["adelic_coupled"]["ms"] for r in rows_n])), 2),
                "kissat_4_0_4_mean_ms": round(float(np.mean([r["kissat"]["ms"] for r in rows_n])), 2),
                "cryptominisat5_mean_ms": round(float(np.mean(cms_vals)), 2) if cms_vals else "NOT_AVAILABLE",
                "cadical_195_mean_ms": round(float(np.mean([r["cadical195"]["ms"] for r in rows_n])), 2),
            }
        )

    # Emit & verify at least 2 concrete VeriPB `.pbp` proofs for instances solved by Adelic RM(2,3) (+) CG-Witt
    pbp_dir = Path(args.pbp_dir)
    pbp_dir.mkdir(parents=True, exist_ok=True)
    pbp_records = []
    solved_candidates = [r for r in raw_results if r["adelic_coupled"]["unsat"]]
    for cand in solved_candidates:
        if len(pbp_records) >= 2:
            break
        n_c = cand["n"]
        seed_c = cand["seed"]
        idx_c = cand["seed_idx"]
        _, cl_c, _ = generate_verified_unsat_3sat(n_c, seed_c, ALPHA)
        cnf_p = pbp_dir / f"schoenebeck_n{n_c}_seed{idx_c}.cnf"
        pbp_p = pbp_dir / f"schoenebeck_n{n_c}_seed{idx_c}.pbp"
        ok, reason = certify_adelic_schoenebeck_veripb(n_c, cl_c, cnf_p, pbp_p)
        print(f"  [VeriPB] n={n_c} seed={idx_c} -> verified={ok} ({reason})")
        if ok:
            pbp_records.append(
                {
                    "n": n_c,
                    "m": len(cl_c),
                    "seed_idx": idx_c,
                    "seed": seed_c,
                    "cnf_path": str(cnf_p),
                    "pbp_path": str(pbp_p),
                    "verified_veripb": True,
                    "reason": reason,
                }
            )

    out_payload = {
        "protocol": "Protocolo XXI (ATAQUE-03)",
        "description": "Schoenebeck Random 3-SAT Adelic Scaling RM(2,3) (+) CG-Witt at alpha=6.2",
        "alpha": ALPHA,
        "seeds_per_n": args.seeds,
        "total_wall_s": round(time.perf_counter() - t_start, 2),
        "summary_by_n": summary_rows,
        "veripb_proofs": pbp_records,
        "instances": raw_results,
    }
    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out_payload, indent=2), encoding="utf-8")
    print(f"\nSaved results to {out_path}")


if __name__ == "__main__":
    main()
