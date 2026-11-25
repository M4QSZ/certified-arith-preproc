"""Blind 2-input gate extraction, integer adder telescoping, and 2-adic bit-peeling from scrambled 3-CNF."""

from __future__ import annotations

import math
from collections import defaultdict
from fractions import Fraction
import numpy as np

from .cnf_utils import (
    VAR_TT_CACHE,
    apply_fixed_and_equivs_to_clauses,
    fast_unroll_11_chains,
    propagate_bcp_2clause_and_2xor,
)


def scan_deterministic_2input_gates(
    work_cls: list[list[int]],
) -> tuple[str, dict[tuple[int, int], list[tuple[int, tuple[int, ...]]]] | None, dict[int, tuple[int, int, tuple[int, ...]]] | None]:
    """
    Scan all 3-variable triples in width <= 3 clauses and return:
      - ("UNSAT", None, None) if any triple has an empty satisfying truth table, or
      - ("OK", gates_by_in, gate_of_quad_out).
    """
    two_by_pair: dict[tuple[int, int], list[list[int]]] = defaultdict(list)
    three_by_trip: dict[tuple[int, int, int], list[list[int]]] = defaultdict(list)
    for c in work_cls:
        if len(c) == 2:
            two_by_pair[tuple(sorted((abs(c[0]), abs(c[1]))))].append(c)  # type: ignore[arg-type]
        elif len(c) == 3:
            three_by_trip[tuple(sorted((abs(c[0]), abs(c[1]), abs(c[2]))))].append(c)  # type: ignore[arg-type]

    gates_by_in: dict[tuple[int, int], list[tuple[int, tuple[int, ...]]]] = defaultdict(list)
    gate_of_quad_out: dict[int, tuple[int, int, tuple[int, ...]]] = {}

    for trip, t_list in three_by_trip.items():
        v0, v1, v2 = trip
        rel = (
            list(t_list)
            + two_by_pair.get((v0, v1), [])
            + two_by_pair.get((v0, v2), [])
            + two_by_pair.get((v1, v2), [])
        )
        sat_m = 255
        for c in rel:
            sub = 255
            for l in c:
                j = 0 if abs(l) == v0 else (1 if abs(l) == v1 else 2)
                vt = VAR_TT_CACHE[3][j]
                sub &= vt if l < 0 else (vt ^ 255)
            sat_m &= ~sub
        if sat_m == 0:
            return "UNSAT", None, None

        for out_j in range(3):
            in_js = [j for j in range(3) if j != out_j]
            u_v, w_v, out_v = trip[in_js[0]], trip[in_js[1]], trip[out_j]
            tt4: list[int] = []
            ok_f = True
            for bu in (0, 1):
                for bw in (0, 1):
                    v_bo = []
                    for bo in (0, 1):
                        b0 = bu if 0 == in_js[0] else (bw if 0 == in_js[1] else bo)
                        b1 = bu if 1 == in_js[0] else (bw if 1 == in_js[1] else bo)
                        b2 = bu if 2 == in_js[0] else (bw if 2 == in_js[1] else bo)
                        if (sat_m >> ((b0 << 2) | (b1 << 1) | b2)) & 1:
                            v_bo.append(bo)
                    if len(v_bo) != 1:
                        ok_f = False
                        break
                    tt4.append(v_bo[0])
                if not ok_f:
                    break
            if ok_f:
                t_tup = tuple(tt4)
                gates_by_in[(u_v, w_v)].append((out_v, t_tup))
                if (t_tup[0] ^ t_tup[1] ^ t_tup[2] ^ t_tup[3]) == 1:
                    gate_of_quad_out[out_v] = (u_v, w_v, t_tup)

    return "OK", gates_by_in, gate_of_quad_out


def blind_adder_telescoping_engine(
    clauses: list[list[int]],
) -> tuple[str, dict[int, int], dict[int, tuple[int, int]], list[list[int]]]:
    """
    Blind O(N^3) arithmetic adder telescoping + incremental 2-adic/GCD bit-peeling engine.
    Returns (status_str, fixed_dict, equiv_dict, reduced_clauses).
    """
    fixed: dict[int, int] = {}
    equiv: dict[int, tuple[int, int]] = {}
    work = [list(c) for c in clauses]

    # Phase 1: Blind gate congruence closure (merges isomorphic/negated gates)
    for _ in range(10):
        st, work = propagate_bcp_2clause_and_2xor(work, fixed, equiv)
        if st == "UNSAT":
            return "UNSAT_CONG_BCP", fixed, equiv, []
        st_g, gates_by_in, _ = scan_deterministic_2input_gates(work)
        if st_g == "UNSAT" or gates_by_in is None:
            return "UNSAT_LOCAL3", fixed, equiv, []
        merged_any = False
        for (_u_v, _w_v), glist in gates_by_in.items():
            if len(glist) >= 2:
                for i in range(len(glist)):
                    o1, t1 = glist[i]
                    comp1 = tuple(1 ^ b for b in t1)
                    for j in range(i + 1, len(glist)):
                        o2, t2 = glist[j]
                        if o1 != o2 and (t2 == t1 or t2 == comp1):
                            hi, lo = (o1, o2) if o1 > o2 else (o2, o1)
                            fl = 0 if t2 == t1 else 1
                            if hi not in fixed and hi not in equiv:
                                equiv[hi] = (lo, fl)
                                merged_any = True
        if not merged_any:
            break

    st, work = propagate_bcp_2clause_and_2xor(work, fixed, equiv)
    if st == "UNSAT":
        return "UNSAT_POST_CONG", fixed, equiv, []
    if not work:
        return "OK_EMPTY", fixed, equiv, []

    st_g, gates_by_in, gate_of_out = scan_deterministic_2input_gates(work)
    if st_g == "UNSAT" or gates_by_in is None or gate_of_out is None:
        return "UNSAT_LOCAL3", fixed, equiv, []

    # Phase 2: Extract exact Z-linear half-adder and disjoint-carry full-adder equations
    z_eqs: list[dict[int, int]] = []
    xor_on_pair: dict[tuple[int, int], list[tuple[int, tuple[int, ...]]]] = defaultdict(list)
    for (u_v, w_v), glist in gates_by_in.items():
        xors = [(o, t) for o, t in glist if (t[0] ^ t[1] ^ t[2] ^ t[3]) == 0 and t[0] != t[1] and t[0] != t[2]]
        quads = [(o, t) for o, t in glist if (t[0] ^ t[1] ^ t[2] ^ t[3]) == 1]
        for o, t in xors:
            xor_on_pair[(u_v, w_v)].append((o, t))
        for s_v, ts in xors:
            for c_v, tc in quads:
                cnt_0 = sum(1 for b in tc if b == 0)
                spec_val = 0 if cnt_0 == 1 else 1
                idx_spec = tc.index(spec_val)
                bu0, bw0 = idx_spec >> 1, idx_spec & 1
                opp_idx = ((1 - bu0) << 1) | (1 - bw0)
                s_flip = ts[opp_idx]
                row: dict[int, int] = defaultdict(int)
                rhs = 0
                if bu0 == 1:
                    row[u_v] += 1
                else:
                    row[u_v] -= 1
                    rhs -= 1
                if bw0 == 1:
                    row[w_v] += 1
                else:
                    row[w_v] -= 1
                    rhs -= 1
                if s_flip == 0:
                    row[s_v] -= 1
                else:
                    row[s_v] += 1
                    rhs += 1
                if spec_val == 1:
                    row[c_v] -= 2
                else:
                    row[c_v] += 2
                    rhs += 2
                row[0] = rhs
                z_eqs.append(dict(row))

    for cout_v, (c1_v, c2_v, t_out) in gate_of_out.items():
        if c1_v in gate_of_out and c2_v in gate_of_out:
            p1, t1 = gate_of_out[c1_v][:2], gate_of_out[c1_v][2]
            p2, t2 = gate_of_out[c2_v][:2], gate_of_out[c2_v][2]
            found_dc = False
            for pa, ta, pb, tb, first_is_1 in [(p1, t1, p2, t2, True), (p2, t2, p1, t1, False)]:
                for x_wire, tx in xor_on_pair.get(pa, ()):
                    if x_wire in pb:
                        reachable = set()
                        x_pos = 0 if pb[0] == x_wire else 1
                        for ba in (0, 1):
                            for bb in (0, 1):
                                bx = tx[(ba << 1) | bb]
                                v_a = ta[(ba << 1) | bb]
                                for bo in (0, 1):
                                    v_b = tb[(bx << 1) | bo if x_pos == 0 else (bo << 1) | bx]
                                    reachable.add((v_a, v_b) if first_is_1 else (v_b, v_a))
                        if len(reachable) == 3:
                            pts = sorted(reachable)
                            mat = np.array([[p[0], p[1], 1] for p in pts], dtype=int)
                            yv = np.array([t_out[(p[0] << 1) | p[1]] for p in pts], dtype=int)
                            sol = np.round(np.linalg.solve(mat, yv)).astype(int)
                            z_eqs.append({c1_v: int(sol[0]), c2_v: int(sol[1]), cout_v: -1, 0: -int(sol[2])})
                            found_dc = True
                            break
                if found_dc:
                    break

    if not z_eqs:
        return "OK", fixed, equiv, work

    # Phase 3: Single sparse rational RREF + incremental 2-adic/GCD bit-peeling
    zeq_occ: dict[int, int] = defaultdict(int)
    for eq in z_eqs:
        for k, val in eq.items():
            if k != 0 and val != 0:
                zeq_occ[k] += 1

    def col_prio(k: int) -> tuple[int, int]:
        return (1 if zeq_occ[k] >= 2 else 0, k)

    pivots: dict[int, dict[int, Fraction]] = {}

    def insert_row_into_pivots(raw_dict: dict[int, int] | dict[int, Fraction]) -> bool:
        row: dict[int, Fraction] = {k: Fraction(v) for k, v in raw_dict.items() if v != 0 or k == 0}
        row[0] = row.get(0, Fraction(0))
        while True:
            cols = [k for k in row.keys() if k != 0 and row[k] != 0]
            if not cols:
                return row[0] != 0
            lead = max(cols, key=col_prio)
            if lead in pivots:
                fac = row[lead]
                for k, pv in pivots[lead].items():
                    nv = row.get(k, Fraction(0)) - fac * pv
                    if k != 0 and nv == 0:
                        row.pop(k, None)
                    else:
                        row[k] = nv
            else:
                inv_l = Fraction(1) / row[lead]
                nrow = {k: v * inv_l for k, v in row.items() if k == 0 or v * inv_l != 0}
                for _pk, prow in pivots.items():
                    if lead in prow:
                        f2 = prow[lead]
                        for k, nv2 in nrow.items():
                            val2 = prow.get(k, Fraction(0)) - f2 * nv2
                            if k != 0 and val2 == 0:
                                prow.pop(k, None)
                            else:
                                prow[k] = val2
                pivots[lead] = nrow
                return False

    for eq in z_eqs:
        if insert_row_into_pivots(eq):
            return "UNSAT_Z_RREF_INIT", fixed, equiv, []

    def resolve_v(v: int) -> tuple[int, int]:
        fl = 0
        while v in equiv:
            v, f = equiv[v]
            fl ^= f
        return v, fl

    touched_vars = set(fixed.keys()) | set(equiv.keys())
    for peel_iter in range(1, 80):
        if touched_vars:
            affected_leads = [
                ld for ld, prow in list(pivots.items())
                if ld in touched_vars or any(k in touched_vars for k in prow if k != 0)
            ]
            reinsert_rows = []
            for ld in affected_leads:
                prow = pivots.pop(ld)
                neq: dict[int, Fraction] = defaultdict(Fraction)
                rhs = prow.get(0, Fraction(0))
                for k, coeff in prow.items():
                    if k == 0 or coeff == 0:
                        continue
                    rv, fl = resolve_v(k)
                    if rv in fixed:
                        rhs -= coeff * (fixed[rv] ^ fl)
                    else:
                        if fl == 0:
                            neq[rv] += coeff
                        else:
                            rhs -= coeff
                            neq[rv] -= coeff
                neq[0] = rhs
                reinsert_rows.append(neq)
            touched_vars.clear()
            for r_dict in reinsert_rows:
                if insert_row_into_pivots(r_dict):
                    return f"UNSAT_Z_RREF_IT{peel_iter}", fixed, equiv, []

        prev_f, prev_e = set(fixed.keys()), set(equiv.keys())
        found_new = False

        for prow in list(pivots.values()):
            cols = [k for k in prow.keys() if k != 0 and prow[k] != 0]
            if not cols:
                if prow.get(0, 0) != 0:
                    return f"UNSAT_Z_CONST_IT{peel_iter}", fixed, equiv, []
                continue
            if len(cols) > 80:
                continue
            lcm_d = 1
            for k in cols + [0]:
                lcm_d = math.lcm(lcm_d, prow[k].denominator)
            i_coeffs = {k: int(prow[k] * lcm_d) for k in cols}
            i_rhs = int(prow[0] * lcm_d)
            g_all = 0
            for c_v in i_coeffs.values():
                g_all = math.gcd(g_all, abs(c_v))
            if g_all > 1:
                if i_rhs % g_all != 0:
                    return f"UNSAT_Z_GCD_GHOST_IT{peel_iter}", fixed, equiv, []
                for k in cols:
                    i_coeffs[k] //= g_all
                i_rhs //= g_all

            min_s = sum(c for c in i_coeffs.values() if c < 0)
            max_s = sum(c for c in i_coeffs.values() if c > 0)
            if i_rhs < min_s or i_rhs > max_s:
                return f"UNSAT_ARCHIMEDEAN_BOUND_IT{peel_iter}", fixed, equiv, []
            if i_rhs == min_s:
                for k, c in i_coeffs.items():
                    fixed[k] = 1 if c < 0 else 0
                found_new = True
            elif i_rhs == max_s:
                for k, c in i_coeffs.items():
                    fixed[k] = 1 if c > 0 else 0
                found_new = True

            odd_vars = [k for k, c in i_coeffs.items() if (c & 1) == 1]
            rhs_mod2 = i_rhs & 1
            if len(odd_vars) == 0 and rhs_mod2 == 1:
                return f"UNSAT_2ADIC_PARITY_IT{peel_iter}", fixed, equiv, []
            elif len(odd_vars) == 1:
                v0 = odd_vars[0]
                if v0 in fixed and fixed[v0] != rhs_mod2:
                    return f"UNSAT_2ADIC_UNIT_IT{peel_iter}", fixed, equiv, []
                if v0 not in fixed:
                    fixed[v0] = rhs_mod2
                    found_new = True
            elif len(odd_vars) == 2:
                v1, v2 = sorted(odd_vars)
                if v2 not in fixed and v2 not in equiv:
                    equiv[v2] = (v1, rhs_mod2)
                    found_new = True

        st, work = propagate_bcp_2clause_and_2xor(work, fixed, equiv)
        if st == "UNSAT":
            return f"UNSAT_OSTROWSKI_HENSEL_PEEL_IT{peel_iter}", fixed, equiv, []

        new_f = set(fixed.keys()) - prev_f
        new_e = set(equiv.keys()) - prev_e
        touched_vars.update(new_f)
        touched_vars.update(new_e)
        if not found_new and not touched_vars:
            break

    return "OK", fixed, equiv, work


def blind_functional_root_dag_solve(
    clauses: list[list[int]],
    fixed_init: dict[int, int] | None = None,
    equiv_init: dict[int, tuple[int, int]] | None = None,
    max_roots: int = 16,
) -> tuple[str, dict[int, int] | None]:
    """
    Blind functional input-dimension reduction: when the extracted acyclic gate DAG
    depends on <= max_roots free input variables, evaluate all 2^R fibers bitwise.
    """
    fixed = dict(fixed_init) if fixed_init else {}
    equiv = dict(equiv_init) if equiv_init else {}
    st, work = propagate_bcp_2clause_and_2xor([list(c) for c in clauses], fixed, equiv)
    if st == "UNSAT":
        return "UNSAT_DAG_PRE", None
    if not work:
        return "SAT_DAG_TRIVIAL", fixed

    work = fast_unroll_11_chains(work)
    if not work:
        return "SAT_DAG_TRIVIAL", fixed

    st_g, gates_by_in, quad_gates = scan_deterministic_2input_gates(work)
    if st_g == "UNSAT" or gates_by_in is None or quad_gates is None:
        return "UNSAT_DAG_LOCAL3", None

    all_active = sorted({abs(l) for c in work for l in c})
    all_cand = []
    for out_v, (u_v, w_v, tt4) in quad_gates.items():
        all_cand.append((0, out_v, u_v, w_v, tt4))
    for (u_v, w_v), glist in gates_by_in.items():
        for out_v, tt4 in glist:
            if (tt4[0] ^ tt4[1] ^ tt4[2] ^ tt4[3]) == 0 and tt4[0] != tt4[1] and tt4[0] != tt4[2]:
                all_cand.append((1, out_v, u_v, w_v, tt4))

    anc = {v: {v} for v in all_active}
    chosen_def = {}
    quad_inputs = {x for (u, w, _) in quad_gates.values() for x in (u, w)} - set(quad_gates.keys())
    all_cand.sort(key=lambda item: (item[0], 1 if item[1] in quad_inputs else 0, -item[1]))

    for _kind, out_v, u_v, w_v, tt4 in all_cand:
        if out_v in chosen_def:
            continue
        if out_v in anc[u_v] or out_v in anc[w_v]:
            continue
        chosen_def[out_v] = (u_v, w_v, tt4)
        new_anc = anc[u_v] | anc[w_v]
        for k_v in all_active:
            if k_v == out_v:
                anc[k_v] = new_anc
            elif out_v in anc[k_v]:
                anc[k_v] = (anc[k_v] - {out_v}) | new_anc

    roots = sorted({r for k_v in all_active for r in anc[k_v]})
    n_r = len(roots)
    if n_r > max_roots:
        return f"SKIP(R={n_r})", None

    eval_tt: dict[int, int] = {}
    all_ones = (1 << (1 << n_r)) - 1
    for j, rv in enumerate(roots):
        step = 1 << (n_r - 1 - j)
        m = ((1 << step) - 1) << step
        cur_len = 2 * step
        while cur_len < (1 << n_r):
            m |= (m << cur_len)
            cur_len <<= 1
        eval_tt[rv] = m

    remaining = [v for v in all_active if v not in eval_tt]
    while remaining:
        progressed = False
        nxt_rem = []
        for v in remaining:
            u_v, w_v, tt4 = chosen_def[v]
            if u_v in eval_tt and w_v in eval_tt:
                tu, tw = eval_tt[u_v], eval_tt[w_v]
                nu, nw = tu ^ all_ones, tw ^ all_ones
                res_m = 0
                if tt4[0]:
                    res_m |= nu & nw
                if tt4[1]:
                    res_m |= nu & tw
                if tt4[2]:
                    res_m |= tu & nw
                if tt4[3]:
                    res_m |= tu & tw
                eval_tt[v] = res_m
                progressed = True
            else:
                nxt_rem.append(v)
        if not progressed:
            return "SKIP_CYCLE", None
        remaining = nxt_rem

    valid_mask = all_ones
    for c in work:
        c_m = 0
        for l in c:
            tv = eval_tt[abs(l)]
            c_m |= tv if l > 0 else (tv ^ all_ones)
        valid_mask &= c_m
        if valid_mask == 0:
            return f"UNSAT_BLIND_ROOT_DAG(R={n_r})", None

    sol_count = valid_mask.bit_count()
    lsb = valid_mask & -valid_mask
    row_idx = lsb.bit_length() - 1

    model = dict(fixed)
    for v in all_active:
        model[v] = (eval_tt[v] >> row_idx) & 1

    for u_orig in sorted(equiv.keys()):
        rv, fl = u_orig, 0
        while rv in equiv:
            rv, f = equiv[rv]
            fl ^= f
        model[u_orig] = model.get(rv, 0) ^ fl

    return f"SAT_BLIND_ROOT_DAG(R={n_r},sols={sol_count})", model
