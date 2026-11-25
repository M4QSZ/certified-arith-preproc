"""Coupled sparse degree-3 Macaulay, modular hyperplanes, guarded clique cutting planes, and vertex-cut decomposition."""

from __future__ import annotations

import itertools
from collections import defaultdict
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from .adder_extraction import blind_adder_telescoping_engine, blind_functional_root_dag_solve
from .cnf_utils import (
    VAR_TT_CACHE,
    apply_fixed_and_equivs_to_clauses,
    compact_active_cnf,
    fast_unroll_11_chains,
    gf2_vec_rref,
    propagate_bcp_2clause_and_2xor,
    simplify_and_bve,
)
from .veronese_annihilator import synthesize_ef_extensions


def rref_mod_p(rows_dict_list: list[dict[int, int]], p: int) -> tuple[bool, list[dict[int, int]]]:
    """Exact sparse RREF over F_p. Key 0 stores the RHS constant."""
    pivots: dict[int, dict[int, int]] = {}
    inv_p = {a: pow(a, p - 2, p) for a in range(1, p)}

    for raw in rows_dict_list:
        row = {k: (v % p) for k, v in raw.items() if (v % p) != 0 or k == 0}
        row[0] = row.get(0, 0) % p
        while True:
            cols = [k for k in row.keys() if k != 0 and row[k] % p != 0]
            if not cols:
                if row[0] % p != 0:
                    return True, []
                break
            lead = max(cols)
            if lead in pivots:
                factor = row[lead] % p
                prow = pivots[lead]
                for k, pv in prow.items():
                    row[k] = (row.get(k, 0) - factor * pv) % p
                    if k != 0 and row[k] == 0:
                        del row[k]
            else:
                inv_lead = inv_p[row[lead] % p]
                norm_row = {k: (v * inv_lead) % p for k, v in row.items() if k == 0 or (v * inv_lead) % p != 0}
                norm_row[0] = norm_row.get(0, 0) % p
                for _pk, prow in pivots.items():
                    if lead in prow:
                        f2 = prow[lead] % p
                        for k, nv in norm_row.items():
                            prow[k] = (prow.get(k, 0) - f2 * nv) % p
                            if k != 0 and prow[k] == 0:
                                del prow[k]
                pivots[lead] = norm_row
                break
    return False, list(pivots.values())


def extract_modular_hyperplanes(
    work_clauses: list[list[int]],
    fixed: dict[int, int],
    primes: tuple[int, ...] = (2, 3, 5),
) -> tuple[str, dict[int, list[dict[int, int]]]]:
    """Extract linear equations over F_p satisfied on all local <=3-variable truth-table points."""
    by_vars: dict[tuple[int, ...], list[list[int]]] = defaultdict(list)
    for cl in work_clauses:
        if 2 <= len(cl) <= 3:
            by_vars[tuple(sorted(abs(x) for x in cl))].append(cl)

    eqs_by_p = {p: [{v: 1, 0: val % p} for v, val in fixed.items()] for p in primes}

    for vtuple, cl_list in by_vars.items():
        k = len(vtuple)
        allowed = []
        for bits in itertools.product((0, 1), repeat=k):
            vmap = dict(zip(vtuple, bits))
            ok = True
            for cl in cl_list:
                if not any((vmap[abs(lit)] == 1 if lit > 0 else vmap[abs(lit)] == 0) for lit in cl):
                    ok = False
                    break
            if ok:
                allowed.append(bits)

        if len(allowed) == 0:
            return "UNSAT_LOCAL_TRUTHTABLE", eqs_by_p

        for p in primes:
            if len(allowed) >= (1 << k):
                continue
            for coeffs in itertools.product(range(p), repeat=k):
                nz = [c for c in coeffs if c != 0]
                if not nz or nz[0] != 1:
                    continue
                vals = {(sum(c * b for c, b in zip(coeffs, pt)) % p) for pt in allowed}
                if len(vals) == 1:
                    rhs = next(iter(vals))
                    row: dict[int, int] = {0: rhs}
                    for var_id, c in zip(vtuple, coeffs):
                        if c != 0:
                            row[var_id] = c
                    eqs_by_p[p].append(row)

    return "OK", eqs_by_p


def extract_local_vanishing_ideal(
    supp: tuple[int, ...],
    cl_list: list[list[int]],
    deg_lim: int,
) -> list[set[tuple[int, ...]]]:
    """Compute a GF(2) basis of polynomials of degree <= deg_lim vanishing on all SAT assignments of `cl_list`."""
    k = len(supp)
    all_ones = (1 << (1 << k)) - 1
    pos = {v: j for j, v in enumerate(supp)}
    sat_mask = all_ones
    for c in cl_list:
        sub_mask = all_ones
        for lit in c:
            j = pos[abs(lit)]
            v_tt = VAR_TT_CACHE[k][j]
            sub_mask &= v_tt if lit < 0 else (v_tt ^ all_ones)
        sat_mask &= ~sub_mask

    if sat_mask == 0:
        return [{()}]

    monoms: list[tuple[int, ...]] = [()] + [
        comb
        for r in range(1, min(deg_lim, k) + 1)
        for comb in itertools.combinations(supp, r)
    ]
    v_tts = VAR_TT_CACHE[k]
    sub_tt: dict[tuple[int, ...], int] = {(): all_ones}
    for j, v in enumerate(supp):
        sub_tt[(v,)] = v_tts[j]
    for m in monoms:
        if len(m) >= 2:
            sub_tt[m] = sub_tt[m[:-1]] & sub_tt[(m[-1],)]

    pivots: dict[int, tuple[int, int]] = {}
    ideal_polys: list[set[tuple[int, ...]]] = []
    for idx_m, m in enumerate(monoms):
        vec = sub_tt[m] & sat_mask
        comb = 1 << idx_m
        while vec:
            msb = vec.bit_length() - 1
            if msb in pivots:
                pv, pc = pivots[msb]
                vec ^= pv
                comb ^= pc
            else:
                pivots[msb] = (vec, comb)
                break
        else:
            poly: set[tuple[int, ...]] = set()
            tmp = comb
            while tmp:
                b = tmp.bit_length() - 1
                poly.add(monoms[b])
                tmp ^= (1 << b)
            if poly:
                ideal_polys.append(poly)
    return ideal_polys


def mul_var_poly(v: int, poly: set[tuple[int, ...]]) -> set[tuple[int, ...]]:
    """Multiply a Boolean polynomial by variable `v` modulo (x_i^2 = x_i)."""
    out: set[tuple[int, ...]] = set()
    for m in poly:
        if m == ():
            nm: tuple[int, ...] = (v,)
        elif v in m:
            nm = m
        else:
            nm = tuple(sorted(m + (v,)))
        if nm in out:
            out.remove(nm)
        else:
            out.add(nm)
    return out


def degree_absorbing_macaulay_cascade(
    clauses: list[list[int]],
    fixed_init: dict[int, int] | None = None,
    max_deg: int = 3,
    max_rounds: int = 5,
    max_active_vars: int = 48,
) -> tuple[str, dict[int, int], dict[int, tuple[int, int]], list[list[int]]]:
    """Dense bitmask degree-absorbing Macaulay cascade for <=48-variable unrolled cores."""
    fixed = dict(fixed_init) if fixed_init else {}
    equiv: dict[int, tuple[int, int]] = {}
    work = fast_unroll_11_chains(clauses)

    for rnd in range(1, max_rounds + 1):
        st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
        if st == "UNSAT":
            return f"UNSAT_BCP_MACAULAY_R{rnd}", fixed, equiv, []

        unit_changed = True
        while unit_changed:
            unit_changed = False
            for c in work:
                if len(c) == 1:
                    v = abs(c[0])
                    val = 1 if c[0] > 0 else 0
                    if v in fixed and fixed[v] != val:
                        return f"UNSAT_UNIT_MACAULAY_R{rnd}", fixed, equiv, []
                    if v not in fixed:
                        fixed[v] = val
                        unit_changed = True
            if unit_changed:
                st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
                if st == "UNSAT":
                    return f"UNSAT_BCP_MACAULAY_R{rnd}", fixed, equiv, []

        if not work:
            return "OK", fixed, equiv, []

        unrolled = fast_unroll_11_chains(work)
        all_active = sorted({abs(l) for c in unrolled for l in c})
        if not all_active or len(all_active) > max_active_vars:
            return "OK", fixed, equiv, work

        by_supp: dict[tuple[int, ...], list[list[int]]] = defaultdict(list)
        skip_mac = False
        for c in unrolled:
            if len(c) == 0:
                return f"UNSAT_EMPTY_R{rnd}", fixed, equiv, []
            if len(c) == 1:
                v = abs(c[0])
                fixed[v] = 1 if c[0] > 0 else 0
                skip_mac = True
            elif len(c) <= 7:
                supp = tuple(sorted({abs(l) for l in c}))
                by_supp[supp].append(c)
        if skip_mac:
            continue
        if not by_supp:
            return "OK", fixed, equiv, work

        deduced_new = False
        for d_cur in ([2] if max_deg <= 2 else [2, 3]):
            global_polys: list[set[tuple[int, ...]]] = []
            for supp, cl_list in by_supp.items():
                id2 = extract_local_vanishing_ideal(supp, cl_list, min(2, d_cur))
                if id2 == [{()}]:
                    return f"UNSAT_LOCAL_IDEAL_R{rnd}", fixed, equiv, []
                global_polys.extend(id2)
                if d_cur >= 3:
                    if len(supp) >= 3:
                        id3 = extract_local_vanishing_ideal(supp, cl_list, 3)
                        global_polys.extend(id3)
                    for p2 in id2:
                        for v in all_active:
                            prod = mul_var_poly(v, p2)
                            if prod:
                                global_polys.append(prod)

            if not global_polys:
                continue

            nonconst = sorted(
                {m for p in global_polys for m in p if m != ()},
                key=lambda x: (len(x), x),
            )
            m_idx = {m: idx + 1 for idx, m in enumerate(nonconst)}
            max_deg1_idx = sum(1 for m in nonconst if len(m) == 1)
            idx_to_var = {m_idx[m]: m[0] for m in nonconst if len(m) == 1}

            vecs = []
            for p in global_polys:
                if not p:
                    continue
                mask = 1 if () in p else 0
                for m in p:
                    if m != ():
                        mask |= (1 << m_idx[m])
                if mask:
                    vecs.append(mask)

            rref = gf2_vec_rref(vecs)
            if any(v == 1 for v in rref):
                return f"UNSAT_ABSORBING_MACAULAY_D{d_cur}_R{rnd}", fixed, equiv, []

            for row in rref:
                msb = row.bit_length() - 1
                if 1 <= msb <= max_deg1_idx:
                    const_b = row & 1
                    lin_bits = row >> 1
                    deg_lin = lin_bits.bit_count()
                    if deg_lin == 1:
                        v_u = idx_to_var[msb]
                        if v_u in fixed and fixed[v_u] != const_b:
                            return f"UNSAT_MACAULAY_UNIT_CONFLICT_R{rnd}", fixed, equiv, []
                        if v_u not in fixed:
                            fixed[v_u] = const_b
                            deduced_new = True
                    elif deg_lin == 2:
                        u_hi = idx_to_var[msb]
                        rem_row = row ^ (1 << msb) ^ const_b
                        lo_idx = rem_row.bit_length() - 1
                        v_lo = idx_to_var[lo_idx]
                        if u_hi not in fixed and u_hi not in equiv and u_hi != v_lo:
                            equiv[u_hi] = (v_lo, const_b)
                            deduced_new = True

            if deduced_new:
                break

        if not deduced_new:
            break

    for v_orig in list(equiv.keys()):
        rv, fl = v_orig, 0
        while rv in equiv:
            rv, f = equiv[rv]
            fl ^= f
        if rv in fixed:
            fixed[v_orig] = fixed[rv] ^ fl

    st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
    if st == "UNSAT":
        return "UNSAT_FINAL_MACAULAY_PROP", fixed, equiv, []
    return "OK", fixed, equiv, work


def sparse_gf2_rref_deg_lex(
    polys: list[set[tuple[int, ...]]],
) -> tuple[str, dict[int, int], dict[int, tuple[int, int]]]:
    """Sparse GF(2) RREF with degree-lex ordering (deg >= 3 > deg 2 > deg 1 > const)."""
    monoms = sorted({m for p in polys for m in p if m != ()}, key=lambda x: (len(x), x))
    m_to_id: dict[tuple[int, ...], int] = {(): 0}
    id_to_var: dict[int, int] = {}
    for idx, m in enumerate(monoms, start=1):
        m_to_id[m] = idx
        if len(m) == 1:
            id_to_var[idx] = m[0]
    max_lin_id = sum(1 for m in monoms if len(m) == 1)

    pivots: dict[int, set[int]] = {}
    for p in polys:
        if not p:
            continue
        row = {m_to_id[m] for m in p}
        while row:
            lead = max(row)
            if lead == 0:
                return "UNSAT", {}, {}
            if lead in pivots:
                row ^= pivots[lead]
            else:
                pivots[lead] = row
                break

    lin_leads = sorted(ld for ld in pivots if 1 <= ld <= max_lin_id)
    for i, ld_lo in enumerate(lin_leads):
        r_lo = pivots[ld_lo]
        for ld_hi in lin_leads[i + 1 :]:
            if ld_lo in pivots[ld_hi]:
                pivots[ld_hi] ^= r_lo
                if pivots[ld_hi] == {0}:
                    return "UNSAT", {}, {}

    new_fx: dict[int, int] = {}
    new_eq: dict[int, tuple[int, int]] = {}
    for ld in lin_leads:
        r = pivots[ld]
        if not r:
            continue
        if r == {0}:
            return "UNSAT", {}, {}
        const_b = 1 if 0 in r else 0
        vars_in_r = sorted(id_to_var[x] for x in r if x != 0)
        if len(vars_in_r) == 1:
            v0 = vars_in_r[0]
            if v0 in new_fx and new_fx[v0] != const_b:
                return "UNSAT", {}, {}
            new_fx[v0] = const_b
        elif len(vars_in_r) == 2:
            v_lo, v_hi = vars_in_r[0], vars_in_r[1]
            if v_hi not in new_fx and v_hi not in new_eq and v_hi != v_lo:
                new_eq[v_hi] = (v_lo, const_b)
    return "OK", new_fx, new_eq


def diamond_petal_sparse_macaulay(
    clauses: list[list[int]],
    fixed: dict[int, int],
    equiv: dict[int, tuple[int, int]],
    max_deg: int = 3,
    max_diamond_3cls: int = 2400,
    max_mac_vars: int = 160,
) -> tuple[str, list[list[int]]]:
    """
    Collision-prioritized width-3 diamond resolution + 4-variable petal ideals +
    sparse O(nnz) degree-absorbing GF(2) RREF.
    """
    work = [list(c) for c in clauses]

    for mac_outer in range(4):
        for _ in range(14):
            st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
            if st == "UNSAT":
                return f"UNSAT_W3_BCP_M{mac_outer+1}", []
            chg = False
            cl_set = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in work}

            for c in list(work):
                if len(c) == 1:
                    v, val = abs(c[0]), (1 if c[0] > 0 else 0)
                    if v in fixed and fixed[v] != val:
                        return f"UNSAT_W3_UNIT_M{mac_outer+1}", []
                    if v not in fixed:
                        fixed[v] = val
                        chg = True
                elif len(c) == 2:
                    a, b = c[0], c[1]
                    if tuple(sorted((-a, b), key=lambda z: (abs(z), z))) in cl_set:
                        vb, valb = abs(b), (1 if b > 0 else 0)
                        if vb in fixed and fixed[vb] != valb:
                            return f"UNSAT_W3_2UNIT_M{mac_outer+1}", []
                        if vb not in fixed:
                            fixed[vb] = valb
                            chg = True
                    if tuple(sorted((a, -b), key=lambda z: (abs(z), z))) in cl_set:
                        va, vala = abs(a), (1 if a > 0 else 0)
                        if va in fixed and fixed[va] != vala:
                            return f"UNSAT_W3_2UNIT_M{mac_outer+1}", []
                        if va not in fixed:
                            fixed[va] = vala
                            chg = True
                    if tuple(sorted((-a, -b), key=lambda z: (abs(z), z))) in cl_set:
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
                        nc = tuple(sorted({a, c_lit}, key=lambda z: (abs(z), z)))
                        if nc not in cl_set:
                            cl_set.add(nc)
                            new_2.append(list(nc))

            for c3 in three_cls:
                for idx_p in range(3):
                    piv = c3[idx_p]
                    o1, o2 = c3[(idx_p + 1) % 3], c3[(idx_p + 2) % 3]
                    for other in by_lit2.get(-piv, ()):
                        if other == o1 or other == o2:
                            nc = tuple(sorted({o1, o2}, key=lambda z: (abs(z), z)))
                            if nc not in cl_set:
                                cl_set.add(nc)
                                new_2.append(list(nc))
            if new_2:
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
            work.extend(added)

        st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
        if st == "UNSAT":
            return f"UNSAT_POST_W3_M{mac_outer+1}", []
        if not work or max_deg < 2:
            break

        unrolled = fast_unroll_11_chains(work)
        all_active = sorted({abs(l) for c in unrolled for l in c})
        if not all_active or len(all_active) > max_mac_vars:
            break

        by_supp: dict[tuple[int, ...], list[list[int]]] = defaultdict(list)
        for c in unrolled:
            if len(c) == 0:
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
                        return f"UNSAT_LOCAL_IDEAL_M{mac_outer+1}", []
                    polys.extend(id2)
                    quad_generators.extend(id2)
                    if d_cur >= 3 and len(supp) >= 3:
                        polys.extend(extract_local_vanishing_ideal(supp, cl_list, 3))

            for u4, cls_u4 in petals_4.items():
                id2_p = extract_local_vanishing_ideal(u4, cls_u4, 2)
                if id2_p == [{()}]:
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
                    return f"UNSAT_SMAC_UNIT_CONFLICT_M{mac_outer+1}", []
                if v not in fixed:
                    fixed[v] = b
                    deduced_mac = True
            for u, (rv, fl) in neq.items():
                if u not in fixed and u not in equiv:
                    equiv[u] = (rv, fl)
                    deduced_mac = True
            if deduced_mac:
                break

        if not deduced_mac:
            break

    st, work = apply_fixed_and_equivs_to_clauses(work, fixed, equiv)
    if st == "UNSAT":
        return "UNSAT_SMAC_FINAL", []
    return "OK", work


def guarded_cutting_planes_lp(
    n_vars: int,
    clauses: list[list[int]],
    fixed_init: dict[int, int] | None = None,
    equiv_init: dict[int, tuple[int, int]] | None = None,
    max_rounds: int = 5,
) -> tuple[str, dict[int, int], dict[int, tuple[int, int]], list[list[int]]]:
    """
    Monotone modular hyperplanes (F_2, F_3, F_5) + guarded clique LP +
    Chvatal-Gomory single-variable, pair-carry, and 2-XOR rounding.
    """
    fixed = dict(fixed_init) if fixed_init else {}
    equiv = dict(equiv_init) if equiv_init else {}
    learned_2cls: list[list[int]] = []
    st0, work = apply_fixed_and_equivs_to_clauses(clauses, fixed, equiv)
    if st0 == "UNSAT":
        return "UNSAT_PRE_ADELIC", fixed, equiv, learned_2cls

    for rnd in range(1, max_rounds + 1):
        # Monotone exact propagation only (never pure-literal/BVE on a clause subset).
        st, work = propagate_bcp_2clause_and_2xor(work, fixed, equiv)
        if st != "OK":
            return f"{st}_R{rnd}", fixed, equiv, learned_2cls

        st_ad, eqs_by_p = extract_modular_hyperplanes(work, fixed, primes=(2, 3, 5))
        if st_ad != "OK":
            return f"{st_ad}_R{rnd}", fixed, equiv, learned_2cls

        new_deduction = False
        short_gf2_xors = []
        for p in (2, 3, 5):
            unsat_p, basis_p = rref_mod_p(eqs_by_p[p], p)
            if unsat_p:
                return f"UNSAT_ADELIC_MOD{p}_R{rnd}", fixed, equiv, learned_2cls
            for row in basis_p:
                rhs = row.get(0, 0) % p
                vs = [k for k in row.keys() if k != 0 and row[k] % p != 0]
                if len(vs) == 1:
                    v0 = vs[0]
                    if rhs not in (0, 1):
                        return f"UNSAT_TEICHMULLER_GHOST_MOD{p}_R{rnd}", fixed, equiv, learned_2cls
                    if v0 in fixed and fixed[v0] != rhs:
                        return f"UNSAT_CROSS_PRIME_UNIT_R{rnd}", fixed, equiv, learned_2cls
                    if v0 not in fixed:
                        fixed[v0] = rhs
                        new_deduction = True
                elif len(vs) == 2:
                    v1, v2 = sorted(vs)
                    c1, c2 = row[v1] % p, row[v2] % p
                    valid_pairs = [
                        (b1, b2) for b1 in (0, 1) for b2 in (0, 1)
                        if (c1 * b1 + c2 * b2) % p == rhs
                    ]
                    if len(valid_pairs) == 0:
                        return f"UNSAT_PAIR_GHOST_MOD{p}_R{rnd}", fixed, equiv, learned_2cls
                    if len(valid_pairs) == 1:
                        b1, b2 = valid_pairs[0]
                        for vv, bb in ((v1, b1), (v2, b2)):
                            if vv in fixed and fixed[vv] != bb:
                                return f"UNSAT_CROSS_PRIME_PAIR_R{rnd}", fixed, equiv, learned_2cls
                            if vv not in fixed:
                                fixed[vv] = bb
                                new_deduction = True
                    else:
                        for b1 in (0, 1):
                            for b2 in (0, 1):
                                if (b1, b2) not in valid_pairs:
                                    new_cl = [-v1 if b1 else v1, -v2 if b2 else v2]
                                    if new_cl not in work and [new_cl[1], new_cl[0]] not in work:
                                        work.append(new_cl)
                                        learned_2cls.append(new_cl)
                                        new_deduction = True
                        if p == 2:
                            short_gf2_xors.append(([v1, v2], rhs))
                elif p == 2 and len(vs) == 3:
                    short_gf2_xors.append((sorted(vs), rhs))

        if new_deduction:
            continue

        pair_idx: dict[tuple[int, int], int] = {}

        def get_pair(i: int, j: int) -> int:
            if i > j:
                i, j = j, i
            if (i, j) not in pair_idx:
                pair_idx[(i, j)] = n_vars + len(pair_idx)
            return pair_idx[(i, j)]

        for cl in work:
            if len(cl) == 3:
                vs = [abs(x) for x in cl]
                for a in range(len(vs)):
                    for b in range(a + 1, len(vs)):
                        get_pair(vs[a], vs[b])
        for vs, _ in short_gf2_xors:
            if len(vs) == 3:
                for a in range(len(vs)):
                    for b in range(a + 1, len(vs)):
                        get_pair(vs[a], vs[b])

        total_cols = n_vars + len(pair_idx)
        rows_dict: list[dict[int, float]] = []
        rhs_list: list[float] = []

        def add_le(terms: dict[int, float], rhs_val: float) -> None:
            rows_dict.append(terms)
            rhs_list.append(float(rhs_val))

        bounds = [(0.0, 1.0)] * total_cols
        for v, val in fixed.items():
            if 1 <= v <= n_vars:
                bounds[v - 1] = (float(val), float(val))

        for (i, j), pij in pair_idx.items():
            xi, xj = i - 1, j - 1
            add_le({pij: 1.0, xi: -1.0}, 0.0)
            add_le({pij: 1.0, xj: -1.0}, 0.0)
            add_le({xi: 1.0, xj: 1.0, pij: -1.0}, 1.0)

        def u_expr(lit: int) -> tuple[float, dict[int, float]]:
            v = abs(lit) - 1
            return (1.0, {v: -1.0}) if lit > 0 else (0.0, {v: 1.0})

        def val_expr(lit: int) -> tuple[float, dict[int, float]]:
            v = abs(lit) - 1
            return (0.0, {v: 1.0}) if lit > 0 else (1.0, {v: -1.0})

        def c_expr(l1: int, l2: int) -> tuple[float, dict[int, float]]:
            v1, v2 = abs(l1) - 1, abs(l2) - 1
            p12 = get_pair(abs(l1), abs(l2))
            if l1 < 0 and l2 < 0:
                return 0.0, {p12: 1.0}
            elif l1 < 0 and l2 > 0:
                return 0.0, {v1: 1.0, p12: -1.0}
            elif l1 > 0 and l2 < 0:
                return 0.0, {v2: 1.0, p12: -1.0}
            else:
                return 1.0, {v1: -1.0, v2: -1.0, p12: 1.0}

        conflict_adj: dict[int, set[int]] = defaultdict(set)
        guarded_adj: dict[int, dict[int, set[int]]] = defaultdict(lambda: defaultdict(set))
        pair_activity: dict[tuple[int, int], int] = defaultdict(int)

        for cl in work:
            if len(cl) == 2:
                a, b = -cl[0], -cl[1]
                conflict_adj[a].add(b)
                conflict_adj[b].add(a)
            elif len(cl) == 3:
                l0, l1, l2 = cl
                for pa, pb in ((l0, l1), (l0, l2), (l1, l2)):
                    pair_activity[tuple(sorted((pa, pb), key=lambda z: (abs(z), z)))] += 1  # type: ignore[index]
                for gi in range(3):
                    g_lit = cl[gi]
                    o1, o2 = -cl[(gi + 1) % 3], -cl[(gi + 2) % 3]
                    guarded_adj[g_lit][o1].add(o2)
                    guarded_adj[g_lit][o2].add(o1)

        seen_cliques = set()
        for seed_lit, nbrs in conflict_adj.items():
            clique = [seed_lit]
            for cand in sorted(nbrs, key=lambda z: -len(conflict_adj[z])):
                if all(cand in conflict_adj[m_lit] for m_lit in clique):
                    clique.append(cand)
            if len(clique) >= 3:
                key = tuple(sorted(clique))
                if key not in seen_cliques:
                    seen_cliques.add(key)
                    c_clk = 0.0
                    t_clk: dict[int, float] = defaultdict(float)
                    for lit in clique:
                        cv, dv = val_expr(lit)
                        c_clk += cv
                        for k, val_c in dv.items():
                            t_clk[k] += val_c
                    add_le(t_clk, 1.0 - c_clk)

        guard_vars_priority: set[int] = set()
        for g_lit, g_graph in guarded_adj.items():
            if len(g_graph) < 3:
                continue
            seen_g_cliques = set()
            for seed_lit, nbrs in list(g_graph.items()):
                if len(nbrs) < 2:
                    continue
                clique = [seed_lit]
                for cand in sorted(nbrs, key=lambda z: -len(g_graph[z])):
                    if all(cand in g_graph[m_lit] for m_lit in clique):
                        clique.append(cand)
                if len(clique) >= 3:
                    key = tuple(sorted(clique))
                    if key not in seen_g_cliques:
                        seen_g_cliques.add(key)
                        guard_vars_priority.add(abs(g_lit))
                        k_sz = len(clique)
                        cg, dg = val_expr(g_lit)
                        c_tot = -(k_sz - 1) * cg
                        t_tot: dict[int, float] = defaultdict(float)
                        for k, val_c in dg.items():
                            t_tot[k] -= (k_sz - 1) * val_c
                        for lit in clique:
                            cv, dv = val_expr(lit)
                            c_tot += cv
                            for k, val_c in dv.items():
                                t_tot[k] += val_c
                        add_le(t_tot, 1.0 - c_tot)

        for cl in work:
            if len(cl) == 2:
                cu1, du1 = u_expr(cl[0])
                cu2, du2 = u_expr(cl[1])
                t2c: dict[int, float] = defaultdict(float)
                for k, vc in du1.items():
                    t2c[k] += vc
                for k, vc in du2.items():
                    t2c[k] += vc
                add_le(t2c, 1.0 - (cu1 + cu2))
                a_lo, b_hi = sorted((abs(cl[0]), abs(cl[1])))
                if (a_lo, b_hi) in pair_idx:
                    cc, dc = c_expr(cl[0], cl[1])
                    add_le(dc, -cc)
            elif len(cl) == 3:
                l1, l2, l3 = cl
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
                add_le(t0, 1.0 - c0)

                c2 = -sum(u[0] for u in u_list) + 2.0 * (c12[0] + c13[0] + c23[0])
                t2: dict[int, float] = defaultdict(float)
                for _, d in u_list:
                    for k, val_c in d.items():
                        t2[k] -= val_c
                for _, d in (c12, c13, c23):
                    for k, val_c in d.items():
                        t2[k] += 2.0 * val_c
                add_le(t2, -c2)

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
                    add_le(tloc, -cloc)

        for vs, rhs in short_gf2_xors:
            if len(vs) == 3:
                v0, v1, v2 = vs[0] - 1, vs[1] - 1, vs[2] - 1
                p01, p02, p12 = get_pair(vs[0], vs[1]), get_pair(vs[0], vs[2]), get_pair(vs[1], vs[2])
                if rhs == 0:
                    add_le({v0: 1.0, v1: -1.0, v2: -1.0}, 0.0)
                    add_le({v0: -1.0, v1: 1.0, v2: -1.0}, 0.0)
                    add_le({v0: -1.0, v1: -1.0, v2: 1.0}, 0.0)
                    add_le({v0: 1.0, v1: 1.0, v2: 1.0}, 2.0)
                    add_le({v0: 1.0, v1: 1.0, v2: 1.0, p01: -2.0, p02: -2.0, p12: -2.0}, 0.0)
                else:
                    add_le({v0: -1.0, v1: -1.0, v2: -1.0}, -1.0)
                    add_le({v0: 1.0, v1: 1.0, v2: -1.0}, 1.0)
                    add_le({v0: 1.0, v1: -1.0, v2: 1.0}, 1.0)
                    add_le({v0: -1.0, v1: 1.0, v2: 1.0}, 1.0)
                    add_le({v0: -1.0, v1: -1.0, v2: -1.0, p01: -2.0, p02: 2.0, p12: 2.0}, -1.0)
                    add_le({v0: -1.0, v1: -1.0, v2: -1.0, p01: 2.0, p02: -2.0, p12: 2.0}, -1.0)
                    add_le({v0: -1.0, v1: -1.0, v2: -1.0, p01: 2.0, p02: 2.0, p12: -2.0}, -1.0)

        if not rows_dict:
            return "FEASIBLE", fixed, equiv, learned_2cls

        A_ub = lil_matrix((len(rows_dict), total_cols), dtype=np.float64)
        for i_r, d in enumerate(rows_dict):
            for col, val_c in d.items():
                if abs(val_c) > 1e-12:
                    A_ub[i_r, col] = val_c
        A_csc = A_ub.tocsc()
        b_ub = np.array(rhs_list, dtype=np.float64)

        res = linprog(np.zeros(total_cols), A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
        if not res.success:
            return f"UNSAT_OSTROWSKI_LP_R{rnd}", fixed, equiv, learned_2cls

        witness_xs = [res.x]

        deg_cnt: dict[int, int] = defaultdict(int)
        for cl in work:
            for lit in cl:
                deg_cnt[abs(lit)] += 1
        cand_vars = list(guard_vars_priority) + [
            v for v, _ in sorted(deg_cnt.items(), key=lambda kv: -kv[1]) if v not in guard_vars_priority
        ]
        max_cg = 6 if total_cols > 12000 else 28
        cand_vars = [v for v in cand_vars if 1 <= v <= n_vars and v not in fixed][:max_cg]

        cg_progressed = False
        for v in cand_vars:
            col_v = v - 1
            if not any(wx[col_v] <= 1e-6 for wx in witness_xs):
                c_obj = np.zeros(total_cols)
                c_obj[col_v] = 1.0
                r_lo = linprog(c_obj, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
                if r_lo.success:
                    if r_lo.fun > 1e-6:
                        fixed[v] = 1
                        cg_progressed = True
                        break
                    witness_xs.append(r_lo.x)
            if not any(wx[col_v] >= 1.0 - 1e-6 for wx in witness_xs):
                c_obj = np.zeros(total_cols)
                c_obj[col_v] = -1.0
                r_hi = linprog(c_obj, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
                if r_hi.success:
                    if (-r_hi.fun) < 1.0 - 1e-6:
                        fixed[v] = 0
                        cg_progressed = True
                        break
                    witness_xs.append(r_hi.x)

        if cg_progressed:
            continue

        if total_cols <= 6000:
            cl2_existing = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in work if len(c) == 2}
            top_pairs = [
                pr for pr, cnt in sorted(pair_activity.items(), key=lambda kv: -kv[1])
                if cnt >= 2 and pr not in cl2_existing and abs(pr[0]) not in fixed and abs(pr[1]) not in fixed
            ][:8]

            for l1, l2 in top_pairs:
                c_const, c_dict = c_expr(l1, l2)
                if any((c_const + sum(cv * wx[ci] for ci, cv in c_dict.items())) >= 1.0 - 1e-5 for wx in witness_xs):
                    continue
                c_obj = np.zeros(total_cols)
                for col_i, coeff_v in c_dict.items():
                    c_obj[col_i] = -coeff_v
                r_c = linprog(c_obj, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
                if r_c.success:
                    if (c_const - r_c.fun) < 1.0 - 1e-5:
                        ncl = sorted([l1, l2], key=lambda z: (abs(z), z))
                        work.append(ncl)
                        learned_2cls.append(ncl)
                        cg_progressed = True
                        break
                    witness_xs.append(r_c.x)

            if not cg_progressed:
                top_var_pairs = sorted(
                    pair_idx.keys(),
                    key=lambda ij: -(deg_cnt[ij[0]] + deg_cnt[ij[1]]),
                )
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
                                equiv[vj] = (vi, 1)
                                work.extend([[-vi, -vj], [vi, vj]])
                                learned_2cls.extend([[-vi, -vj], [vi, vj]])
                                cg_progressed = True
                                break
                            witness_xs.append(r_xlo.x)
                    if not any((wx[vi - 1] + wx[vj - 1] - 2.0 * wx[pij]) >= 1.0 - 1e-5 for wx in witness_xs):
                        c_xor = np.zeros(total_cols)
                        c_xor[vi - 1] = -1.0
                        c_xor[vj - 1] = -1.0
                        c_xor[pij] = 2.0
                        r_xhi = linprog(c_xor, A_ub=A_csc, b_ub=b_ub, bounds=bounds, method="highs")
                        if r_xhi.success:
                            if (-r_xhi.fun) < 1.0 - 1e-5:
                                equiv[vj] = (vi, 0)
                                work.extend([[-vi, vj], [vi, -vj]])
                                learned_2cls.extend([[-vi, vj], [vi, -vj]])
                                cg_progressed = True
                                break
                            witness_xs.append(r_xhi.x)

        if not cg_progressed:
            return "FEASIBLE", fixed, equiv, learned_2cls

    return "FEASIBLE", fixed, equiv, learned_2cls


def vertex_cut_interpolant_refute(
    clauses: list[list[int]],
    max_rm_deg: int = 4,
    max_mac_deg: int = 3,
    max_cut: int = 6,
) -> tuple[str, dict[int, int]]:
    """Exact O(|V|^2) primal graph separator decomposition for wire-eliminated disjunctive interpolants."""
    unrolled = fast_unroll_11_chains(clauses)
    if len(unrolled) < 6:
        return "NONE", {}

    adj: dict[int, set[int]] = defaultdict(set)
    all_v: set[int] = set()
    for c in unrolled:
        vs = [abs(l) for l in c]
        all_v.update(vs)
        for i in range(len(vs)):
            ui = vs[i]
            for j in range(i + 1, len(vs)):
                vj = vs[j]
                adj[ui].add(vj)
                adj[vj].add(ui)

    v_list = sorted(all_v)
    if len(v_list) < 8 or len(v_list) > 400:
        return "NONE", {}

    found_cut = None
    found_comps = None
    tested_cuts = set()

    for i in range(len(v_list)):
        u = v_list[i]
        nu = adj[u]
        if len(nu) >= len(v_list) - 1:
            continue
        for j in range(i + 1, len(v_list)):
            v = v_list[j]
            if v in nu:
                continue
            s_cand = frozenset(nu & adj[v])
            if not (1 <= len(s_cand) <= max_cut) or s_cand in tested_cuts:
                continue
            tested_cuts.add(s_cand)
            rem_vars = all_v - s_cand
            if len(rem_vars) < 4:
                continue
            visited = set()
            comps = []
            for start_node in rem_vars:
                if start_node in visited:
                    continue
                comp = set()
                queue = [start_node]
                visited.add(start_node)
                while queue:
                    cur = queue.pop()
                    comp.add(cur)
                    for nb in adj[cur]:
                        if nb not in s_cand and nb not in visited:
                            visited.add(nb)
                            queue.append(nb)
                comps.append(comp)
            if len(comps) >= 2 and sum(1 for cp in comps if len(cp) >= 3) >= 2:
                found_cut = sorted(s_cand)
                found_comps = comps
                break
        if found_cut is not None:
            break

    if found_cut is None or found_comps is None:
        return "NONE", {}

    cut_set = set(found_cut)
    pure_s_clauses = []
    comp_clauses: list[list[list[int]]] = [[] for _ in range(len(found_comps))]
    var_to_cidx = {v: idx for idx, cp in enumerate(found_comps) for v in cp}

    for c in unrolled:
        c_idxs = {var_to_cidx[abs(l)] for l in c if abs(l) not in cut_set}
        if not c_idxs:
            pure_s_clauses.append(c)
        elif len(c_idxs) == 1:
            comp_clauses[next(iter(c_idxs))].append(c)

    sub_verdict_cache: dict[frozenset[tuple[int, ...]], tuple[bool, str]] = {}

    def is_subformula_unsat(proj_cls: list[list[int]]) -> tuple[bool, str]:
        key = frozenset(tuple(sorted(c, key=lambda z: (abs(z), z))) for c in proj_cls)
        if not key:
            return False, "SAT_EMPTY"
        if key in sub_verdict_cache:
            return sub_verdict_cache[key]
        resplit = []
        tv = max(abs(x) for c in proj_cls for x in c)
        for c in proj_cls:
            lits = list(c)
            while len(lits) > 3:
                tv += 1
                resplit.append([lits[0], lits[1], tv])
                lits = [-tv] + lits[2:]
            resplit.append(lits)
        n_sub, c_sub = compact_active_cnf(resplit)
        verd_sub, _, _ = solve_hybrid_preproc(
            n_sub, c_sub, max_rm_deg=max_rm_deg, max_mac_deg=max_mac_deg, allow_lift1=False, _allow_cut=False
        )
        is_u = not verd_sub.startswith("FEASIBLE")
        sub_verdict_cache[key] = (is_u, verd_sub)
        return is_u, verd_sub

    reasons: set[str] = set()
    for bits in itertools.product((0, 1), repeat=len(found_cut)):
        s_map = dict(zip(found_cut, bits))
        if any(not any((s_map[abs(l)] == 1 if l > 0 else s_map[abs(l)] == 0) for l in sc) for sc in pure_s_clauses):
            continue
        fiber_refuted = False
        for c_list in comp_clauses:
            if not c_list:
                continue
            proj = []
            immediate_unsat = False
            for cl in c_list:
                sat_by_s = False
                rem_lits = []
                for l in cl:
                    av = abs(l)
                    if av in cut_set:
                        if (l > 0 and s_map[av] == 1) or (l < 0 and s_map[av] == 0):
                            sat_by_s = True
                            break
                    else:
                        rem_lits.append(l)
                if sat_by_s:
                    continue
                if not rem_lits:
                    immediate_unsat = True
                    break
                proj.append(rem_lits)
            if immediate_unsat:
                fiber_refuted = True
                break
            u_ok, v_tag = is_subformula_unsat(proj)
            if u_ok:
                reasons.add(v_tag.split()[0])
                fiber_refuted = True
                break
        if not fiber_refuted:
            return "FEASIBLE_CUT", {}

    r_str = "+".join(sorted(reasons))
    return f"UNSAT_VERTEX_CUT(|S|={len(found_cut)}:{r_str})", {}


def solve_hybrid_preproc(
    n_vars: int,
    clauses: list[list[int]],
    max_rm_deg: int = 4,
    max_mac_deg: int = 3,
    allow_lift1: bool = False,
    _allow_cut: bool = True,
) -> tuple[str, str, dict[int, int] | None]:
    """
    Unified zero-branch preprocessor & refutation engine:
      1) Blind arithmetic adder telescoping + 2-adic/GCD bit-peeling.
      2) Blind functional root-DAG evaluation (R_root <= 16).
      2b) Unrolled (1,1)-chain degree-absorbing Macaulay pre-pass on <= 48 active vars.
      3) Primal vertex-cut decomposition for wire-eliminated disjunctive interpolants.
      4) Dual Veronese RM(d, n) annihilator synthesis + polar biclique factorization.
      5) Monotone coupled sparse Macaulay <-> modular/guarded cutting-planes LP loop.
    """
    st_w, fix_w, eq_w, _ = blind_adder_telescoping_engine(clauses)
    if st_w.startswith("UNSAT_"):
        return f"{st_w} [AdderZ]", "LVL0", None
    if st_w == "OK_EMPTY":
        return "FEASIBLE [AdderZ_solved]", "LVL0", fix_w

    st_dag, dag_model = blind_functional_root_dag_solve(
        clauses, fixed_init=fix_w, equiv_init=eq_w, max_roots=16
    )
    if st_dag.startswith("UNSAT_"):
        return st_dag, "LVL0", None
    if st_dag.startswith("SAT_"):
        return f"FEASIBLE [{st_dag}]", "LVL0", dag_model

    if max_mac_deg >= 2:
        unr_pre = fast_unroll_11_chains(clauses)
        if any(len(c) >= 4 for c in unr_pre):
            st_pre, fix_pre, _, red_pre = degree_absorbing_macaulay_cascade(
                clauses, max_deg=max_mac_deg, max_rounds=5, max_active_vars=48
            )
            if st_pre != "OK":
                return f"{st_pre}_PRE [act<=48]", "LVL0", fix_pre
            if not red_pre:
                return f"FEASIBLE [mac_solved,units={len(fix_pre)}]", "LVL0", fix_pre

    if _allow_cut:
        st_cut, _ = vertex_cut_interpolant_refute(
            clauses, max_rm_deg=max_rm_deg, max_mac_deg=max_mac_deg, max_cut=6
        )
        if st_cut.startswith("UNSAT_"):
            return st_cut, "LVL0", None

    nv_ef, cls_ef, rmc, ns, nm = synthesize_ef_extensions(n_vars, clauses, max_rm_deg=max_rm_deg)
    rm_str = ",".join(f"rm{k}={v}" for k, v in sorted(rmc.items())) if rmc else "rm=0"
    tag = f"[{rm_str},syn={ns},merge={nm},act={nv_ef}]"

    if nv_ef > 500:
        st_big, _, _, _ = guarded_cutting_planes_lp(nv_ef, cls_ef[:650], max_rounds=1)
        return f"{st_big} {tag}", "LVL0", None

    st_bve0, _, cls_ef = simplify_and_bve(nv_ef, cls_ef, {})
    if st_bve0 != "OK":
        return f"{st_bve0}_INIT {tag}", "LVL0", None
    if not cls_ef:
        return f"FEASIBLE [bve_solved] {tag}", "LVL0", {}

    base_cls_set = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in cls_ef}

    fixed: dict[int, int] = {}
    equiv: dict[int, tuple[int, int]] = {}
    work_cls = [list(c) for c in cls_ef]

    for pp_rnd in range(1, 5):
        prev_sig = (len(fixed), len(equiv))

        if max_mac_deg >= 2:
            st_mac, work_cls = diamond_petal_sparse_macaulay(
                work_cls,
                fixed,
                equiv,
                max_deg=max_mac_deg,
                max_diamond_3cls=2400,
                max_mac_vars=160,
            )
            if st_mac != "OK":
                return f"{st_mac}_PP{pp_rnd} {tag}", "LVL0", None
            if not work_cls:
                return f"FEASIBLE [smac_solved] {tag}", "LVL0", fixed

        cls_le2 = [c for c in work_cls if len(c) <= 2]
        cls_eq3 = [c for c in work_cls if len(c) == 3]
        cap_3lp = max(520, len(base_cls_set))
        if len(cls_eq3) > cap_3lp:
            supp_freq: dict[tuple[int, ...], int] = defaultdict(int)
            for c in cls_eq3:
                supp_freq[tuple(sorted(abs(x) for x in c))] += 1
            cls_eq3_sorted = sorted(
                cls_eq3,
                key=lambda c: (
                    0 if tuple(sorted(c, key=lambda z: (abs(z), z))) in base_cls_set else 1,
                    -supp_freq[tuple(sorted(abs(x) for x in c))],
                ),
            )
            lp_cls = cls_le2 + cls_eq3_sorted[:cap_3lp]
        else:
            lp_cls = cls_le2 + cls_eq3

        st_ad, fixed_ad, equiv_ad, learned_2 = guarded_cutting_planes_lp(
            nv_ef, lp_cls, fixed_init=fixed, equiv_init=equiv, max_rounds=3
        )
        if st_ad != "FEASIBLE":
            return f"{st_ad}_PP{pp_rnd} {tag}", "LVL0", None

        fixed.update(fixed_ad)
        for u_v, val_eq in equiv_ad.items():
            if u_v not in fixed and u_v not in equiv:
                equiv[u_v] = val_eq
        if learned_2:
            existing = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in work_cls}
            for c2 in learned_2:
                tc2 = tuple(sorted(c2, key=lambda z: (abs(z), z)))
                if tc2 not in existing:
                    existing.add(tc2)
                    work_cls.append(list(tc2))

        if (len(fixed), len(equiv)) == prev_sig and not learned_2:
            break

    if not allow_lift1:
        return f"FEASIBLE {tag}", "LVL0", fixed

    deg: dict[int, int] = defaultdict(int)
    for c in work_cls:
        for l in c:
            deg[abs(l)] += 1
    order_vars = [v for v, _ in sorted(deg.items(), key=lambda kv: -kv[1]) if v <= nv_ef and v not in fixed]
    for v in order_vars:
        v0, _, _ = solve_hybrid_preproc(nv_ef, work_cls + [[-v]], max_rm_deg=0, max_mac_deg=max_mac_deg, allow_lift1=False)
        v1, _, _ = solve_hybrid_preproc(nv_ef, work_cls + [[v]], max_rm_deg=0, max_mac_deg=max_mac_deg, allow_lift1=False)
        if not v0.startswith("FEASIBLE") and not v1.startswith("FEASIBLE"):
            return f"UNSAT_LIFT1(v={v}) {tag}", "LIFT1", None
    return f"FEASIBLE_LIFT1 {tag}", "LIFT1", fixed
