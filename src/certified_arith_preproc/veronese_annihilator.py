"""Dual Reed-Muller RM(d, n) Veronese annihilator synthesis and Boolean derivative syzygy collapse."""

from __future__ import annotations

import itertools
from collections import defaultdict

from .cnf_utils import (
    VAR_TT_CACHE,
    compact_active_cnf,
    fast_unroll_11_chains,
    gf2_in_span,
    gf2_vec_rref,
    prime_cnf_of_mask,
    truth_mask_on_vars,
)


def fast_project_mask(basis_vecs: list[int], allowed_mask: int) -> list[int]:
    """Project `basis_vecs` onto coordinates active in `allowed_mask` via O(1) bitwise Gaussian elimination."""
    outside_pivots: dict[int, int] = {}
    projected: list[int] = []
    for vec in basis_vecs:
        cur = int(vec)
        while cur:
            out_part = cur & ~allowed_mask
            if not out_part:
                projected.append(cur)
                break
            msb = out_part.bit_length() - 1
            if msb in outside_pivots:
                cur ^= outside_pivots[msb]
            else:
                outside_pivots[msb] = cur
                break
    return gf2_vec_rref(projected) if projected else []


def zassenhaus_intersect(p1: list[int], p2: list[int]) -> list[int]:
    """Exact subspace intersection span(p1) cap span(p2) in O((|p1| + |p2|)^2)."""
    pivots: dict[int, tuple[int, int]] = {}
    inter_raw: list[int] = []
    for v in p1:
        cur = int(v)
        p1_part = int(v)
        while cur:
            msb = cur.bit_length() - 1
            if msb in pivots:
                pv, pp1 = pivots[msb]
                cur ^= pv
                p1_part ^= pp1
            else:
                pivots[msb] = (cur, p1_part)
                break
    for v in p2:
        cur = int(v)
        p1_part = 0
        while cur:
            msb = cur.bit_length() - 1
            if msb in pivots:
                pv, pp1 = pivots[msb]
                cur ^= pv
                p1_part ^= pp1
            else:
                pivots[msb] = (cur, p1_part)
                break
        else:
            if p1_part:
                inter_raw.append(p1_part)
    return gf2_vec_rref(inter_raw) if inter_raw else []


def substitute_known_gadget_globally(
    clause_sets: list[frozenset[int]],
    dom_t: tuple[int, ...],
    pos_clauses_tuple: tuple[tuple[int, ...], ...],
    neg_clauses_tuple: tuple[tuple[int, ...], ...] | None,
    g_lit: int,
) -> tuple[list[frozenset[int]], int]:
    """Substitute occurrences of both a synthesized gadget and its Boolean complement across `clause_sets`."""
    dom_set = set(dom_t)
    pos_set = set(pos_clauses_tuple)
    neg_set = set(neg_clauses_tuple) if neg_clauses_tuple is not None else None

    beta_to_alphas: dict[frozenset[int], set[tuple[int, ...]]] = defaultdict(set)
    for cs in clause_sets:
        in_dom = [l for l in cs if abs(l) in dom_set]
        if in_dom and len(in_dom) < len(cs):
            beta = frozenset(l for l in cs if abs(l) not in dom_set)
            if g_lit in beta or -g_lit in beta:
                continue
            al_t = tuple(sorted(in_dom, key=lambda z: (abs(z), z)))
            beta_to_alphas[beta].add(al_t)

    to_remove: set[frozenset[int]] = set()
    to_add: list[frozenset[int]] = []
    comp_hits = 0

    for beta, al_found in beta_to_alphas.items():
        if pos_set.issubset(al_found):
            for al in pos_set:
                to_remove.add(frozenset(al) | beta)
            to_add.append(beta | {g_lit})
        if neg_set is not None and neg_set.issubset(al_found):
            for al in neg_set:
                to_remove.add(frozenset(al) | beta)
            to_add.append(beta | {-g_lit})
            comp_hits += 1

    if not to_remove:
        return clause_sets, 0

    existing = set(clause_sets) - to_remove
    out = [cs for cs in clause_sets if cs not in to_remove]
    for nc in to_add:
        if not any(-x in nc for x in nc) and nc not in existing:
            existing.add(nc)
            out.append(nc)
    return out, comp_hits


def synthesize_veronese_rm_d(
    top_var: int,
    clause_sets: list[frozenset[int]],
    deg_d: int,
    max_supp: int = 12,
    max_extract_supp: int = 12,
    shared_monom_wire: dict[tuple[int, ...], int] | None = None,
) -> tuple[int, list[frozenset[int]], int]:
    """
    Synthesize auxiliary extension variables via degree-d Veronese RM(d, n) dual annihilators,
    Boolean derivative syzygy collapse (dP/du == 1), and codimension-1 hypersurface extraction.
    """
    if shared_monom_wire is None:
        shared_monom_wire = {}

    min_len = 4
    by_supp: dict[tuple[int, ...], list[frozenset[int]]] = defaultdict(list)
    for cs in clause_sets:
        if min_len <= len(cs) <= max_supp:
            supp = tuple(sorted(abs(l) for l in cs))
            if len(supp) == len(cs):
                by_supp[supp].append(cs)

    all_cand_supps = sorted(
        [supp for supp, cl_l in by_supp.items() if 2 <= len(cl_l) < (1 << len(supp))],
        key=lambda s: len(s),
    )
    cand_supps = [s for s in all_cand_supps if len(s) <= max_extract_supp]
    if not cand_supps:
        return top_var, clause_sets, 0

    all_vars = sorted({v for supp in all_cand_supps for v in supp})
    if len(all_vars) > 100:
        return top_var, clause_sets, 0

    monom_set: set[tuple[int, ...]] = set()
    supp_vmonoms: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    for supp in cand_supps:
        mlist = [
            comb
            for r in range(1, min(deg_d, len(supp)) + 1)
            for comb in itertools.combinations(supp, r)
        ]
        monom_set.update(mlist)
        supp_vmonoms[supp] = mlist

    coord_to_monom = sorted(monom_set, key=lambda m: (len(m), m))
    monom_to_coord = {m: idx for idx, m in enumerate(coord_to_monom)}

    higher_coords_with_var: dict[int, list[int]] = defaultdict(list)
    unit_coord_of_var: dict[int, int] = {}
    for idx, m in enumerate(coord_to_monom):
        if len(m) == 1:
            unit_coord_of_var[m[0]] = idx
        else:
            for v in m:
                higher_coords_with_var[v].append(idx)
    higher_mask_with_var = {v: sum(1 << c for c in cs) for v, cs in higher_coords_with_var.items()}

    ray_vars_cache: dict[int, tuple[int, ...]] = {}

    def vars_of_ray(ry: int) -> tuple[int, ...]:
        if ry not in ray_vars_cache:
            vs: set[int] = set()
            tmp = int(ry)
            while tmp:
                b = tmp.bit_length() - 1
                vs.update(coord_to_monom[b])
                tmp ^= (1 << b)
            ray_vars_cache[ry] = tuple(sorted(vs))
        return ray_vars_cache[ry]

    def is_balanced_ray_fast(ry: int) -> bool:
        vs = vars_of_ray(ry)
        kv = len(vs)
        if kv == 0 or kv > 12:
            return False
        v_pos = {v: j for j, v in enumerate(vs)}
        v_tts = VAR_TT_CACHE[kv]
        poly_tt = 0
        tmp = int(ry)
        while tmp:
            b = tmp.bit_length() - 1
            m = coord_to_monom[b]
            m_tt = v_tts[v_pos[m[0]]]
            for mv in m[1:]:
                m_tt &= v_tts[v_pos[mv]]
            poly_tt ^= m_tt
            tmp ^= (1 << b)
        return poly_tt.bit_count() == (1 << (kv - 1))

    rm_blocks = []
    codim1_exact_rays: set[int] = set()

    for supp in cand_supps:
        cl_list = by_supp[supp]
        k = len(supp)
        all_ones = (1 << (1 << k)) - 1
        pos_in_supp = {v: j for j, v in enumerate(supp)}

        bad_mask = 0
        b0_idx = -1
        n_bad = 0
        for cs in cl_list:
            row_idx = sum((1 << (k - 1 - pos_in_supp[abs(l)])) for l in cs if l < 0)
            bit = 1 << row_idx
            if not (bad_mask & bit):
                bad_mask |= bit
                n_bad += 1
                if b0_idx == -1 or row_idx < b0_idx:
                    b0_idx = row_idx

        if n_bad < 2 or n_bad >= (1 << k):
            continue

        var_tts = VAR_TT_CACHE[k]
        vcoords = [monom_to_coord[m] for m in supp_vmonoms[supp]]

        sub_tt: dict[tuple[int, ...], int] = {}
        local_coord_tt: dict[int, int] = {}
        for j, v in enumerate(supp):
            t_v = var_tts[j]
            sub_tt[(v,)] = t_v
            local_coord_tt[monom_to_coord[(v,)]] = t_v
        for m in supp_vmonoms[supp]:
            if len(m) >= 2:
                t_m = sub_tt[m[:-1]] & sub_tt[(m[-1],)]
                sub_tt[m] = t_m
                local_coord_tt[monom_to_coord[m]] = t_m

        rest_bad = bad_mask ^ (1 << b0_idx)
        pivots: dict[int, tuple[int, int]] = {}
        u_raw: list[int] = []
        for c in vcoords:
            tt_c = local_coord_tt[c]
            c0 = (tt_c >> b0_idx) & 1
            vec = ((tt_c ^ all_ones) if c0 else tt_c) & rest_bad
            comb = 1 << c
            while vec:
                msb = vec.bit_length() - 1
                if msb in pivots:
                    p_vec, p_comb = pivots[msb]
                    vec ^= p_vec
                    comb ^= p_comb
                else:
                    pivots[msb] = (vec, comb)
                    break
            else:
                u_raw.append(comb)

        if not u_raw:
            continue
        u_basis = gf2_vec_rref(u_raw)

        def eval_local_tt(poly_mask: int) -> int:
            att = 0
            tmp = int(poly_mask)
            while tmp:
                b = tmp.bit_length() - 1
                att ^= local_coord_tt[b]
                tmp ^= (1 << b)
            return att

        locus = all_ones
        for alpha in u_basis:
            att = eval_local_tt(alpha)
            c0 = (att >> b0_idx) & 1
            locus &= (att if c0 else (att ^ all_ones))
            if locus == bad_mask:
                break

        if locus == bad_mask:
            vc_mask = sum(1 << c for c in vcoords)
            rm_blocks.append((supp, cl_list, bad_mask, b0_idx, u_basis, local_coord_tt, vc_mask))
            if n_bad == (1 << (k - 1)):
                if len(u_basis) == 1:
                    codim1_exact_rays.add(u_basis[0])
                else:
                    best_c1 = None
                    for u_var in supp:
                        u_unit = unit_coord_of_var.get(u_var, -1)
                        if u_unit == -1:
                            continue
                        allowed_m = vc_mask & ~higher_mask_with_var.get(u_var, 0)
                        proj_u = fast_project_mask(u_basis, allowed_m)
                        if len(proj_u) == 1:
                            cand = proj_u[0]
                            att = eval_local_tt(cand)
                            c0 = (att >> b0_idx) & 1
                            if (att if c0 else (att ^ all_ones)) == bad_mask:
                                if best_c1 is None or cand.bit_count() < best_c1.bit_count():
                                    best_c1 = cand
                    if best_c1 is not None:
                        codim1_exact_rays.add(best_c1)
        elif deg_d >= 2 and len(rm_blocks) == 0 and supp == cand_supps[0] and len(cand_supps) >= 6:
            return top_var, clause_sets, 0

    if not rm_blocks:
        return top_var, clause_sets, 0

    proj_cache: dict[tuple[int, int], list[int]] = {}

    def get_projected(blk_id: int, b_vecs: list[int], target_vc_mask: int) -> list[int]:
        key = (blk_id, target_vc_mask)
        if key not in proj_cache:
            proj_cache[key] = fast_project_mask(b_vecs, target_vc_mask)
        return proj_cache[key]

    rays: set[int] = set(codim1_exact_rays)

    def extract_rays_from_subspace(inter: list[int], c_mask: int, s_vars: list[int]) -> None:
        if len(inter) == 1:
            rays.add(inter[0])
            return
        if deg_d >= 2:
            for u_var in s_vars:
                u_unit = unit_coord_of_var.get(u_var, -1)
                if u_unit == -1 or not ((c_mask >> u_unit) & 1):
                    continue
                allowed_m = c_mask & ~higher_mask_with_var.get(u_var, 0)
                proj_u = fast_project_mask(inter, allowed_m)
                if len(proj_u) == 1:
                    cand = proj_u[0]
                    if ((cand >> u_unit) & 1) and is_balanced_ray_fast(cand):
                        rays.add(cand)
                elif 2 <= len(proj_u) <= 4:
                    best_cand = None
                    best_key = (999, 999)
                    tie = False
                    for mask_c in range(1, 1 << len(proj_u)):
                        vc = 0
                        for bi, bv in enumerate(proj_u):
                            if (mask_c >> bi) & 1:
                                vc ^= bv
                        if ((vc >> u_unit) & 1) and is_balanced_ray_fast(vc):
                            k_c = (len(vars_of_ray(vc)), vc.bit_count())
                            if k_c < best_key:
                                best_key = k_c
                                best_cand = vc
                                tie = False
                            elif k_c == best_key and vc != best_cand:
                                tie = True
                    if best_cand is not None and not tie:
                        rays.add(best_cand)

    def all_blocks_covered_now() -> bool:
        valid_r = [
            r for r in rays
            if r in codim1_exact_rays
            or sum(1 for _, _, _, _, ub, _, vm in rm_blocks if (r & ~vm) == 0 and gf2_in_span(r, ub)) >= 2
        ]
        if not valid_r:
            return False
        for supp, _, bad_mask, b0_idx, u_basis, local_coord_tt, vc_mask in rm_blocks:
            k = len(supp)
            all_ones = (1 << (1 << k)) - 1
            loc = all_ones
            for ry in valid_r:
                if (ry & ~vc_mask) == 0 and gf2_in_span(ry, u_basis):
                    att = 0
                    tmp = int(ry)
                    while tmp:
                        b = tmp.bit_length() - 1
                        att ^= local_coord_tt[b]
                        tmp ^= (1 << b)
                    c0 = (att >> b0_idx) & 1
                    loc &= (att if c0 else (att ^ all_ones))
                    if loc == bad_mask:
                        break
            if loc != bad_mask:
                return False
        return True

    if len(rm_blocks) >= 2 and not all_blocks_covered_now():
        base_pool = [(idx, frozenset(supp), ui, vc_m) for idx, (supp, _, _, _, ui, _, vc_m) in enumerate(rm_blocks)]
        frontier = []
        seen_subspaces: set[tuple[int, ...]] = set()

        n_b = len(base_pool)
        for i in range(n_b):
            id1, s1, b1, vm1 = base_pool[i]
            for j in range(i + 1, n_b):
                id2, s2, b2, vm2 = base_pool[j]
                s_inter = s1 & s2
                if len(s_inter) < 2:
                    continue
                c_mask = vm1 & vm2
                if c_mask.bit_count() < 2:
                    continue
                p1 = get_projected(id1, b1, c_mask)
                if not p1:
                    continue
                p2 = get_projected(id2, b2, c_mask)
                if not p2:
                    continue
                inter = zassenhaus_intersect(p1, p2)
                if not inter:
                    continue
                t_in = tuple(inter)
                if t_in not in seen_subspaces:
                    seen_subspaces.add(t_in)
                    extract_rays_from_subspace(inter, c_mask, sorted(s_inter))
                    if len(inter) >= 2 and len(s_inter) > 2:
                        frontier.append((s_inter, inter, c_mask))

        frontier.sort(key=lambda item: (len(item[0]), len(item[1])))
        for _depth in range(2):
            if not frontier or all_blocks_covered_now():
                break
            next_frontier = []
            for s_cur, cur_b, cur_vm in frontier[:180]:
                for id2, s2, b2, vm2 in base_pool:
                    s_inter = s_cur & s2
                    if len(s_inter) < 2 or len(s_inter) == len(s_cur):
                        continue
                    c_mask = cur_vm & vm2
                    if c_mask.bit_count() < 2:
                        continue
                    p1 = fast_project_mask(cur_b, c_mask)
                    if not p1:
                        continue
                    p2 = get_projected(id2, b2, c_mask)
                    if not p2:
                        continue
                    inter = zassenhaus_intersect(p1, p2)
                    if not inter:
                        continue
                    t_in = tuple(inter)
                    if t_in not in seen_subspaces:
                        seen_subspaces.add(t_in)
                        extract_rays_from_subspace(inter, c_mask, sorted(s_inter))
                        if len(inter) >= 2 and len(s_inter) > deg_d + 1 and len(seen_subspaces) < 600:
                            next_frontier.append((s_inter, inter, c_mask))
            if not next_frontier:
                break
            next_frontier.sort(key=lambda item: (len(item[0]), len(item[1])))
            frontier = next_frontier

        if deg_d == 1:
            changed_peel = True
            while changed_peel:
                changed_peel = False
                for _, _, _, _, u_basis, _, vc_mask in rm_blocks:
                    in_u = [ry for ry in rays if (ry & ~vc_mask) == 0 and gf2_in_span(ry, u_basis)]
                    r_in = gf2_vec_rref(in_u)
                    if len(r_in) == len(u_basis) - 1:
                        for cand in u_basis:
                            if not gf2_in_span(cand, r_in):
                                rays.add(cand)
                                changed_peel = True
                                break

    if not rays:
        return top_var, clause_sets, 0

    ray_hits: dict[int, int] = {}
    for ry in rays:
        hits = sum(
            1 for _, _, _, _, ub, _, vm in rm_blocks
            if (ry & ~vm) == 0 and gf2_in_span(ry, ub)
        )
        if hits >= 2 or ry in codim1_exact_rays:
            ray_hits[ry] = hits

    shared_rays = set(ray_hits.keys()) if ray_hits else rays

    sorted_raw = sorted(shared_rays, key=lambda r: (len(vars_of_ray(r)), r.bit_count()))
    atomic_rays: list[int] = []
    for r in sorted_raw:
        if r in codim1_exact_rays:
            atomic_rays.append(r)
            continue
        rv_len = len(vars_of_ray(r))
        smaller_basis = gf2_vec_rref([ar for ar in atomic_rays if len(vars_of_ray(ar)) < rv_len])
        if not gf2_in_span(r, smaller_basis):
            atomic_rays.append(r)

    ray_to_wire: dict[int, int] = {}
    new_clauses: list[frozenset[int]] = []
    clauses_to_remove: set[frozenset[int]] = set()
    rewritten = 0

    def get_monom_wire(monom: tuple[int, ...]) -> int:
        nonlocal top_var
        if len(monom) == 1:
            return monom[0]
        if monom not in shared_monom_wire:
            prev_w = get_monom_wire(monom[:-1])
            last_v = monom[-1]
            top_var += 1
            y_var = top_var
            shared_monom_wire[monom] = y_var
            new_clauses.extend([
                frozenset({-y_var, prev_w}),
                frozenset({-y_var, last_v}),
                frozenset({y_var, -prev_w, -last_v}),
            ])
        return shared_monom_wire[monom]

    def get_ray_wire(ry: int) -> int:
        nonlocal top_var
        if ry in ray_to_wire:
            return ray_to_wire[ry]
        top_var += 1
        w_var = top_var
        ray_to_wire[ry] = w_var

        m_wires = []
        tmp = int(ry)
        while tmp:
            b = tmp.bit_length() - 1
            m_wires.append(get_monom_wire(coord_to_monom[b]))
            tmp ^= (1 << b)

        if len(m_wires) == 1:
            mw = m_wires[0]
            new_clauses.extend([frozenset({-w_var, mw}), frozenset({w_var, -mw})])
        else:
            cur_x = m_wires[0]
            for nxt_m in m_wires[1:-1]:
                top_var += 1
                mid = top_var
                new_clauses.extend([
                    frozenset({-cur_x, -nxt_m, -mid}),
                    frozenset({cur_x, nxt_m, -mid}),
                    frozenset({-cur_x, nxt_m, mid}),
                    frozenset({cur_x, -nxt_m, mid}),
                ])
                cur_x = mid
            last_m = m_wires[-1]
            new_clauses.extend([
                frozenset({-cur_x, -last_m, -w_var}),
                frozenset({cur_x, last_m, -w_var}),
                frozenset({-cur_x, last_m, w_var}),
                frozenset({cur_x, -last_m, w_var}),
            ])
        return w_var

    sorted_rays = sorted(atomic_rays, key=lambda r: (len(vars_of_ray(r)), -ray_hits.get(r, 1), r.bit_count()))
    ray_var_sets = [(ry, set(vars_of_ray(ry))) for ry in sorted_rays]

    def eval_ray_on_supp(ry: int, supp_pos: dict[int, int], k_len: int) -> int:
        v_tts = VAR_TT_CACHE[k_len]
        att = 0
        tmp = int(ry)
        while tmp:
            b = tmp.bit_length() - 1
            m = coord_to_monom[b]
            m_tt = v_tts[supp_pos[m[0]]]
            for mv in m[1:]:
                m_tt &= v_tts[supp_pos[mv]]
            att ^= m_tt
            tmp ^= (1 << b)
        return att

    for supp in sorted(all_cand_supps, key=lambda s: -len(s)):
        cl_list = by_supp[supp]
        k = len(supp)
        supp_set = set(supp)
        in_supp_rays = [ry for ry, rvs in ray_var_sets if rvs.issubset(supp_set)]
        if not in_supp_rays:
            continue

        all_ones = (1 << (1 << k)) - 1
        pos_in_supp = {v: j for j, v in enumerate(supp)}
        bad_mask = 0
        for cs in cl_list:
            row_idx = sum((1 << (k - 1 - pos_in_supp[abs(l)])) for l in cs if l < 0)
            bad_mask |= (1 << row_idx)
        if bad_mask == 0 or bad_mask == all_ones:
            continue

        cand_info = []
        for ry in in_supp_rays:
            att = eval_ray_on_supp(ry, pos_in_supp, k)
            masked = att & bad_mask
            if masked == 0:
                cand_info.append((ry, 0, att ^ all_ones))
            elif masked == bad_mask:
                cand_info.append((ry, 1, att))

        if not cand_info:
            continue

        cur_locus = all_ones
        chosen: list[tuple[int, int]] = []
        while cur_locus != bad_mask:
            best_cand = None
            best_key = (cur_locus.bit_count(), 2, 99, 0, 999)
            for ry, c0, r_mask in cand_info:
                new_loc = cur_locus & r_mask
                cnt = new_loc.bit_count()
                if cnt < cur_locus.bit_count():
                    k_ord = (
                        cnt,
                        0 if ry in ray_to_wire else 1,
                        len(vars_of_ray(ry)),
                        -ray_hits.get(ry, 1),
                        ry.bit_count(),
                    )
                    if k_ord < best_key:
                        best_key = k_ord
                        best_cand = (ry, c0, new_loc)
            if best_cand is None:
                break
            ry_win, cv_win, cur_locus = best_cand
            chosen.append((ry_win, cv_win))

        if cur_locus != bad_mask:
            continue

        blk_cl = frozenset(get_ray_wire(ry) if c_val == 0 else -get_ray_wire(ry) for ry, c_val in chosen)
        for cs in cl_list:
            clauses_to_remove.add(cs)
        new_clauses.append(blk_cl)
        rewritten += 1

    if rewritten == 0:
        return top_var, clause_sets, 0

    kept = [cs for cs in clause_sets if cs not in clauses_to_remove] + new_clauses
    return top_var, kept, len(ray_to_wire)


def synthesize_ef_extensions(
    n_vars: int,
    clauses: list[list[int]],
    max_rm_deg: int = 4,
    max_iters: int = 60,
) -> tuple[int, list[list[int]], dict[int, int], int, int]:
    """
    Full Extended-Frege synthesis pipeline:
      1) Fast (1,1)-chain unrolling.
      2) Adaptive Veronese RM(d) dual annihilator synthesis (d = 1..max_rm_deg).
      3) Polar-symmetric clause-biclique factorization.
      4) Re-splitting to <=3-CNF and compact variable relabeling.
    """
    work_list = fast_unroll_11_chains(clauses)
    clause_sets = [frozenset(c) for c in work_list]
    top_var = n_vars
    shared_monoms: dict[tuple[int, ...], int] = {}
    rm_counts: dict[int, int] = {}

    for d in range(1, max_rm_deg + 1):
        if not any(4 <= len(cs) <= 12 for cs in clause_sets):
            break
        top_var, clause_sets, nr = synthesize_veronese_rm_d(
            top_var, clause_sets, deg_d=d, max_supp=12, shared_monom_wire=shared_monoms
        )
        if nr > 0:
            rm_counts[d] = nr

    synth_records: list[tuple[int, tuple[int, ...], int]] = []
    n_synth = 0
    n_comp_merged = 0

    for _it in range(max_iters):
        wide = [cs for cs in clause_sets if 3 <= len(cs) <= 8]
        if len(wide) < 2 or len(wide) > 1500:
            break

        lit_to_idxs: dict[int, list[int]] = defaultdict(list)
        for i, cs in enumerate(wide):
            for l in cs:
                lit_to_idxs[l].append(i)

        cand_betas: set[frozenset[int]] = set()
        i1_by_anchor: dict[int, list[frozenset[int]]] = defaultdict(list)
        seen_pairs: set[tuple[int, int]] = set()
        for _l, idxs in lit_to_idxs.items():
            if len(idxs) < 2:
                continue
            use_idxs = idxs if len(idxs) <= 120 else idxs[:80]
            for a_i in range(len(use_idxs)):
                i1 = use_idxs[a_i]
                c1 = wide[i1]
                for b_i in range(a_i + 1, len(use_idxs)):
                    i2 = use_idxs[b_i]
                    pk = (i1, i2) if i1 < i2 else (i2, i1)
                    if pk in seen_pairs:
                        continue
                    seen_pairs.add(pk)
                    inter = c1 & wide[i2]
                    if 1 <= len(inter) < min(len(c1), len(wide[i2])):
                        if inter not in cand_betas:
                            cand_betas.add(inter)
                            i1_by_anchor[next(iter(inter))].append(inter)

        for anchor, x_list in i1_by_anchor.items():
            c_idxs = lit_to_idxs.get(anchor, ())[:80]
            for x_set in x_list[:80]:
                for idx_c in c_idxs:
                    inter2 = x_set & wide[idx_c]
                    if 1 <= len(inter2) < len(x_set):
                        cand_betas.add(inter2)

        if not cand_betas:
            break

        all_set = set(clause_sets)
        full_lit_idx: dict[int, list[frozenset[int]]] = defaultdict(list)
        for cs in clause_sets:
            for l in cs:
                full_lit_idx[l].append(cs)

        a_to_betas: dict[tuple[tuple[int, ...], ...], list[frozenset[int]]] = defaultdict(list)
        for beta in cand_betas:
            rare_lit = min(beta, key=lambda l: len(full_lit_idx[l]))
            b_vars = {abs(l) for l in beta}
            alphas = []
            for cs in full_lit_idx[rare_lit]:
                if len(cs) > len(beta) and beta.issubset(cs):
                    alpha = cs - beta
                    if len(alpha) <= 6 and not any(abs(al) in b_vars for al in alpha):
                        alphas.append(tuple(sorted(alpha, key=lambda z: (abs(z), z))))
            if len(alphas) >= 2:
                a_key = tuple(sorted(set(alphas)))
                if len(a_key) >= 2:
                    a_to_betas[a_key].append(beta)

        best_score = (0, 0)
        best_choice = None
        for a_key, b_list in a_to_betas.items():
            a_vars = {abs(l) for al in a_key for l in al}
            seen_b: set[frozenset[int]] = set()
            valid_betas: list[frozenset[int]] = []
            for b in b_list:
                if b not in seen_b and not any(abs(bl) in a_vars for bl in b):
                    if all((frozenset(al) | b) in all_set for al in a_key):
                        seen_b.add(b)
                        valid_betas.append(b)
            if len(valid_betas) < 2:
                continue
            b_key = tuple(sorted(tuple(sorted(b, key=lambda z: (abs(z), z))) for b in valid_betas))
            b_vars = {abs(l) for bl in b_key for l in bl}
            if len(b_vars) < len(a_vars):
                g_key, p_list, g_vars = b_key, [frozenset(al) for al in a_key], b_vars
            else:
                g_key, p_list, g_vars = a_key, valid_betas, a_vars
            if len(g_vars) > 6:
                continue
            ng, np_sz = len(g_key), len(p_list)
            gain = ng * np_sz - (ng + np_sz)
            if gain < 3:
                continue
            score = (gain * 10 - len(g_vars), gain)
            if score > best_score:
                best_score = score
                best_choice = (g_key, p_list, tuple(sorted(g_vars)))

        if best_choice is None:
            break

        g_key, p_list, dom_t = best_choice
        smask = truth_mask_on_vars(g_key, dom_t)
        full_m = (1 << (1 << len(dom_t))) - 1
        comp_m = full_m ^ smask

        reused_lit = None
        for prev_lit, prev_dom, prev_mask in synth_records:
            if prev_dom == dom_t and prev_mask == comp_m:
                reused_lit = -prev_lit
                break
            elif prev_dom == dom_t and prev_mask == smask:
                reused_lit = prev_lit
                break

        to_del = {frozenset(al) | b for al in g_key for b in p_list}
        clause_sets = [cs for cs in clause_sets if cs not in to_del]

        if reused_lit is not None:
            g_lit = reused_lit
            n_comp_merged += 1
        else:
            top_var += 1
            g_lit = top_var
            n_synth += 1

        existing = set(clause_sets)
        comp_key = prime_cnf_of_mask(dom_t, comp_m) if len(dom_t) <= 6 else None
        for al in g_key:
            nc = frozenset(al) | {-g_lit}
            if not any(-x in nc for x in nc) and nc not in existing:
                existing.add(nc)
                clause_sets.append(nc)
        if comp_key:
            for cal in comp_key:
                nc = frozenset(cal) | {g_lit}
                if not any(-x in nc for x in nc) and nc not in existing:
                    existing.add(nc)
                    clause_sets.append(nc)
        for b in p_list:
            nc = b | {g_lit}
            if not any(-x in nc for x in nc) and nc not in existing:
                existing.add(nc)
                clause_sets.append(nc)

        for prev_lit, prev_dom, prev_mask in synth_records:
            if prev_dom == dom_t and (smask & prev_mask) == 0 and abs(prev_lit) != abs(g_lit):
                mutex = frozenset({-g_lit, -prev_lit})
                if mutex not in existing:
                    existing.add(mutex)
                    clause_sets.append(mutex)

        synth_records.append((g_lit, dom_t, smask))
        clause_sets, c_hits = substitute_known_gadget_globally(clause_sets, dom_t, g_key, comp_key, g_lit)
        n_comp_merged += c_hits

    raw_clauses = []
    for cs in clause_sets:
        lits = sorted(cs, key=lambda z: (abs(z), z))
        while len(lits) > 3:
            top_var += 1
            raw_clauses.append([lits[0], lits[1], top_var])
            lits = [-top_var] + lits[2:]
        raw_clauses.append(lits)

    n_compact, compact_clauses = compact_active_cnf(raw_clauses)
    return n_compact, compact_clauses, rm_counts, n_synth, n_comp_merged
