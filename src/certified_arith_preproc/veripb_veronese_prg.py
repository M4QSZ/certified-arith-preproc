"""VeriPB 3.0 blind degree-2 Veronese RM(2, n) & F2-homological PRG proof logger (v0.3).

Certifies single-component expander-entangled Goldreich PRG formulas (`TSA` = XOR_3 + AND_2,
5-local twisted & 6-local homological `XOR_3 + MAJ_3` over K_4 simplicial 2-cycles, and
overdetermined random `XOR-MAJ_3` / `TSA` PRGs) as well as hybrid `PHP OR_S Goldreich`
disjunctive interpolants, using ONLY `pol` and `red` steps (zero `rup` search).
"""

from __future__ import annotations

import argparse
import itertools
import json
import shutil
import subprocess
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

from .benchmarks import gen_php
from .cnf_utils import scramble_cnf, write_dimacs
from .veripb_emitter import VeriPBLogger, lit_str
from .veripb_interpolant import (
    _emit_red_constraint,
    _ensure_uniform_guard,
    _realize_parity3_bounds,
    _try_certify_guarded_parity,
    _try_certify_guarded_php,
    _unroll_11_chains_logged,
    discover_primal_vertex_cut,
)


class _VeroneseRM2Record:
    """Descriptor of a guarded degree-<=2 Boolean equation `L(x) ^ Q(x) == rhs (mod 2)` on `supp`."""

    def __init__(
        self,
        supp: tuple[int, ...],
        lin_vars: tuple[int, ...],
        quad_pairs: tuple[tuple[int, int], ...],
        rhs: int,
        forbid_map: dict[tuple[int, ...], tuple[int, frozenset[int]]],
    ) -> None:
        self.supp = supp
        self.lin_vars = lin_vars
        self.quad_pairs = quad_pairs
        self.rhs = rhs
        # Maps forbidden assignment bits -> (cid, present_lits_frozenset)
        self.forbid_map = forbid_map


def _weaken_clause_to_target(
    cid: int,
    present_lits: set[int] | frozenset[int],
    target_lits: list[int],
    logger: VeriPBLogger,
) -> int:
    """Weaken clause `cid` with literal axioms `l >= 0` for each `l in target_lits - present_lits`."""
    missing = [l for l in target_lits if l not in present_lits]
    if not missing:
        return cid
    rpn: list[int | str] = [cid]
    for l in missing:
        rpn.extend([lit_str(l), "+"])
    return logger.emit_pol(rpn)


def _extract_veronese_rm2_records(
    fiber_items: list[tuple[list[int], int]],
    guard_lits: list[int],
    max_block_arity: int = 6,
) -> list[_VeroneseRM2Record]:
    """
    Blindly extract degree-<=2 Boolean equations in RM(2, n) from unrolled clauses of
    width `1 .. max_block_arity`. Purely cubic or higher-degree blocks (e.g. `XOR-AND_3`)
    have empty RM(2, k) vanishing ideals and cleanly yield zero records.
    """
    by_supp: dict[tuple[int, ...], list[tuple[list[int], int]]] = defaultdict(list)
    for cl, cid in fiber_items:
        if 1 <= len(cl) <= max_block_arity:
            supp = tuple(sorted(abs(x) for x in cl))
            if len(supp) == len(cl):
                by_supp[supp].append((cl, cid))

    guard_set = frozenset(guard_lits)
    records: list[_VeroneseRM2Record] = []

    for supp, items in sorted(by_supp.items()):
        k = len(supp)
        half_cube = 1 << (k - 1)
        if len(items) < half_cube:
            continue

        pos_of = {v: idx for idx, v in enumerate(supp)}
        forbid_map: dict[tuple[int, ...], tuple[int, frozenset[int]]] = {}
        for cl, cid in items:
            pt = [0] * k
            for lit in cl:
                pt[pos_of[abs(lit)]] = 0 if lit > 0 else 1
            tpt = tuple(pt)
            if tpt not in forbid_map:
                forbid_map[tpt] = (cid, guard_set | frozenset(cl))

        n_forbid = len(forbid_map)
        if n_forbid < half_cube:
            continue

        if n_forbid == half_cube:
            # Fast O(k * 2^k) Mobius / ANF transform over F_2
            anf = [0] * (1 << k)
            for bits in forbid_map.keys():
                m = 0
                for j in range(k):
                    if bits[j]:
                        m |= 1 << j
                anf[m] = 1
            for j in range(k):
                step = 1 << j
                for m in range(1 << k):
                    if m & step:
                        anf[m] ^= anf[m ^ step]

            # Exact degree <= 2 check in RM(2, k)
            if any(anf[m] == 1 and m.bit_count() > 2 for m in range(1 << k)):
                continue

            rhs = anf[0]
            lin_vars = tuple(supp[j] for j in range(k) if anf[1 << j] == 1)
            quad_pairs = tuple(
                (supp[j1], supp[j2])
                for j1 in range(k)
                for j2 in range(j1 + 1, k)
                if anf[(1 << j1) | (1 << j2)] == 1
            )
            if not lin_vars and not quad_pairs and rhs == 0:
                continue
            records.append(_VeroneseRM2Record(supp, lin_vars, quad_pairs, rhs, forbid_map))
        else:
            # General overconstrained block (`n_forbid > 2^{k-1}`): extract RM(2, k) vanishing ideal
            sat_pts = [
                bits
                for bits in itertools.product((0, 1), repeat=k)
                if bits not in forbid_map
            ]
            if not sat_pts:
                records.append(_VeroneseRM2Record(supp, (), (), 1, forbid_map))
                continue

            monoms: list[tuple[int, ...]] = [()]
            for j in range(k):
                monoms.append((j,))
            for j1 in range(k):
                for j2 in range(j1 + 1, k):
                    monoms.append((j1, j2))

            n_sat = len(sat_pts)
            pivots: dict[int, tuple[int, int]] = {}
            for m_idx, mon in enumerate(monoms):
                vec = 0
                for s_idx, pt in enumerate(sat_pts):
                    val = 1
                    for j in mon:
                        val &= pt[j]
                    if val:
                        vec |= 1 << s_idx
                comb = 1 << m_idx
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
                    rhs = comb & 1
                    lin_vars = tuple(
                        supp[monoms[b][0]]
                        for b in range(1, k + 1)
                        if (comb >> b) & 1
                    )
                    quad_pairs = tuple(
                        (supp[monoms[b][0]], supp[monoms[b][1]])
                        for b in range(k + 1, len(monoms))
                        if (comb >> b) & 1
                    )
                    if lin_vars or quad_pairs or rhs == 1:
                        records.append(
                            _VeroneseRM2Record(supp, lin_vars, quad_pairs, rhs, forbid_map)
                        )

    return records


def _try_certify_guarded_veronese_rm2(
    fiber_items: list[tuple[list[int], int]],
    guard_lits: list[int],
    logger: VeriPBLogger,
    alloc_var_fn,
    max_block_arity: int = 6,
) -> int | None:
    """
    Blindly extract degree-<=2 equations in Veronese space `RM(2, n)`, find a minimally
    inconsistent core via sparse GF(2) RREF, and emit an exact polynomial-size VeriPB 3.0
    (`pol` + `red`, zero `rup`) derivation of `G >= 1` (or `0 >= 1` when `guard_lits == []`).
    """
    records = _extract_veronese_rm2_records(fiber_items, guard_lits, max_block_arity=max_block_arity)
    if not records:
        return None

    # Map every RM(2, n) monomial `(v,)` or `(u, w)` to a compact integer coordinate ID
    monom_to_id: dict[tuple[int, ...], int] = {}

    def get_coord(m: tuple[int, ...]) -> int:
        cid = monom_to_id.get(m)
        if cid is None:
            cid = len(monom_to_id) + 1
            monom_to_id[m] = cid
        return cid

    pivots: dict[int, tuple[set[int], int, int]] = {}
    unsat_mask: int | None = None

    for idx_r, rec in enumerate(records):
        row_coords: set[int] = set()
        for v in rec.lin_vars:
            row_coords.symmetric_difference_update((get_coord((v,)),))
        for pair in rec.quad_pairs:
            row_coords.symmetric_difference_update((get_coord(pair),))
        rhs = rec.rhs
        comb = 1 << idx_r

        while row_coords:
            lead = max(row_coords)
            if lead in pivots:
                p_coords, p_rhs, p_comb = pivots[lead]
                row_coords ^= p_coords
                rhs ^= p_rhs
                comb ^= p_comb
            else:
                pivots[lead] = (row_coords, rhs, comb)
                break
        else:
            if rhs == 1:
                unsat_mask = comb
                break

    if unsat_mask is None:
        return None

    active_indices: list[int] = []
    tmp = unsat_mask
    while tmp:
        lsb = tmp & -tmp
        active_indices.append(lsb.bit_length() - 1)
        tmp ^= lsb

    # Lazily allocate shared Veronese product witnesses `p_{u,w} <-> (x_u & x_w)` ONLY for pairs in E*
    quad_witness: dict[tuple[int, int], tuple[int, int, int, int]] = {}
    for e_idx in active_indices:
        for pair in records[e_idx].quad_pairs:
            if pair not in quad_witness:
                u, w = pair
                p_var = alloc_var_fn()
                and_11 = _emit_red_constraint([(1, -u), (1, -w), (1, p_var)], 1, p_var, 1, logger)
                and_0x = _emit_red_constraint([(1, u), (1, -p_var)], 1, p_var, 0, logger)
                and_x0 = _emit_red_constraint([(1, w), (1, -p_var)], 1, p_var, 0, logger)
                quad_witness[pair] = (p_var, and_11, and_0x, and_x0)

    taut_cache: dict[int, int] = {}

    def get_taut(v: int) -> int:
        tid = taut_cache.get(v)
        if tid is None:
            tid = logger.emit_pol([f"x{v}", f"~x{v}", "+"])
            taut_cache[v] = tid
        return tid

    def collapse_clause_cube(
        supp: tuple[int, ...],
        leaf_cids: dict[tuple[int, ...], int],
    ) -> int:
        k = len(supp)
        cur_layer = dict(leaf_cids)
        for q in range(k - 1, -1, -1):
            nxt_layer: dict[tuple[int, ...], int] = {}
            for prefix in itertools.product((0, 1), repeat=q):
                id_0 = cur_layer[prefix + (0,)]
                id_1 = cur_layer[prefix + (1,)]
                nxt_layer[prefix] = logger.emit_pol([id_0, id_1, "+", 2, "d"])
            cur_layer = nxt_layer
        return cur_layer[()]

    plus_terms: list[tuple[int, int]] = []
    minus_terms: list[tuple[int, int]] = []
    g_flag = 1 if guard_lits else 0

    for e_idx in active_indices:
        rec = records[e_idx]
        supp = rec.supp
        k = len(supp)
        pos_of = {v: idx for idx, v in enumerate(supp)}
        supp_set = set(supp)

        z_vars: list[int] = list(rec.lin_vars) + [
            quad_witness[pair][0] for pair in rec.quad_pairs
        ]
        r = len(z_vars)
        c0 = rec.rhs

        if r == 0:
            # All 2^k assignments on `supp` are forbidden -> directly derives `G >= 1` (`0 >= 1`)!
            leaf_cids: dict[tuple[int, ...], int] = {}
            for bits in itertools.product((0, 1), repeat=k):
                leaf_lits = [-supp[q] if bits[q] == 1 else supp[q] for q in range(k)]
                base_cid, pres = rec.forbid_map[bits]
                leaf_cids[bits] = _weaken_clause_to_target(
                    base_cid, pres, list(guard_lits) + leaf_lits, logger
                )
            return collapse_clause_cube(supp, leaf_cids)

        if r == 1:
            z1 = z_vars[0]
            target_lit = z1 if c0 == 1 else -z1
            leaf_cids = {}
            for bits in itertools.product((0, 1), repeat=k):
                leaf_lits = [-supp[q] if bits[q] == 1 else supp[q] for q in range(k)]
                full_target = list(guard_lits) + leaf_lits + [target_lit]
                if bits in rec.forbid_map:
                    base_cid, pres = rec.forbid_map[bits]
                    leaf_cids[bits] = _weaken_clause_to_target(base_cid, pres, full_target, logger)
                else:
                    if z1 in supp_set:
                        tid = get_taut(z1)
                        leaf_cids[bits] = _weaken_clause_to_target(
                            tid, {z1, -z1}, full_target, logger
                        )
                    else:
                        pair = rec.quad_pairs[0]
                        p_var, and_11, and_0x, and_x0 = quad_witness[pair]
                        u, w = pair
                        bu, bw = bits[pos_of[u]], bits[pos_of[w]]
                        if bu == 1 and bw == 1:
                            leaf_cids[bits] = _weaken_clause_to_target(
                                and_11, {-u, -w, p_var}, full_target, logger
                            )
                        elif bu == 0:
                            leaf_cids[bits] = _weaken_clause_to_target(
                                and_0x, {u, -p_var}, full_target, logger
                            )
                        else:
                            leaf_cids[bits] = _weaken_clause_to_target(
                                and_x0, {w, -p_var}, full_target, logger
                            )
            unit_cid = collapse_clause_cube(supp, leaf_cids)
            if c0 == 1:
                id_m = logger.emit_pol([f"~x{z1}"])
                plus_terms.append((unit_cid, g_flag))
                minus_terms.append((id_m, 0))
            else:
                id_p = logger.emit_pol([f"x{z1}"])
                plus_terms.append((id_p, 0))
                minus_terms.append((unit_cid, g_flag))
            continue

        # General width `r >= 2`: fold `z_vars[0 .. r-2]` into 3-XOR witness steps
        acc_var = z_vars[0]
        fold_steps: list[tuple[int, int, int, int, int, int, int]] = []
        for nxt_z in z_vars[1 : r - 1]:
            s_var = alloc_var_fn()
            z_01 = _emit_red_constraint([(1, acc_var), (1, -nxt_z), (1, s_var)], 1, s_var, 1, logger)
            z_10 = _emit_red_constraint([(1, -acc_var), (1, nxt_z), (1, s_var)], 1, s_var, 1, logger)
            z_00 = _emit_red_constraint([(1, acc_var), (1, nxt_z), (1, -s_var)], 1, s_var, 0, logger)
            z_11 = _emit_red_constraint([(1, -acc_var), (1, -nxt_z), (1, -s_var)], 1, s_var, 0, logger)
            f_a = {
                (1, 0, 0): z_10,
                (0, 1, 0): z_01,
                (0, 0, 1): z_00,
                (1, 1, 1): z_11,
            }
            idp_a, _, idm_a, _ = _realize_parity3_bounds(
                acc_var, nxt_z, s_var, 0, f_a, [], logger, alloc_var_fn
            )
            plus_terms.append((idp_a, 0))
            minus_terms.append((idm_a, 0))
            fold_steps.append((acc_var, nxt_z, s_var, z_00, z_01, z_10, z_11))
            acc_var = s_var

        last_a = acc_var
        last_b = z_vars[r - 1]
        if c0 == 0:
            pair_p = (last_a, -last_b)
            pair_m = (-last_a, last_b)
        else:
            pair_p = (last_a, last_b)
            pair_m = (-last_a, -last_b)

        leaves_p: dict[tuple[int, ...], int] = {}
        leaves_m: dict[tuple[int, ...], int] = {}

        for bits in itertools.product((0, 1), repeat=k):
            leaf_lits = [-supp[q] if bits[q] == 1 else supp[q] for q in range(k)]
            full_p = list(guard_lits) + leaf_lits + [pair_p[0], pair_p[1]]
            full_m = list(guard_lits) + leaf_lits + [pair_m[0], pair_m[1]]

            if bits in rec.forbid_map:
                base_cid, pres = rec.forbid_map[bits]
                leaves_p[bits] = _weaken_clause_to_target(base_cid, pres, full_p, logger)
                leaves_m[bits] = _weaken_clause_to_target(base_cid, pres, full_m, logger)
                continue

            # Allowed point (`P_i(bits) == 0`): evaluate every variable in `z_vars` and `fold_steps` once!
            val_of: dict[int, int] = {supp[q]: bits[q] for q in range(k)}
            # For derived vars `d not in supp_set`: map `d -> (cid_d, support_set_d)` proving
            # `support_set_d <= set(leaf_lits) | {d if val_of[d]==1 else -d}`
            derived_unit: dict[int, tuple[int, set[int]]] = {}

            for pair in rec.quad_pairs:
                p_var, and_11, and_0x, and_x0 = quad_witness[pair]
                u, w = pair
                bu, bw = bits[pos_of[u]], bits[pos_of[w]]
                if bu == 1 and bw == 1:
                    val_of[p_var] = 1
                    derived_unit[p_var] = (and_11, {-u, -w, p_var})
                elif bu == 0:
                    val_of[p_var] = 0
                    derived_unit[p_var] = (and_0x, {u, -p_var})
                else:
                    val_of[p_var] = 0
                    derived_unit[p_var] = (and_x0, {w, -p_var})

            for v1, v2, s_var, z_00, z_01, z_10, z_11 in fold_steps:
                b1, b2 = val_of[v1], val_of[v2]
                bs = b1 ^ b2
                val_of[s_var] = bs
                lit1_u = v1 if b1 == 1 else -v1
                lit2_u = v2 if b2 == 1 else -v2
                s_lit = s_var if bs == 1 else -s_var

                if (b1, b2) == (0, 0):
                    cur_cid = z_00
                elif (b1, b2) == (0, 1):
                    cur_cid = z_01
                elif (b1, b2) == (1, 0):
                    cur_cid = z_10
                else:
                    cur_cid = z_11
                cur_supp: set[int] = {-lit1_u, -lit2_u, s_lit}

                if v1 not in supp_set:
                    c1, s1 = derived_unit[v1]
                    rem1 = cur_supp - {-lit1_u}
                    s1_rem = s1 - {lit1_u}
                    overlap1 = bool(rem1 & s1_rem)
                    cur_cid = (
                        logger.emit_pol([cur_cid, c1, "+", "s"])
                        if overlap1
                        else logger.emit_pol([cur_cid, c1, "+"])
                    )
                    cur_supp = rem1 | s1_rem

                if v2 not in supp_set:
                    c2, s2 = derived_unit[v2]
                    rem2 = cur_supp - {-lit2_u}
                    s2_rem = s2 - {lit2_u}
                    overlap2 = bool(rem2 & s2_rem)
                    cur_cid = (
                        logger.emit_pol([cur_cid, c2, "+", "s"])
                        if overlap2
                        else logger.emit_pol([cur_cid, c2, "+"])
                    )
                    cur_supp = rem2 | s2_rem

                derived_unit[s_var] = (cur_cid, cur_supp)

            def realize_target_pair(
                t_pair: tuple[int, int], full_target: list[int]
            ) -> int:
                for t_lit in t_pair:
                    tv = abs(t_lit)
                    is_true = (val_of[tv] == 1) if t_lit > 0 else (val_of[tv] == 0)
                    if is_true:
                        if tv in supp_set:
                            tid = get_taut(tv)
                            return _weaken_clause_to_target(tid, {tv, -tv}, full_target, logger)
                        dcid, dsupp = derived_unit[tv]
                        return _weaken_clause_to_target(dcid, dsupp, full_target, logger)
                raise AssertionError("Allowed point violated extracted RM(2, k) identity")

            leaves_p[bits] = realize_target_pair(pair_p, full_p)
            leaves_m[bits] = realize_target_pair(pair_m, full_m)

        cid_p = collapse_clause_cube(supp, leaves_p)
        cid_m = collapse_clause_cube(supp, leaves_m)
        plus_terms.append((cid_p, g_flag))
        minus_terms.append((cid_m, g_flag))

    def sum_and_halve(terms_list: list[tuple[int, int]]) -> tuple[int, int]:
        rpn: list[int | str] = [terms_list[0][0]]
        g_tot = terms_list[0][1]
        for cid, gc in terms_list[1:]:
            rpn.extend([cid, "+"])
            g_tot += gc
        if guard_lits and (g_tot & 1) == 1:
            for g in guard_lits:
                rpn.extend([lit_str(g), "+"])
            g_tot += 1
        rpn.extend([2, "d"])
        return logger.emit_pol(rpn), g_tot // 2

    half_p, mp = sum_and_halve(plus_terms)
    half_m, mm = sum_and_halve(minus_terms)
    comb_id = logger.emit_pol([half_p, half_m, "+"])
    tot_m = mp + mm
    if not guard_lits or tot_m <= 1:
        return comb_id
    return logger.emit_pol([comb_id, tot_m, "d"])


def certify_veronese_prg_veripb(
    n_vars: int,
    clauses: list[list[int]],
    cnf_path: str | Path,
    pbp_path: str | Path,
    max_cut: int = 6,
    max_block_arity: int = 6,
) -> dict[str, object]:
    """
    Unified v0.3 VeriPB 3.0 certifier for blind degree-2 Veronese / homological PRG expanders
    (`|S| == 0`) AND hybrid disjunctive interpolants (`PHP OR_S Goldreich`, `1 <= |S| <= max_cut`).
    """
    cnf_path = Path(cnf_path)
    pbp_path = Path(pbp_path)
    pbp_path.parent.mkdir(parents=True, exist_ok=True)
    write_dimacs(cnf_path, n_vars, clauses)

    t0 = time.perf_counter()
    logger = VeriPBLogger(len(clauses))
    next_fresh_var = n_vars

    def alloc_var() -> int:
        nonlocal next_fresh_var
        next_fresh_var += 1
        return next_fresh_var

    init_items = [(list(cl), idx + 1) for idx, cl in enumerate(clauses)]
    unrolled_items = _unroll_11_chains_logged(init_items, logger)
    unrolled_clauses = [cl for cl, _cid in unrolled_items]

    sep_vars, _comps = discover_primal_vertex_cut(unrolled_clauses, max_cut=max_cut)
    cut_list: list[int] = sep_vars if sep_vars is not None else []
    cut_set = set(cut_list)

    fiber_guard_cids: dict[tuple[int, ...], int] = {}
    fiber_engines: dict[str, str] = {}

    for bits in itertools.product((0, 1), repeat=len(cut_list)):
        guard_lits = [-sv if b == 1 else sv for sv, b in zip(cut_list, bits)]
        satisfied_lits = {sv if b == 1 else -sv for sv, b in zip(cut_list, bits)}

        proj_raw: list[tuple[list[int], int]] = []
        empty_guard_cid: int | None = None

        for cl, cid in unrolled_items:
            if any(x in satisfied_lits for x in cl):
                continue
            present_g = {x for x in cl if abs(x) in cut_set}
            core = [x for x in cl if abs(x) not in cut_set]
            u_cid = _ensure_uniform_guard(cid, present_g, guard_lits, logger)
            if not core:
                empty_guard_cid = u_cid
                break
            proj_raw.append((core, u_cid))

        if empty_guard_cid is not None:
            fiber_guard_cids[bits] = empty_guard_cid
            fiber_engines[str(bits)] = "unit_guard"
            continue

        re_items: list[tuple[list[int], int]] = [
            (sorted(list(guard_lits) + core, key=lambda z: (abs(z), z)), u_cid)
            for core, u_cid in proj_raw
        ]
        re_unrolled = _unroll_11_chains_logged(re_items, logger, protected_vars=cut_set)

        fiber_clean: list[tuple[list[int], int]] = []
        direct_hit: int | None = None
        for full_cl, f_cid in re_unrolled:
            present_g = {x for x in full_cl if abs(x) in cut_set}
            core = [x for x in full_cl if abs(x) not in cut_set]
            u_cid = _ensure_uniform_guard(f_cid, present_g, guard_lits, logger)
            if not core:
                direct_hit = u_cid
                break
            fiber_clean.append((core, u_cid))

        if direct_hit is not None:
            fiber_guard_cids[bits] = direct_hit
            fiber_engines[str(bits)] = "unrolled_empty"
            continue

        g_cid = _try_certify_guarded_php(fiber_clean, guard_lits, logger)
        if g_cid is not None:
            fiber_guard_cids[bits] = g_cid
            fiber_engines[str(bits)] = "guarded_php_cg"
            continue

        g_cid = _try_certify_guarded_parity(fiber_clean, guard_lits, logger, alloc_var)
        if g_cid is not None:
            fiber_guard_cids[bits] = g_cid
            fiber_engines[str(bits)] = "guarded_parity_maj3"
            continue

        g_cid = _try_certify_guarded_veronese_rm2(
            fiber_clean,
            guard_lits,
            logger,
            alloc_var,
            max_block_arity=max_block_arity,
        )
        if g_cid is not None:
            fiber_guard_cids[bits] = g_cid
            fiber_engines[str(bits)] = "veronese_rm2_homological"
            continue

        raise RuntimeError(
            f"Fiber {bits} on separator S={cut_list} is FEASIBLE or outside RM(2, n) Veronese calculus"
        )

    def collapse_cube(idx: int, prefix: tuple[int, ...]) -> int:
        if idx == len(cut_list):
            return fiber_guard_cids[prefix]
        id0 = collapse_cube(idx + 1, prefix + (0,))
        id1 = collapse_cube(idx + 1, prefix + (1,))
        return logger.emit_pol([id0, id1, "+", 2, "d"])

    contra_id = collapse_cube(0, ())
    pbp_text = logger.finish_unsat(contra_id)
    pbp_path.write_text(pbp_text, encoding="utf-8")
    emit_ms = (time.perf_counter() - t0) * 1000.0

    return {
        "n_vars_orig": n_vars,
        "n_clauses_orig": len(clauses),
        "n_extension_vars": next_fresh_var - n_vars,
        "separator_size": len(cut_list),
        "separator_vars": cut_list,
        "fiber_engines": fiber_engines,
        "pbp_lines": len(logger.lines),
        "emit_ms": round(emit_ms, 2),
    }


# ---------------------------------------------------------------------------
# Benchmark Family Generators for v0.3 (Goldreich TSA, Homological XOR3-MAJ3,
# Hybrid PHP OR_S Goldreich, and Degree-3 Cubic XOR3-AND3 Barrier Control)
# ---------------------------------------------------------------------------


def _sample_3regular_expander(
    n_verts: int, rng: np.random.Generator
) -> tuple[int, list[list[int]]]:
    """Sample a simple 3-regular graph (Hamiltonian cycle + disjoint perfect matching)."""
    assert n_verts % 2 == 0 and n_verts >= 6
    inc: list[list[int]] = [[] for _ in range(n_verts)]
    adj_set: set[tuple[int, int]] = set()
    perm = list(rng.permutation(n_verts))
    eid = 0
    for idx in range(n_verts):
        u, v = int(perm[idx]), int(perm[(idx + 1) % n_verts])
        a, b = (u, v) if u < v else (v, u)
        adj_set.add((a, b))
        eid += 1
        inc[a].append(eid)
        inc[b].append(eid)

    for _attempt in range(1000):
        order = list(rng.permutation(n_verts))
        pairs: list[tuple[int, int]] = []
        ok = True
        for idx in range(0, n_verts, 2):
            u, v = int(order[idx]), int(order[idx + 1])
            a, b = (u, v) if u < v else (v, u)
            if (a, b) in adj_set:
                ok = False
                break
            pairs.append((a, b))
        if ok:
            for a, b in pairs:
                eid += 1
                inc[a].append(eid)
                inc[b].append(eid)
            return eid, inc
    raise RuntimeError("Failed to sample simple 3-regular graph")


def gen_goldreich_tsa_expander_3cnf(
    n_verts: int = 44,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    5-local Goldreich TSA (`x_e1 ^ x_e2 ^ x_e3 ^ (x_q1 & x_q2) = rhs_v`) over a single
    3-regular expander with paired antipodal quadratic masks (`|S| = 0`, zero vertex cuts).
    """
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)
    v_order = list(rng.permutation(n_verts))
    quad_of_v: list[tuple[int, int]] = [(0, 0)] * n_verts
    used_quads: set[tuple[int, int]] = set()

    for idx in range(0, n_verts, 2):
        v1, v2 = int(v_order[idx]), int(v_order[idx + 1])
        forbid = set(inc[v1]) | set(inc[v2])
        avail = [e for e in range(1, n_edges + 1) if e not in forbid]
        for _ in range(500):
            q1, q2 = sorted(int(x) for x in rng.choice(avail, size=2, replace=False))
            if (q1, q2) not in used_quads:
                used_quads.add((q1, q2))
                quad_of_v[v1] = (q1, q2)
                quad_of_v[v2] = (q1, q2)
                break
        else:
            raise RuntimeError("Failed to sample antipodal quadratic mask")

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []
    for v in range(n_verts):
        e1, e2, e3 = inc[v]
        q1, q2 = quad_of_v[v]
        vs = (e1, e2, e3, q1, q2)
        zv = [z_star[x] for x in vs]
        rhs = zv[0] ^ zv[1] ^ zv[2] ^ (zv[3] & zv[4])
        if unsat and v == 0:
            rhs ^= 1
        for bits in itertools.product((0, 1), repeat=5):
            val = bits[0] ^ bits[1] ^ bits[2] ^ (bits[3] & bits[4])
            if val != rhs:
                lits = [-var if bit else var for var, bit in zip(vs, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def gen_homological_xormaj3_expander_3cnf(
    n_verts: int = 44,
    five_local_twist: bool = True,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    Single-expander Homological `XOR_3 + MAJ_3` over F_2-simplicial `K_4` 2-cycles (`d^2 = 0`).
    Every `MAJ_3` triplet across all `n_verts` gates is unique (ZERO repeated triplets!).
    - `five_local_twist=True`: 5-local `x_e1 ^ x_e2 ^ x_e3 ^ MAJ_3(x_e3, x_b, x_c) = rhs_v`.
    - `five_local_twist=False`: 6-local `x_e1 ^ x_e2 ^ x_e3 ^ MAJ_3(x_a, x_b, x_c) = rhs_v`.
    """
    assert n_verts % 4 == 0 and n_verts >= 12
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)

    face_of_v: list[tuple[int, int, int]] = [(0, 0, 0)] * n_verts
    for _attempt in range(500):
        v_order = [int(x) for x in rng.permutation(n_verts)]
        used_triplets: set[tuple[int, int, int]] = set()
        ok_all = True
        for g in range(0, n_verts, 4):
            grp = v_order[g : g + 4]
            if five_local_twist:
                found_q = False
                for choices in itertools.product(range(3), repeat=4):
                    u = [inc[grp[j]][choices[j]] for j in range(4)]
                    if len(set(u)) < 4:
                        continue
                    faces = [
                        (u[0], u[1], u[2]),
                        (u[1], u[0], u[3]),
                        (u[2], u[0], u[3]),
                        (u[3], u[1], u[2]),
                    ]
                    f_sets = [tuple(sorted(f)) for f in faces]
                    if any(fs in used_triplets for fs in f_sets):
                        continue
                    if all(
                        all(x not in inc[grp[j]] for x in faces[j] if x != u[j])
                        for j in range(4)
                    ):
                        used_triplets.update(f_sets)
                        for j in range(4):
                            face_of_v[grp[j]] = faces[j]
                        found_q = True
                        break
                if not found_q:
                    ok_all = False
                    break
            else:
                forbid = set().union(*(inc[v] for v in grp))
                avail = [e for e in range(1, n_edges + 1) if e not in forbid]
                for _ in range(300):
                    u = sorted(int(x) for x in rng.choice(avail, size=4, replace=False))
                    faces = [
                        (u[0], u[1], u[2]),
                        (u[0], u[1], u[3]),
                        (u[0], u[2], u[3]),
                        (u[1], u[2], u[3]),
                    ]
                    if not any(f in used_triplets for f in faces):
                        used_triplets.update(faces)
                        for j in range(4):
                            face_of_v[grp[j]] = faces[j]
                        break
                else:
                    ok_all = False
                    break
        if ok_all:
            break
    else:
        raise RuntimeError("Failed to embed disjoint K4 simplicial 2-cycles")

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []

    for v in range(n_verts):
        e1, e2, e3 = inc[v]
        f = face_of_v[v]
        if five_local_twist:
            others = [e for e in (e1, e2, e3) if e != f[0]]
            vs5 = (others[0], others[1], f[0], f[1], f[2])
            zv = [z_star[x] for x in vs5]
            maj = (zv[2] & zv[3]) ^ (zv[2] & zv[4]) ^ (zv[3] & zv[4])
            rhs = zv[0] ^ zv[1] ^ zv[2] ^ maj
            if unsat and v == 0:
                rhs ^= 1
            for bits in itertools.product((0, 1), repeat=5):
                bmaj = (bits[2] & bits[3]) ^ (bits[2] & bits[4]) ^ (bits[3] & bits[4])
                if (bits[0] ^ bits[1] ^ bits[2] ^ bmaj) != rhs:
                    lits = [-var if bit else var for var, bit in zip(vs5, bits)]
                    while len(lits) > 3:
                        top += 1
                        cls.append([lits[0], lits[1], top])
                        lits = [-top] + lits[2:]
                    cls.append(lits)
        else:
            vs6 = (e1, e2, e3, f[0], f[1], f[2])
            zv = [z_star[x] for x in vs6]
            maj = (zv[3] & zv[4]) ^ (zv[3] & zv[5]) ^ (zv[4] & zv[5])
            rhs = zv[0] ^ zv[1] ^ zv[2] ^ maj
            if unsat and v == 0:
                rhs ^= 1
            for bits in itertools.product((0, 1), repeat=6):
                bmaj = (bits[3] & bits[4]) ^ (bits[3] & bits[5]) ^ (bits[4] & bits[5])
                if (bits[0] ^ bits[1] ^ bits[2] ^ bmaj) != rhs:
                    lits = [-var if bit else var for var, bit in zip(vs6, bits)]
                    while len(lits) > 3:
                        top += 1
                        cls.append([lits[0], lits[1], top])
                        lits = [-top] + lits[2:]
                    cls.append(lits)

    return top, cls


def gen_hybrid_php_homological_xormaj3_3cnf(
    pigeons: int = 12,
    holes: int = 11,
    n_verts: int = 36,
    num_selectors: int = 2,
    unsat_php: bool = True,
    unsat_prg: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """Wire-eliminated disjunctive interpolant `PHP_p^h OR_S Homological_XOR3_MAJ3`."""
    n1, c1 = gen_php(pigeons if unsat_php else holes, holes)
    n2, c2 = gen_homological_xormaj3_expander_3cnf(
        n_verts=n_verts, five_local_twist=True, unsat=unsat_prg, seed=seed
    )
    s_vars = [n1 + n2 + 1 + t for t in range(num_selectors)]
    top = s_vars[-1]
    c2_shifted = [[(x + n1 if x > 0 else x - n1) for x in cl] for cl in c2]

    cls: list[list[int]] = []
    for bits in itertools.product((0, 1), repeat=num_selectors):
        gd = [-sv if b == 1 else sv for sv, b in zip(s_vars, bits)]
        target = c1 if (sum(bits) & 1) == 0 else c2_shifted
        for c in target:
            lits = gd + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls


def gen_cubic_xor3_and3_barrier_3cnf(
    n_verts: int = 28,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    Degree-3 Cubic Goldreich Barrier (`x_e1 ^ x_e2 ^ x_e3 ^ (x_a & x_b & x_c) = rhs_v`) with
    paired antipodal cubic masks (`deg = 3` outside `RM(2, n)`, witnessing the v0.3 -> v0.4 frontier).
    """
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)
    v_order = list(rng.permutation(n_verts))
    cub_of_v: list[tuple[int, int, int]] = [(0, 0, 0)] * n_verts
    used_cubs: set[tuple[int, int, int]] = set()

    for idx in range(0, n_verts, 2):
        v1, v2 = int(v_order[idx]), int(v_order[idx + 1])
        forbid = set(inc[v1]) | set(inc[v2])
        avail = [e for e in range(1, n_edges + 1) if e not in forbid]
        for _ in range(500):
            c1, c2, c3 = sorted(int(x) for x in rng.choice(avail, size=3, replace=False))
            if (c1, c2, c3) not in used_cubs:
                used_cubs.add((c1, c2, c3))
                cub_of_v[v1] = (c1, c2, c3)
                cub_of_v[v2] = (c1, c2, c3)
                break

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []
    for v in range(n_verts):
        e1, e2, e3 = inc[v]
        c1, c2, c3 = cub_of_v[v]
        vs = (e1, e2, e3, c1, c2, c3)
        zv = [z_star[x] for x in vs]
        rhs = zv[0] ^ zv[1] ^ zv[2] ^ (zv[3] & zv[4] & zv[5])
        if unsat and v == 0:
            rhs ^= 1
        for bits in itertools.product((0, 1), repeat=6):
            val = bits[0] ^ bits[1] ^ bits[2] ^ (bits[3] & bits[4] & bits[5])
            if val != rhs:
                lits = [-var if bit else var for var, bit in zip(vs, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def gen_xor_maj5_barrier_3cnf(
    n_verts: int = 36,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    7-local Degree-4 Goldreich `XOR_3-MAJ_5` Barrier (`x_e1 ^ x_e2 ^ x_e3 ^ MAJ_5(x_e3, q1, q2, q3, q4) = rhs_v`)
    over a 3-regular expander with paired antipodal `MAJ_5` masks (`nullity == 0` in `RM(2, 7)`).
    """
    assert n_verts % 2 == 0 and n_verts >= 16
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)
    v_order = [int(x) for x in rng.permutation(n_verts)]
    maj5_of_v: list[tuple[int, int, int, int, int]] = [(0, 0, 0, 0, 0)] * n_verts
    used5: set[tuple[int, int, int, int, int]] = set()

    for idx in range(0, n_verts, 2):
        v1, v2 = v_order[idx], v_order[idx + 1]
        forbid = set(inc[v1]) | set(inc[v2])
        avail = [e for e in range(1, n_edges + 1) if e not in forbid]
        for _ in range(500):
            q5 = tuple(sorted(int(x) for x in rng.choice(avail, size=5, replace=False)))
            if q5 not in used5:
                used5.add(q5)  # type: ignore[arg-type]
                maj5_of_v[v1] = q5  # type: ignore[assignment]
                maj5_of_v[v2] = q5  # type: ignore[assignment]
                break
        else:
            raise RuntimeError("Failed to sample antipodal MAJ_5 mask")

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []
    for v in range(n_verts):
        e1, e2, e3 = inc[v]
        q5 = maj5_of_v[v]
        # 8 distinct vars if disjoint, or 7-local if we share one antipodal chord?
        # Wait: to keep antipodal MAJ_5 IDENTICAL on v1 and v2 (so sum mod 2 cancels MAJ_5!),
        # `q5` must be the SAME 5-tuple on v1 and v2 (`8`-local `e1,e2,e3,q1..q5`), OR `q1` is a shared
        # edge between v1 and v2 (if adjacent in expander matching)!
        # Pairing along the 3-regular expander's perfect matching (`e3` shared by `(v1, v2)`!!):
        # Then `vs = (e1, e2, e3, q1, q2, q3, q4)` has `e3` in BOTH `v1` and `v2`, so `MAJ_5(e3, q1, q2, q3, q4)`
        # is IDENTICAL on `v1` and `v2` AND strictly 7-local (`2^7 = 128`, `64` clauses per vertex)!!
        pass
    # Rebuild using the exact shared matching edge `e_shared` of each pair!
    paired_vs: list[tuple[int, int, int]] = []
    edge_to_verts: dict[int, list[int]] = defaultdict(list)
    for v in range(n_verts):
        for e in inc[v]:
            edge_to_verts[e].append(v)
    # The last `n_verts // 2` edges in `_sample_3regular_expander` form a perfect matching!
    matching_edges = list(range(n_verts + 1, n_edges + 1))
    used5.clear()
    for e_sh in matching_edges:
        v1, v2 = edge_to_verts[e_sh]
        forbid = set(inc[v1]) | set(inc[v2])
        avail = [e for e in range(1, n_edges + 1) if e not in forbid]
        for _ in range(500):
            q4 = sorted(int(x) for x in rng.choice(avail, size=4, replace=False))
            q5 = (e_sh, q4[0], q4[1], q4[2], q4[3])
            q5_key = tuple(sorted(q5))
            if q5_key not in used5:
                used5.add(q5_key)  # type: ignore[arg-type]
                maj5_of_v[v1] = q5
                maj5_of_v[v2] = q5
                break

    for v in range(n_verts):
        q5 = maj5_of_v[v]
        e_sh = q5[0]
        others = [e for e in inc[v] if e != e_sh]
        vs = (others[0], others[1], e_sh, q5[1], q5[2], q5[3], q5[4])
        zv = [z_star[x] for x in vs]
        maj5_v = 1 if sum(zv[2:]) >= 3 else 0
        rhs = zv[0] ^ zv[1] ^ zv[2] ^ maj5_v
        if unsat and v == 0:
            rhs ^= 1
        for bits in itertools.product((0, 1), repeat=7):
            bmaj5 = 1 if sum(bits[2:]) >= 3 else 0
            if (bits[0] ^ bits[1] ^ bits[2] ^ bmaj5) != rhs:
                lits = [-var if bit else var for var, bit in zip(vs, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=Path("results/veronese_prg_proofs"))
    ap.add_argument(
        "--json-out", type=Path, default=Path("results/veronese_prg_veripb_results.json")
    )
    ap.add_argument("--veripb-bin", type=str, default=shutil.which("veripb") or "veripb")
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    suite = [
        ("Goldreich_TSA_5Local_V44", lambda: gen_goldreich_tsa_expander_3cnf(44, True, 2026)),
        ("Goldreich_TSA_5Local_V64", lambda: gen_goldreich_tsa_expander_3cnf(64, True, 2027)),
        (
            "Homological_XOR3_MAJ3_5Local_V44",
            lambda: gen_homological_xormaj3_expander_3cnf(44, True, True, 2028),
        ),
        (
            "Homological_XOR3_MAJ3_5Local_V64",
            lambda: gen_homological_xormaj3_expander_3cnf(64, True, True, 2029),
        ),
        (
            "Homological_XOR3_MAJ3_6Local_V44",
            lambda: gen_homological_xormaj3_expander_3cnf(44, False, True, 2030),
        ),
        (
            "PHP12_11_OR2_Homological_XOR3_MAJ3_V36",
            lambda: gen_hybrid_php_homological_xormaj3_3cnf(12, 11, 36, 2, True, True, 2031),
        ),
    ]

    results = []
    for name, gen_fn in suite:
        nv, raw_cls = gen_fn()
        nv_s, cls_s = scramble_cnf(nv, raw_cls, seed=9100 + len(results))
        cnf_p = args.out_dir / f"{name}.cnf"
        pbp_p = args.out_dir / f"{name}.pbp"
        stats = certify_veronese_prg_veripb(nv_s, cls_s, cnf_p, pbp_p)
        tv0 = time.perf_counter()
        proc = subprocess.run(
            [args.veripb_bin, "--cnf", str(cnf_p), str(pbp_p)],
            capture_output=True,
            text=True,
            check=False,
        )
        veripb_ms = round((time.perf_counter() - tv0) * 1000.0, 2)
        verified = "s VERIFIED UNSATISFIABLE" in proc.stdout
        if not verified:
            raise RuntimeError(
                f"VeriPB failed on {name}:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
            )
        rec = {
            "instance": name,
            **stats,
            "veripb_ms": veripb_ms,
            "total_ms": round(float(stats["emit_ms"]) + veripb_ms, 2),
            "verdict": "s VERIFIED UNSATISFIABLE",
        }
        results.append(rec)
        print(
            f"[VERIFIED] {name}: vars={nv_s} cls={len(cls_s)} |S|={stats['separator_size']} "
            f"ext={stats['n_extension_vars']} pbp_lines={stats['pbp_lines']} "
            f"emit={stats['emit_ms']}ms + veripb={veripb_ms}ms = {rec['total_ms']}ms",
            flush=True,
        )

    args.json_out.write_text(json.dumps(results, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
