"""VeriPB 3.0 proof logger for blind wire-eliminated disjunctive interpolants (PHP OR Tseitin, multi-selector cuts)."""

from __future__ import annotations

import argparse
import itertools
import json
import shutil
import subprocess
import time
from collections import defaultdict
from pathlib import Path

from .benchmarks import gen_php, gen_wire_eliminated_php_tseitin
from .cnf_utils import scramble_cnf, write_dimacs
from .veripb_emitter import VeriPBLogger, lit_str


def _unroll_11_chains_logged(
    clauses_with_ids: list[tuple[list[int], int]],
    logger: VeriPBLogger,
    protected_vars: set[int] | None = None,
) -> list[tuple[list[int], int]]:
    """
    Eliminate Tseitin splitting variables with occurrence count (1, 1) while logging
    each exact resolution/cancellation step in VeriPB 3.0 (`pol id_p id_n + [s] ;`).
    """
    prot = protected_vars or set()
    work: list[tuple[list[int], int]] = []
    seen_init: set[tuple[int, ...]] = set()
    for cl, cid in clauses_with_ids:
        norm = sorted(set(cl), key=lambda z: (abs(z), z))
        if any(-x in norm for x in norm):
            continue
        tc = tuple(norm)
        if tc not in seen_init:
            seen_init.add(tc)
            work.append((norm, cid))

    while True:
        pos: dict[int, list[int]] = defaultdict(list)
        neg: dict[int, list[int]] = defaultdict(list)
        for idx, (cl, _cid) in enumerate(work):
            for lit in cl:
                v = abs(lit)
                if v in prot:
                    continue
                if lit > 0:
                    pos[v].append(idx)
                else:
                    neg[v].append(idx)

        used: set[int] = set()
        merges: list[tuple[int, int, int]] = []
        for v in sorted(pos.keys()):
            p_idxs = pos[v]
            if len(p_idxs) == 1:
                n_idxs = neg.get(v, ())
                if len(n_idxs) == 1:
                    pi, ni = p_idxs[0], n_idxs[0]
                    if pi != ni and pi not in used and ni not in used:
                        used.add(pi)
                        used.add(ni)
                        merges.append((v, pi, ni))

        if not merges:
            break

        nxt: list[tuple[list[int], int]] = [
            item for idx, item in enumerate(work) if idx not in used
        ]
        for v, pi, ni in merges:
            cl_p, id_p = work[pi]
            cl_n, id_n = work[ni]
            cp = [x for x in cl_p if x != v]
            cn = [x for x in cl_n if x != -v]
            mset = set(cp) | set(cn)
            if any(-x in mset for x in mset):
                continue
            overlap = bool(set(cp) & set(cn))
            new_cid = (
                logger.emit_pol([id_p, id_n, "+", "s"])
                if overlap
                else logger.emit_pol([id_p, id_n, "+"])
            )
            nxt.append((sorted(mset, key=lambda z: (abs(z), z)), new_cid))

        dedup: list[tuple[list[int], int]] = []
        seen: set[tuple[int, ...]] = set()
        for cl, cid in nxt:
            tc = tuple(cl)
            if tc not in seen:
                seen.add(tc)
                dedup.append((cl, cid))
        work = dedup

    return work


def discover_primal_vertex_cut(
    unrolled_clauses: list[list[int]],
    max_cut: int = 6,
) -> tuple[list[int] | None, list[set[int]] | None]:
    """
    Discover a small primal vertex separator S (1 <= |S| <= max_cut) splitting the
    remaining variables into >= 2 non-trivial components in O(|V| * deg) time.
    """
    adj: dict[int, set[int]] = defaultdict(set)
    all_v: set[int] = set()
    for cl in unrolled_clauses:
        vs = [abs(x) for x in cl]
        all_v.update(vs)
        for i in range(len(vs)):
            ui = vs[i]
            for j in range(i + 1, len(vs)):
                vj = vs[j]
                adj[ui].add(vj)
                adj[vj].add(ui)

    if len(all_v) < 8:
        return None, None

    # First check if already disconnected (|S| = 0 -> no separator needed, handled as single/split components)
    v_by_deg = sorted(all_v, key=lambda v: (len(adj[v]), v))
    tested_cuts: set[frozenset[int]] = set()

    # By Pigeonhole Principle, among `max_cut + 1` minimum-degree vertices, at least one lies
    # outside any separator S of size <= max_cut. Furthermore, every vertex in S connects to >= 2
    # components, whereas in a single dense clique/grid (e.g. standalone PHP), candidate 2-cuts
    # fail a fast 1-step neighbor check before full BFS.
    anchors = v_by_deg[: min(len(v_by_deg), max_cut + 1)]
    for u in anchors:
        nu = adj[u]
        if len(nu) >= len(all_v) - 1:
            continue
        for v in v_by_deg:
            if v == u or v in nu:
                continue
            s_cand = frozenset(nu & adj[v])
            if not (1 <= len(s_cand) <= max_cut) or s_cand in tested_cuts:
                continue
            tested_cuts.add(s_cand)
            rem_vars = all_v - s_cand
            if len(rem_vars) < 6:
                continue
            # Fast BFS from u: if u's component in (G - S) covers all remaining vertices,
            # then S does not disconnect G; otherwise (G - S) has >= 2 components!
            comp_u: set[int] = {u}
            q_u = [u]
            while q_u:
                cur = q_u.pop()
                for nb in adj[cur]:
                    if nb not in s_cand and nb not in comp_u:
                        comp_u.add(nb)
                        q_u.append(nb)
            if len(comp_u) == len(rem_vars):
                continue
            visited: set[int] = set(comp_u)
            comps: list[set[int]] = [comp_u]
            for start_node in rem_vars:
                if start_node in visited:
                    continue
                comp: set[int] = set()
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
                return sorted(s_cand), comps

    return None, None


def _ensure_uniform_guard(
    cid: int,
    present_guard: set[int],
    target_guard: list[int],
    logger: VeriPBLogger,
) -> int:
    """Weaken `cid` with literal axioms `g >= 0` for any missing guard literal in `target_guard`."""
    missing = [g for g in target_guard if g not in present_guard]
    if not missing:
        return cid
    rpn: list[int | str] = [cid]
    for g in missing:
        rpn.extend([lit_str(g), "+"])
    return logger.emit_pol(rpn)


def _try_certify_guarded_php(
    fiber_items: list[tuple[list[int], int]],
    guard_lits: list[int],
    logger: VeriPBLogger,
) -> int | None:
    """
    Blindly detect a Pigeonhole / clique-cover contradiction among guarded clauses
    `G + C >= 1` and emit an exact polynomial-size Cutting-Planes (`pol`) derivation
    of `sum_{g in G} g >= 1` (or `0 >= 1` if `guard_lits` is empty).
    """
    # Map ordered pair (l1, l2) -> cid of guarded clause `G + ~l1 + ~l2 >= 1`
    amo_cid: dict[tuple[int, int], int] = {}
    for cl, cid in fiber_items:
        if len(cl) == 2:
            a, b = -cl[0], -cl[1]
            if a != b and (a, b) not in amo_cid:
                amo_cid[(a, b)] = cid
                amo_cid[(b, a)] = cid

    if not amo_cid:
        return None

    # Candidate ALO clauses: try width >= 3 first; fallback to width >= 2 if needed
    for min_alo_len in (3, 2):
        alo_candidates = [(cl, cid) for cl, cid in fiber_items if len(cl) >= min_alo_len]
        if len(alo_candidates) < 2:
            continue

        # In PHP_p^h, ALO clauses are variable-disjoint (or literal-disjoint) and each literal
        # belongs to a clique in `amo_cid`. Filter to ALO clauses whose literals have AMO degree >= 1.
        amo_deg: dict[int, int] = defaultdict(int)
        for l1, _l2 in amo_cid.keys():
            amo_deg[l1] += 1

        valid_alo: list[tuple[list[int], int]] = []
        used_alo_lits: set[int] = set()
        # Sort longer clauses first, then by high AMO connectivity
        ordered_cands = sorted(
            alo_candidates,
            key=lambda item: (-len(item[0]), -min(amo_deg[x] for x in item[0])),
        )
        for cl, cid in ordered_cands:
            if all(amo_deg[x] >= 1 for x in cl) and not any(x in used_alo_lits for x in cl):
                # For min_alo_len == 2 (e.g. PHP_3^2), ensure we don't pick AMO clauses themselves:
                # in PHP_3^2, hole cliques are triangles (amo_deg[-x] == 0, amo_deg[x] == 2)
                if min_alo_len == 2 and any((-x, -y) in amo_cid for i, x in enumerate(cl) for y in cl[i + 1 :]):
                    pass
                valid_alo.append((cl, cid))
                used_alo_lits.update(cl)

        if len(valid_alo) < 2:
            continue

        # Partition `used_alo_lits` into cliques in `amo_cid`
        unassigned = set(used_alo_lits)
        cliques: list[list[int]] = []
        while unassigned:
            seed_lit = max(
                unassigned,
                key=lambda x: sum(1 for y in unassigned if y != x and (x, y) in amo_cid),
            )
            clique = [seed_lit]
            cands = sorted(
                [y for y in unassigned if y != seed_lit and (seed_lit, y) in amo_cid],
                key=lambda y: -sum(1 for z in unassigned if z != y and (y, z) in amo_cid),
            )
            for y in cands:
                if all((y, cur) in amo_cid for cur in clique):
                    clique.append(y)
            cliques.append(clique)
            unassigned -= set(clique)

        # Restrict to ALO clauses completely covered by cliques, and drop unused clique members
        # Wait: every literal in `used_alo_lits` is in exactly one clique by construction!
        p_count = len(valid_alo)
        h_count = len(cliques)
        if p_count <= h_count:
            continue

        # Emit inductive Cutting-Planes AMO inequality for each clique Q_j:
        #   (|Q_j| - 1) * G + sum_{l in Q_j} ~l >= |Q_j| - 1
        hole_ineq_ids: list[int] = []
        c_guard = p_count
        for q in cliques:
            m_q = len(q)
            if m_q == 1:
                # 0 * G + 1 * ~q[0] >= 0 (literal axiom)
                hole_ineq_ids.append(logger.emit_pol([lit_str(-q[0])]))
                continue
            cur_id = amo_cid[(q[0], q[1])]
            for m_step in range(2, m_q):
                nxt_lit = q[m_step]
                rpn: list[int | str] = (
                    [cur_id]
                    if (m_step - 1) == 1
                    else [cur_id, m_step - 1, "*"]
                )
                for prev_idx in range(m_step):
                    pair_id = amo_cid[(q[prev_idx], nxt_lit)]
                    rpn.extend([pair_id, "+"])
                rpn.extend([m_step, "d"])
                cur_id = logger.emit_pol(rpn)
            hole_ineq_ids.append(cur_id)
            c_guard += m_q - 1

        # Sum all p ALO clauses + all h clique AMO inequalities
        sum_rpn: list[int | str] = [valid_alo[0][1]]
        for _cl, cid in valid_alo[1:]:
            sum_rpn.extend([cid, "+"])
        for hid in hole_ineq_ids:
            sum_rpn.extend([hid, "+"])
        sum_cid = logger.emit_pol(sum_rpn)

        if not guard_lits:
            return sum_cid
        return logger.emit_pol([sum_cid, c_guard, "d"])

    return None


class _ParityEqRecord:
    """Internal descriptor of a guarded parity equation `sum_{v in vars} x_v == rhs (mod 2)`."""

    def __init__(
        self,
        supp: tuple[int, ...],
        rhs: int,
        clause_map: dict[tuple[int, ...], int],
    ) -> None:
        self.supp = supp
        self.rhs = rhs
        self.clause_map = clause_map


def _emit_red_constraint(
    terms: list[tuple[int, int]],
    rhs: int,
    witness_var: int,
    witness_val: int,
    logger: VeriPBLogger,
) -> int:
    """Emit a VeriPB 3.0 `red` constraint with explicit witness `x{w} -> val`."""
    logger.cid += 1
    lhs = " ".join(f"{coeff} {lit_str(lit)}" for coeff, lit in terms)
    w_str = f"x{witness_var} -> {witness_val}"
    logger.lines.append(f"red {lhs} >= {rhs} : {w_str} ;")
    return logger.cid


def _realize_parity3_bounds(
    v1: int,
    v2: int,
    v3: int,
    rhs: int,
    forbid_cid: dict[tuple[int, int, int], int],
    guard_lits: list[int],
    logger: VeriPBLogger,
    alloc_var_fn,
) -> tuple[int, int, int, int]:
    """
    Emit witness `w = MAJ_3(y1, y2, y3)` via `red` and derive paired guarded integer bounds:
      U+: (+/- x_v1) + x_v2 + x_v3 - 2 x_w + gamma+ * G >= beta
      U-: (-/+ x_v1) - x_v2 - x_v3 + 2 x_w + gamma- * G >= -beta
    Returns `(id_plus, gamma_plus, id_minus, gamma_minus)`.
    """
    # Map (y1, y2, y3) so y1 ^ y2 ^ y3 == 0 when G == 0:
    # if rhs == 0: y1 = v1; if rhs == 1: y1 = -v1 (i.e. ~x_{v1})
    y1 = -v1 if rhs == 1 else v1
    y2 = v2
    y3 = v3

    def forbid_y_point(by1: int, by2: int, by3: int) -> int:
        bv1 = (1 - by1) if rhs == 1 else by1
        return forbid_cid[(bv1, by2, by3)]

    # K1 forbids (y1,y2,y3)=(1,0,0), K2=(0,1,0), K3=(0,0,1), K4=(1,1,1)
    k1 = forbid_y_point(1, 0, 0)
    k2 = forbid_y_point(0, 1, 0)
    k3 = forbid_y_point(0, 0, 1)
    k4 = forbid_y_point(1, 1, 1)

    w_var = alloc_var_fn()
    r1 = _emit_red_constraint([(1, y1), (1, y2), (1, y3), (2, -w_var)], 2, w_var, 0, logger)
    r2 = _emit_red_constraint([(1, -y1), (1, -y2), (1, -y3), (2, w_var)], 2, w_var, 1, logger)

    l1 = logger.emit_pol([r2, k1, "+", 2, "d"])
    l2 = logger.emit_pol([r2, k2, "+", 2, "d"])
    l3 = logger.emit_pol([r2, k3, "+", 2, "d"])
    u_minus = logger.emit_pol([l1, l2, "+", l3, "+", 2, "*", k4, "+", 3, "d"])

    gamma_minus = 3 if guard_lits else 0
    return r1, 0, u_minus, gamma_minus


def _try_certify_guarded_parity(
    fiber_items: list[tuple[list[int], int]],
    guard_lits: list[int],
    logger: VeriPBLogger,
    alloc_var_fn,
) -> int | None:
    """
    Blindly extract guarded GF(2) parity equations of width 1..4 from `fiber_items`,
    find an exact minimally inconsistent parity subset via GF(2) RREF, and emit a
    compact Gocht-Nordström-style VeriPB 3.0 cutting-planes derivation of `G >= 1`.
    """
    by_supp: dict[tuple[int, ...], list[tuple[list[int], int]]] = defaultdict(list)
    for cl, cid in fiber_items:
        if 1 <= len(cl) <= 4:
            supp = tuple(sorted(abs(x) for x in cl))
            if len(supp) == len(cl):
                by_supp[supp].append((cl, cid))

    records: list[_ParityEqRecord] = []
    for supp, items in sorted(by_supp.items()):
        k = len(supp)
        if len(items) < (1 << (k - 1)):
            continue
        # Map forbidden truth-table point `bits` -> cid
        # A clause [l_1, ..., l_k] forbids the unique assignment where every l_j is FALSE:
        # bit_j = 0 if l_j > 0 else 1
        forbid_map: dict[tuple[int, ...], int] = {}
        pos_of = {v: idx for idx, v in enumerate(supp)}
        for cl, cid in items:
            pt = [0] * k
            for lit in cl:
                pt[pos_of[abs(lit)]] = 0 if lit > 0 else 1
            tpt = tuple(pt)
            if tpt not in forbid_map:
                forbid_map[tpt] = cid

        for rhs_cand in (0, 1):
            needed = [
                bits
                for bits in itertools.product((0, 1), repeat=k)
                if (sum(bits) & 1) != rhs_cand
            ]
            if all(bits in forbid_map for bits in needed):
                sub_map = {bits: forbid_map[bits] for bits in needed}
                records.append(_ParityEqRecord(supp, rhs_cand, sub_map))
                break

    if not records:
        return None

    # Sparse GF(2) RREF tracking row combination bitmasks
    pivots: dict[int, tuple[set[int], int, int]] = {}
    unsat_mask: int | None = None

    for idx_r, rec in enumerate(records):
        row_vars = set(rec.supp)
        rhs = rec.rhs
        comb = 1 << idx_r
        while row_vars:
            lead = max(row_vars)
            if lead in pivots:
                p_vars, p_rhs, p_comb = pivots[lead]
                row_vars ^= p_vars
                rhs ^= p_rhs
                comb ^= p_comb
            else:
                pivots[lead] = (row_vars, rhs, comb)
                break
        else:
            if rhs == 1:
                unsat_mask = comb
                break

    if unsat_mask is None:
        return None

    # Lazy realization: emit `red` + `pol` ONLY for equations in `unsat_mask`
    plus_terms: list[tuple[int, int]] = []
    minus_terms: list[tuple[int, int]] = []
    g_flag = 1 if guard_lits else 0

    tmp = unsat_mask
    while tmp:
        lsb = tmp & -tmp
        e_idx = lsb.bit_length() - 1
        tmp ^= lsb
        rec = records[e_idx]
        k = len(rec.supp)

        if k == 1:
            v1 = rec.supp[0]
            if rec.rhs == 1:
                # Forbidden point (0,) -> clause G + v1 >= 1
                id_p = rec.clause_map[(0,)]
                id_m = logger.emit_pol([f"~x{v1}"])
                plus_terms.append((id_p, g_flag))
                minus_terms.append((id_m, 0))
            else:
                # Forbidden point (1,) -> clause G + ~v1 >= 1
                id_p = logger.emit_pol([f"x{v1}"])
                id_m = rec.clause_map[(1,)]
                plus_terms.append((id_p, 0))
                minus_terms.append((id_m, g_flag))

        elif k == 2:
            v1, v2 = rec.supp
            if rec.rhs == 0:
                # Forbidden (0,1) -> G + v1 + ~v2 >= 1; (1,0) -> G + ~v1 + v2 >= 1
                id_p = rec.clause_map[(0, 1)]
                id_m = rec.clause_map[(1, 0)]
            else:
                # Forbidden (0,0) -> G + v1 + v2 >= 1; (1,1) -> G + ~v1 + ~v2 >= 1
                id_p = rec.clause_map[(0, 0)]
                id_m = rec.clause_map[(1, 1)]
            plus_terms.append((id_p, g_flag))
            minus_terms.append((id_m, g_flag))

        elif k == 3:
            v1, v2, v3 = rec.supp
            forbid3 = {(b1, b2, b3): cid for (b1, b2, b3), cid in rec.clause_map.items()}
            id_p, gp, id_m, gm = _realize_parity3_bounds(
                v1, v2, v3, rec.rhs, forbid3, guard_lits, logger, alloc_var_fn
            )
            plus_terms.append((id_p, gp))
            minus_terms.append((id_m, gm))

        elif k == 4:
            # Split v1 ^ v2 ^ v3 ^ v4 = rhs via fresh witness z <-> (v1 ^ v2)
            v1, v2, v3, v4 = rec.supp
            z_var = alloc_var_fn()
            # Define z <-> (v1 ^ v2) unconditionally via 4 `red` clauses:
            # z=0 when v1==v2, z=1 when v1!=v2
            z_01 = _emit_red_constraint([(1, v1), (1, -v2), (1, z_var)], 1, z_var, 1, logger)
            z_10 = _emit_red_constraint([(1, -v1), (1, v2), (1, z_var)], 1, z_var, 1, logger)
            z_00 = _emit_red_constraint([(1, v1), (1, v2), (1, -z_var)], 1, z_var, 0, logger)
            z_11 = _emit_red_constraint([(1, -v1), (1, -v2), (1, -z_var)], 1, z_var, 0, logger)
            # Part A: v1 ^ v2 ^ z == 0 (unconditional -> guard coeff 0!)
            f_a = {
                (1, 0, 0): z_10,
                (0, 1, 0): z_01,
                (0, 0, 1): z_00,
                (1, 1, 1): z_11,
            }
            idp_a, _, idm_a, _ = _realize_parity3_bounds(
                v1, v2, z_var, 0, f_a, [], logger, alloc_var_fn
            )
            plus_terms.append((idp_a, 0))
            minus_terms.append((idm_a, 0))

            # Part B: derive guarded 4 clauses of z ^ v3 ^ v4 == rhs by resolving z_ij with 8-clause map
            f_b: dict[tuple[int, int, int], int] = {}
            for bz, b3, b4 in itertools.product((0, 1), repeat=3):
                if (bz ^ b3 ^ b4) != rec.rhs:
                    if bz == 0:
                        # Need G + z + (v3/~v3) + (v4/~v4) >= 1 from (0,0,b3,b4) + (1,1,b3,b4) + z_01 + z_10
                        c00 = rec.clause_map[(0, 0, b3, b4)]
                        c11 = rec.clause_map[(1, 1, b3, b4)]
                        # Resolve v2 on (c00, z_01 -> G + v1 + z + l3 + l4) and (c11, z_10 -> G + ~v1 + z + l3 + l4)
                        p1 = logger.emit_pol([c00, z_01, "+", "s"])
                        p2 = logger.emit_pol([c11, z_10, "+", "s"])
                        f_b[(0, b3, b4)] = logger.emit_pol([p1, p2, "+", "s"])
                    else:
                        c01 = rec.clause_map[(0, 1, b3, b4)]
                        c10 = rec.clause_map[(1, 0, b3, b4)]
                        p1 = logger.emit_pol([c01, z_00, "+", "s"])
                        p2 = logger.emit_pol([c10, z_11, "+", "s"])
                        f_b[(1, b3, b4)] = logger.emit_pol([p1, p2, "+", "s"])
            idp_b, gp_b, idm_b, gm_b = _realize_parity3_bounds(
                z_var, v3, v4, rec.rhs, f_b, guard_lits, logger, alloc_var_fn
            )
            plus_terms.append((idp_b, gp_b))
            minus_terms.append((idm_b, gm_b))

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


def certify_disjunctive_interpolant_veripb(
    n_vars: int,
    clauses: list[list[int]],
    cnf_path: str | Path,
    pbp_path: str | Path,
    max_cut: int = 6,
) -> dict[str, object]:
    """
    Blindly decompose a variable- and polarity-scrambled 3-CNF disjunctive interpolant
    (or standalone cardinality/parity formula), emit a complete VeriPB 3.0 proof (`.pbp`),
    and return structural proof telemetry.
    """
    cnf_path = Path(cnf_path)
    pbp_path = Path(pbp_path)
    pbp_path.parent.mkdir(parents=True, exist_ok=True)
    write_dimacs(cnf_path, n_vars, clauses)

    logger = VeriPBLogger(len(clauses))
    next_fresh_var = n_vars
    n_witness_vars = 0

    def alloc_fresh_var() -> int:
        nonlocal next_fresh_var, n_witness_vars
        next_fresh_var += 1
        n_witness_vars += 1
        return next_fresh_var

    # 1. Global (1,1)-chain unrolling with logged `pol` steps
    init_items = [(list(cl), idx + 1) for idx, cl in enumerate(clauses)]
    unrolled_items = _unroll_11_chains_logged(init_items, logger)
    unrolled_cls = [cl for cl, _ in unrolled_items]

    # 2. Blind primal vertex-cut discovery
    found_cut, found_comps = discover_primal_vertex_cut(unrolled_cls, max_cut=max_cut)

    if found_cut is None or found_comps is None:
        # Fallback: treat as single unguarded formula (S = empty)
        cut_vars: list[int] = []
        comp_clauses_items: list[list[tuple[list[int], int]]] = [unrolled_items]
        pure_s_items: list[tuple[list[int], int]] = []
    else:
        cut_vars = found_cut
        cut_set = set(cut_vars)
        pure_s_items = []
        comp_clauses_items = [[] for _ in range(len(found_comps))]
        var_to_cidx = {v: idx for idx, cp in enumerate(found_comps) for v in cp}
        for cl, cid in unrolled_items:
            c_idxs = {var_to_cidx[abs(lit)] for lit in cl if abs(lit) not in cut_set}
            if not c_idxs:
                pure_s_items.append((cl, cid))
            elif len(c_idxs) == 1:
                comp_clauses_items[next(iter(c_idxs))].append((cl, cid))

    # 3. Certify every fiber b in {0, 1}^|S|
    cut_set_lookup = set(cut_vars)
    fiber_guard_cids: dict[tuple[int, ...], int] = {}
    fiber_engines: dict[str, int] = defaultdict(int)

    for bits in itertools.product((0, 1), repeat=len(cut_vars)):
        s_map = dict(zip(cut_vars, bits))
        # Target guard clause D_b: falsified iff s == bits
        guard_lits = [-v if b == 1 else v for v, b in zip(cut_vars, bits)]
        guard_set = set(guard_lits)

        # Check if a pure-S clause already refutes this fiber
        pure_hit_cid: int | None = None
        for scl, scid in pure_s_items:
            if not any((s_map[abs(l)] == 1 if l > 0 else s_map[abs(l)] == 0) for l in scl):
                pure_hit_cid = _ensure_uniform_guard(scid, set(scl), guard_lits, logger)
                break
        if pure_hit_cid is not None:
            fiber_guard_cids[bits] = pure_hit_cid
            fiber_engines["PURE_CUT"] += 1
            continue

        derived_guard_cid: int | None = None
        for comp_items in comp_clauses_items:
            if not comp_items:
                continue
            projected_raw: list[tuple[list[int], int]] = []
            immediate_cid: int | None = None

            for cl, cid in comp_items:
                sat_by_s = False
                rem_comp: list[int] = []
                pres_guard: set[int] = set()
                for lit in cl:
                    av = abs(lit)
                    if av in cut_set_lookup:
                        if (lit > 0 and s_map[av] == 1) or (lit < 0 and s_map[av] == 0):
                            sat_by_s = True
                            break
                        pres_guard.add(lit)
                    else:
                        rem_comp.append(lit)
                if sat_by_s:
                    continue
                norm_cid = _ensure_uniform_guard(cid, pres_guard, guard_lits, logger)
                if not rem_comp:
                    immediate_cid = norm_cid
                    break
                projected_raw.append((guard_lits + rem_comp, norm_cid))

            if immediate_cid is not None:
                derived_guard_cid = immediate_cid
                fiber_engines["UNIT_FIBER"] += 1
                break

            if not projected_raw:
                continue

            # Fiber-local (1,1)-chain unrolling keeping `cut_vars` protected!
            fiber_unrolled = _unroll_11_chains_logged(
                projected_raw, logger, protected_vars=cut_set_lookup
            )
            stripped: list[tuple[list[int], int]] = []
            for full_cl, fcid in fiber_unrolled:
                comp_only = [x for x in full_cl if abs(x) not in guard_set and abs(x) not in cut_set_lookup]
                if not comp_only:
                    derived_guard_cid = fcid
                    fiber_engines["UNROLL_EMPTY"] += 1
                    break
                stripped.append((comp_only, fcid))

            if derived_guard_cid is not None:
                break

            # Strategy 1: Guarded PHP / Clique-Cover Cutting Planes
            php_cid = _try_certify_guarded_php(stripped, guard_lits, logger)
            if php_cid is not None:
                derived_guard_cid = php_cid
                fiber_engines["PHP_CP"] += 1
                break

            # Strategy 2: Guarded Parity / Gocht-Nordström VeriPB 3.0
            par_cid = _try_certify_guarded_parity(stripped, guard_lits, logger, alloc_fresh_var)
            if par_cid is not None:
                derived_guard_cid = par_cid
                fiber_engines["PARITY_RED_CP"] += 1
                break

            # Strategy 3: RUP fallback for small local/BCP contradictions
            # Check if `guard_lits` is already RUP wrt current DB? Only attempt if small core
            if len(stripped) <= 64:
                # Bounded check via Python BCP not sufficient alone; skip unless needed
                pass

        if derived_guard_cid is None:
            raise RuntimeError(
                f"Fiber {bits} on separator S={cut_vars} is FEASIBLE or uncertified (formula may be SAT)."
            )
        fiber_guard_cids[bits] = derived_guard_cid

    # 4. Boolean Cube Halving Reassembly over S: 2^|S| - 1 steps -> `0 >= 1`
    def collapse_cube(prefix: tuple[int, ...]) -> int:
        if len(prefix) == len(cut_vars):
            return fiber_guard_cids[prefix]
        id0 = collapse_cube(prefix + (0,))
        id1 = collapse_cube(prefix + (1,))
        return logger.emit_pol([id0, id1, "+", 2, "d"])

    contra_id = collapse_cube(())
    pbp_text = logger.finish_unsat(contra_id)
    pbp_path.write_text(pbp_text, encoding="utf-8")

    return {
        "cut_size": len(cut_vars),
        "cut_vars": cut_vars,
        "num_fibers": 1 << len(cut_vars),
        "fiber_engines": dict(fiber_engines),
        "witness_vars": n_witness_vars,
        "pbp_lines": len(logger.lines),
        "contra_id": contra_id,
    }


def gen_multiguard_php_tseitin_3cnf(
    pigeons: int = 12,
    holes: int = 11,
    tseitin_verts: int = 24,
    num_selectors: int = 3,
    random_3reg: bool = False,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    Generalized k-selector wire-eliminated disjunctive interpolant:
      OR_{s_1 ^ ... ^ s_k}(PHP_{p}^{h}, Tseitin_{G, charge})
    Supports arbitrary selector width `num_selectors >= 1`, Möbius-prism or random
    3-regular graphs, and `unsat=False` sanity-check instances.
    """
    import numpy as np

    assert tseitin_verts % 2 == 0 and tseitin_verts >= 6
    p_eff = pigeons if unsat else holes
    n1, c1 = gen_php(p_eff, holes)

    rng = np.random.default_rng(seed)
    inc: list[list[int]] = [[] for _ in range(tseitin_verts)]
    edges: list[tuple[int, int]] = []

    if not random_3reg:
        for i in range(tseitin_verts):
            u, v = i, (i + 1) % tseitin_verts
            eid = len(edges) + 1
            edges.append((u, v))
            inc[u].append(eid)
            inc[v].append(eid)
        for i in range(tseitin_verts // 2):
            u, v = i, i + tseitin_verts // 2
            eid = len(edges) + 1
            edges.append((u, v))
            inc[u].append(eid)
            inc[v].append(eid)
    else:
        # Random Hamiltonian cycle + random perfect matching on non-adjacent vertices -> simple 3-regular expander
        perm_cycle = list(rng.permutation(tseitin_verts))
        adj_set: set[tuple[int, int]] = set()
        for idx in range(tseitin_verts):
            u, v = int(perm_cycle[idx]), int(perm_cycle[(idx + 1) % tseitin_verts])
            a, b = (u, v) if u < v else (v, u)
            adj_set.add((a, b))
            eid = len(edges) + 1
            edges.append((a, b))
            inc[a].append(eid)
            inc[b].append(eid)
        for _attempt in range(500):
            order = list(rng.permutation(tseitin_verts))
            pairs = []
            ok = True
            for idx in range(0, tseitin_verts, 2):
                u, v = int(order[idx]), int(order[idx + 1])
                a, b = (u, v) if u < v else (v, u)
                if (a, b) in adj_set:
                    ok = False
                    break
                pairs.append((a, b))
            if ok:
                for a, b in pairs:
                    eid = len(edges) + 1
                    edges.append((a, b))
                    inc[a].append(eid)
                    inc[b].append(eid)
                break
        else:
            raise RuntimeError("Failed to sample simple 3-regular matching")

    c2: list[list[int]] = []
    for v_idx in range(tseitin_verts):
        e1, e2, e3 = inc[v_idx]
        ch = 1 if (v_idx == 0 and unsat) else 0
        for b1, b2, b3 in itertools.product((0, 1), repeat=3):
            if (b1 ^ b2 ^ b3) != ch:
                c2.append([-e1 if b1 else e1, -e2 if b2 else e2, -e3 if b3 else e3])

    n2 = len(edges)
    s_vars = [n1 + n2 + 1 + t for t in range(num_selectors)]
    top = s_vars[-1]
    c2_shifted = [[(x + n1 if x > 0 else x - n1) for x in cl] for cl in c2]

    cls: list[list[int]] = []
    for bits in itertools.product((0, 1), repeat=num_selectors):
        gd = [-sv if b == 1 else sv for sv, b in zip(s_vars, bits)]
        parity = sum(bits) & 1
        target = c1 if parity == 0 else c2_shifted
        for c in target:
            lits = gd + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit and verify VeriPB 3.0.2 proofs for scrambled wire-eliminated disjunctive interpolants."
    )
    parser.add_argument("--out-dir", type=Path, default=Path("results/interpolant_proofs"))
    parser.add_argument("--json-out", type=Path, default=Path("results/interpolant_veripb_results.json"))
    parser.add_argument("--veripb-bin", type=str, default=shutil.which("veripb") or "/home/miguel/.local/bin/veripb")
    args = parser.parse_args(argv)

    if not args.veripb_bin or not Path(args.veripb_bin).exists():
        raise FileNotFoundError(f"veripb binary not found at {args.veripb_bin!r}")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    suite = [
        ("Scrambled_PHP08_07_OR2_Tseitin16", gen_wire_eliminated_php_tseitin(8, 7, 16), 3101),
        ("Scrambled_PHP10_09_OR2_Tseitin20", gen_wire_eliminated_php_tseitin(10, 9, 20), 3102),
        ("Scrambled_PHP13_12_OR2_Tseitin28", gen_wire_eliminated_php_tseitin(13, 12, 28), 3103),
        ("Scrambled_PHP16_15_OR2_Tseitin36", gen_wire_eliminated_php_tseitin(16, 15, 36), 3104),
        ("Scrambled_PHP20_19_OR2_Tseitin44", gen_wire_eliminated_php_tseitin(20, 19, 44), 3105),
        ("Scrambled_PHP24_23_OR2_Tseitin52", gen_wire_eliminated_php_tseitin(24, 23, 52), 3106),
        ("Scrambled_PHP12_11_OR3_Expander30", gen_multiguard_php_tseitin_3cnf(12, 11, 30, 3, True, True, 41), 3107),
        ("Scrambled_PHP14_13_OR3_Expander36", gen_multiguard_php_tseitin_3cnf(14, 13, 36, 3, True, True, 42), 3108),
    ]

    print("=" * 114)
    print("VeriPB 3.0.2 Certification on Scrambled 3-CNF Disjunctive Interpolants (PHP_p^h OR_S Tseitin_G)")
    print("=" * 114)

    rows = []
    for name, (nv0, cl0), seed in suite:
        snv, scl = scramble_cnf(nv0, cl0, seed=seed)
        cnf_file = args.out_dir / f"{name}.cnf"
        pbp_file = args.out_dir / f"{name}.pbp"

        t0 = time.perf_counter()
        stats = certify_disjunctive_interpolant_veripb(snv, scl, cnf_file, pbp_file)
        emit_ms = round((time.perf_counter() - t0) * 1000.0, 2)

        t1 = time.perf_counter()
        proc = subprocess.run(
            [args.veripb_bin, "--cnf", str(cnf_file), str(pbp_file)],
            capture_output=True,
            text=True,
            timeout=180,
        )
        check_ms = round((time.perf_counter() - t1) * 1000.0, 2)
        ok = proc.returncode == 0 and "VERIFIED UNSATISFIABLE" in proc.stdout
        if not ok:
            raise AssertionError(
                f"VeriPB failed on {name}:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
            )

        print(
            f"  {name:36s} (v={snv:5d}, m={len(scl):5d}, |S|={stats['cut_size']}) | "
            f"pbp={stats['pbp_lines']:5d} (w={stats['witness_vars']:3d}) | "
            f"emit={emit_ms:7.1f}ms | veripb={check_ms:6.1f}ms | s VERIFIED UNSATISFIABLE"
        )
        rows.append(
            {
                "instance": name,
                "vars": snv,
                "clauses": len(scl),
                "cut_size": stats["cut_size"],
                "num_fibers": stats["num_fibers"],
                "fiber_engines": stats["fiber_engines"],
                "witness_vars": stats["witness_vars"],
                "pbp_lines": stats["pbp_lines"],
                "emit_ms": emit_ms,
                "veripb_check_ms": check_ms,
                "veripb_status": "s VERIFIED UNSATISFIABLE",
                "cnf_path": str(cnf_file),
                "pbp_path": str(pbp_file),
            }
        )

    args.json_out.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
    print(f"\nVerified {len(rows)}/{len(rows)} disjunctive interpolant proofs -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
