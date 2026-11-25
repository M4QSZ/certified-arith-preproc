"""VeriPB 3.0 proof logger for blind arithmetic adder extraction and 2-adic/GCD cutting-planes refutations."""

from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import numpy as np

from .adder_extraction import scan_deterministic_2input_gates
from .benchmarks import gen_schoolbook_vs_wallace_miter_3cnf
from .cnf_utils import apply_fixed_and_equivs_to_clauses, scramble_cnf, write_dimacs


def lit_str(lit: int) -> str:
    return f"x{lit}" if lit > 0 else f"~x{-lit}"


class VeriPBLogger:
    """Exact VeriPB 3.0 proof emitter (`.pbp`) checkable via `veripb --cnf`."""

    def __init__(self, n_clauses: int) -> None:
        self.cid = n_clauses
        self.lines: list[str] = [
            "pseudo-Boolean proof version 3.0",
            f"f {n_clauses} ;",
        ]

    def emit_rup_clause(self, lits: list[int]) -> int:
        self.cid += 1
        terms = " ".join(f"1 {lit_str(l)}" for l in lits)
        self.lines.append(f"rup {terms} >= 1 ;" if terms else "rup >= 1 ;")
        return self.cid

    def emit_pol(self, rpn_tokens: list[int | str]) -> int:
        self.cid += 1
        self.lines.append("pol " + " ".join(str(t) for t in rpn_tokens) + " ;")
        return self.cid

    def derive_clause_over_cube(self, target_lits: list[int], cube_vars: list[int]) -> int:
        base = list(dict.fromkeys(target_lits))
        for l in base:
            if -l in base:
                v = abs(l)
                return self.emit_pol([f"x{v}", f"~x{v}", "+"])

        rem_vars = [v for v in cube_vars if v not in {abs(x) for x in base}]

        def rec(idx: int, extra_lits: list[int]) -> int:
            if idx == len(rem_vars):
                return self.emit_rup_clause(base + extra_lits)
            v = rem_vars[idx]
            id_pos = rec(idx + 1, extra_lits + [v])
            id_neg = rec(idx + 1, extra_lits + [-v])
            return self.emit_pol([id_pos, id_neg, "+", 2, "d"])

        return rec(0, [])

    def derive_half_adder_z_eq(
        self, u_lit: int, w_lit: int, s_lit: int, c_lit: int, gate_inputs: list[int]
    ) -> tuple[int, int]:
        a1 = self.derive_clause_over_cube([-c_lit, u_lit], gate_inputs)
        a2 = self.derive_clause_over_cube([-c_lit, w_lit], gate_inputs)
        a3 = self.derive_clause_over_cube([-c_lit, -s_lit], gate_inputs)
        a4 = self.derive_clause_over_cube([u_lit, w_lit, -s_lit], gate_inputs)
        id_ge = self.emit_pol([a1, a2, "+", a3, "+", 2, "*", a4, "+", 3, "d"])

        d1 = self.derive_clause_over_cube([-u_lit, s_lit, c_lit], gate_inputs)
        d2 = self.derive_clause_over_cube([-w_lit, s_lit, c_lit], gate_inputs)
        b1 = self.derive_clause_over_cube([-u_lit, -w_lit, c_lit], gate_inputs)
        id_le = self.emit_pol([d1, d2, "+", b1, "+", lit_str(c_lit), "+", 2, "d"])
        return id_ge, id_le

    def derive_disjoint_or_z_eq(
        self, c1_lit: int, c2_lit: int, cout_lit: int, fa_inputs: list[int]
    ) -> tuple[int, int]:
        id_ge = self.derive_clause_over_cube([c1_lit, c2_lit, -cout_lit], fa_inputs)
        e1 = self.derive_clause_over_cube([-c1_lit, cout_lit], fa_inputs)
        e2 = self.derive_clause_over_cube([-c2_lit, cout_lit], fa_inputs)
        e3 = self.derive_clause_over_cube([-c1_lit, -c2_lit], fa_inputs)
        id_le = self.emit_pol([e1, e2, "+", e3, "+", 2, "d"])
        return id_ge, id_le

    def finish_unsat(self, contra_id: int = -1) -> str:
        self.lines.append("output NONE ;")
        self.lines.append(f"conclusion UNSAT : {contra_id} ;")
        self.lines.append("end pseudo-Boolean proof ;")
        return "\n".join(self.lines) + "\n"


def certify_adder_telescoping_veripb(
    n_vars: int,
    clauses: list[list[int]],
    cnf_path: str | Path,
    pbp_path: str | Path,
) -> int:
    """Solve scrambled 3-CNF arithmetic miter via blind adder telescoping and emit VeriPB 3.0 proof."""
    cnf_path = Path(cnf_path)
    pbp_path = Path(pbp_path)
    pbp_path.parent.mkdir(parents=True, exist_ok=True)
    write_dimacs(cnf_path, n_vars, clauses)

    logger = VeriPBLogger(len(clauses))
    fixed: dict[int, int] = {}
    equiv: dict[int, tuple[int, int]] = {}
    unit_eq_ids: dict[int, tuple[int, int, int]] = {}
    equiv_eq_ids: dict[int, tuple[int, int, int, int]] = {}

    def record_unit(v: int, val: int, id_unit: int | None = None) -> bool:
        if v in fixed:
            return fixed[v] != val
        fixed[v] = val
        if val == 1:
            id_ge = id_unit if id_unit is not None else logger.emit_rup_clause([v])
            id_le = logger.emit_pol([f"~x{v}"])
        else:
            id_ge = logger.emit_pol([f"x{v}"])
            id_le = id_unit if id_unit is not None else logger.emit_rup_clause([-v])
        unit_eq_ids[v] = (val, id_ge, id_le)
        return False

    def record_equiv(hi: int, lo: int, fl: int, ids_pair: tuple[int, int] | None = None) -> None:
        if hi in fixed or hi in equiv:
            return
        equiv[hi] = (lo, fl)
        if fl == 0:
            if ids_pair is None:
                id_ge = logger.emit_rup_clause([hi, -lo])
                id_le = logger.emit_rup_clause([-hi, lo])
            else:
                id_ge, id_le = ids_pair
        else:
            if ids_pair is None:
                id_ge = logger.emit_rup_clause([hi, lo])
                id_le = logger.emit_rup_clause([-hi, -lo])
            else:
                id_ge, id_le = ids_pair
        equiv_eq_ids[hi] = (lo, fl, id_ge, id_le)

    known_db_2cls = {
        tuple(sorted(c, key=lambda z: (abs(z), z)))
        for c in clauses
        if len(c) == 2
    }

    def sync_shortened_2clauses(work_cls: list[list[int]]) -> None:
        for c in work_cls:
            if len(c) == 2:
                tc = tuple(sorted(c, key=lambda z: (abs(z), z)))
                if tc not in known_db_2cls:
                    known_db_2cls.add(tc)
                    logger.emit_rup_clause(list(tc))

    def bcp_and_log(work_cls: list[list[int]]) -> tuple[str, list[list[int]], int | None]:
        while True:
            st, work_cls = apply_fixed_and_equivs_to_clauses(work_cls, fixed, equiv)
            if st == "UNSAT":
                cid = logger.emit_rup_clause([])
                return "UNSAT", [], cid
            sync_shortened_2clauses(work_cls)
            chg = False
            cl_set = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in work_cls}
            for c in work_cls:
                if len(c) == 1:
                    v, val = abs(c[0]), (1 if c[0] > 0 else 0)
                    if v not in fixed:
                        if record_unit(v, val):
                            return "UNSAT", [], logger.emit_rup_clause([])
                        chg = True
                elif len(c) == 2 and abs(c[0]) != abs(c[1]):
                    a, b = c[0], c[1]
                    if tuple(sorted((-a, b), key=lambda z: (abs(z), z))) in cl_set:
                        vb, valb = abs(b), (1 if b > 0 else 0)
                        if vb not in fixed:
                            if record_unit(vb, valb):
                                return "UNSAT", [], logger.emit_rup_clause([])
                            chg = True
                    if tuple(sorted((a, -b), key=lambda z: (abs(z), z))) in cl_set:
                        va, vala = abs(a), (1 if a > 0 else 0)
                        if va not in fixed:
                            if record_unit(va, vala):
                                return "UNSAT", [], logger.emit_rup_clause([])
                            chg = True
                    if tuple(sorted((-a, -b), key=lambda z: (abs(z), z))) in cl_set:
                        va, vb = abs(a), abs(b)
                        hi, lo = (va, vb) if va > vb else (vb, va)
                        fl = 1 if (a > 0) == (b > 0) else 0
                        if hi not in fixed and hi not in equiv:
                            record_equiv(hi, lo, fl)
                            chg = True
            if not chg:
                return "OK", work_cls, None

    work = [list(c) for c in clauses]

    for _ in range(10):
        st, work, cid_u = bcp_and_log(work)
        if st == "UNSAT":
            assert cid_u is not None
            pbp_path.write_text(logger.finish_unsat(cid_u), encoding="utf-8")
            return len(logger.lines)

        st_g, gates_by_in, _ = scan_deterministic_2input_gates(work)
        if st_g == "UNSAT" or gates_by_in is None:
            cid_u = logger.emit_rup_clause([])
            pbp_path.write_text(logger.finish_unsat(cid_u), encoding="utf-8")
            return len(logger.lines)

        merged = False
        for (u_v, w_v), glist in gates_by_in.items():
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
                                if fl == 0:
                                    ig = logger.derive_clause_over_cube([hi, -lo], [u_v, w_v])
                                    il = logger.derive_clause_over_cube([-hi, lo], [u_v, w_v])
                                else:
                                    ig = logger.derive_clause_over_cube([hi, lo], [u_v, w_v])
                                    il = logger.derive_clause_over_cube([-hi, -lo], [u_v, w_v])
                                record_equiv(hi, lo, fl, (ig, il))
                                merged = True
        if not merged:
            break

    st, work, cid_u = bcp_and_log(work)
    if st == "UNSAT":
        assert cid_u is not None
        pbp_path.write_text(logger.finish_unsat(cid_u), encoding="utf-8")
        return len(logger.lines)

    st_g, gates_by_in, gate_of_out = scan_deterministic_2input_gates(work)
    assert gates_by_in is not None and gate_of_out is not None

    base_z_eqs: list[tuple[dict[int, int], int, int]] = []
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

                u_lit = u_v if bu0 == 1 else -u_v
                w_lit = w_v if bw0 == 1 else -w_v
                s_lit = s_v if s_flip == 0 else -s_v
                c_lit = c_v if spec_val == 1 else -c_v

                id_ge, id_le = logger.derive_half_adder_z_eq(u_lit, w_lit, s_lit, c_lit, [u_v, w_v])

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
                base_z_eqs.append((dict(row), id_ge, id_le))

    for cout_v, (c1_v, c2_v, t_out) in gate_of_out.items():
        if c1_v in gate_of_out and c2_v in gate_of_out:
            p1, t1 = gate_of_out[c1_v][:2], gate_of_out[c1_v][2]
            p2, t2 = gate_of_out[c2_v][:2], gate_of_out[c2_v][2]
            found_dc = False
            for pa, _ta, pb, _tb, first_is_1 in [(p1, t1, p2, t2, True), (p2, t2, p1, t1, False)]:
                for x_wire, tx in xor_on_pair.get(pa, ()):
                    if x_wire in pb:
                        reachable = set()
                        x_pos = 0 if pb[0] == x_wire else 1
                        ta_use = t1 if first_is_1 else t2
                        tb_use = t2 if first_is_1 else t1
                        for ba in (0, 1):
                            for bb in (0, 1):
                                bx = tx[(ba << 1) | bb]
                                v_a = ta_use[(ba << 1) | bb]
                                for bo in (0, 1):
                                    v_b = tb_use[(bx << 1) | bo if x_pos == 0 else (bo << 1) | bx]
                                    reachable.add((v_a, v_b) if first_is_1 else (v_b, v_a))
                        if len(reachable) == 3:
                            excl = next((b1, b2) for b1 in (0, 1) for b2 in (0, 1) if (b1, b2) not in reachable)
                            c1_eff = c1_v if excl[0] == 1 else -c1_v
                            c2_eff = c2_v if excl[1] == 1 else -c2_v
                            out_at_00 = t_out[((1 - excl[0]) << 1) | (1 - excl[1])]
                            cout_eff = cout_v if out_at_00 == 0 else -cout_v
                            fa_in = sorted(set(pa) | (set(pb) - {x_wire}))
                            ig, il = logger.derive_disjoint_or_z_eq(c1_eff, c2_eff, cout_eff, fa_in)

                            row = defaultdict(int)
                            rhs = 0
                            for v_x, eff_l, sgn in ((c1_v, c1_eff, 1), (c2_v, c2_eff, 1), (cout_v, cout_eff, -1)):
                                if eff_l > 0:
                                    row[v_x] += sgn
                                else:
                                    row[v_x] -= sgn
                                    rhs -= sgn
                            row[0] = rhs
                            base_z_eqs.append((dict(row), ig, il))
                            found_dc = True
                            break
                if found_dc:
                    break

    eq_bank: list[tuple[int, int]] = [(ig, il) for _, ig, il in base_z_eqs]
    unit_bank_idx: dict[int, int] = {}
    equiv_bank_idx: dict[int, int] = {}

    def get_unit_eq_idx(v: int) -> int:
        if v not in unit_bank_idx:
            _, ig, il = unit_eq_ids[v]
            unit_bank_idx[v] = len(eq_bank)
            eq_bank.append((ig, il))
        return unit_bank_idx[v]

    def get_equiv_eq_idx(u_hi: int) -> int:
        if u_hi not in equiv_bank_idx:
            _, _, ig, il = equiv_eq_ids[u_hi]
            equiv_bank_idx[u_hi] = len(eq_bank)
            eq_bank.append((ig, il))
        return equiv_bank_idx[u_hi]

    def emit_int_combination(comb_dict: dict[int, Fraction], scale_int: int, side: str = "ge") -> int:
        rpn: list[int | str] = []
        first = True
        for e_id, frac_c in sorted(comb_dict.items()):
            mult = int(frac_c * scale_int)
            if mult == 0:
                continue
            ig, il = eq_bank[e_id]
            use_id = (ig if mult > 0 else il) if side == "ge" else (il if mult > 0 else ig)
            absm = abs(mult)
            if absm == 1:
                rpn.append(use_id)
            else:
                rpn.extend([use_id, absm, "*"])
            if not first:
                rpn.append("+")
            first = False
        return logger.emit_pol(rpn)

    zeq_occ: dict[int, int] = defaultdict(int)
    for r_d, _, _ in base_z_eqs:
        for k, val in r_d.items():
            if k != 0 and val != 0:
                zeq_occ[k] += 1

    def col_prio(k: int) -> tuple[int, int]:
        return (1 if zeq_occ[k] >= 2 else 0, k)

    pivots: dict[int, tuple[dict[int, Fraction], dict[int, Fraction]]] = {}

    def insert_row(row_f: dict[int, int] | dict[int, Fraction], comb_f: dict[int, Fraction]) -> int | None:
        row: dict[int, Fraction] = {k: Fraction(v) for k, v in row_f.items() if v != 0 or k == 0}
        row[0] = row.get(0, Fraction(0))
        comb: dict[int, Fraction] = {e: Fraction(c) for e, c in comb_f.items() if c != 0}
        while True:
            cols = [k for k in row.keys() if k != 0 and row[k] != 0]
            if not cols:
                if row[0] != 0:
                    lcm_d = 1
                    for c_val in list(comb.values()) + [row[0]]:
                        lcm_d = math.lcm(lcm_d, c_val.denominator)
                    r_int = int(row[0] * lcm_d)
                    return emit_int_combination(comb, lcm_d, "le" if r_int > 0 else "ge")
                return None
            lead = max(cols, key=col_prio)
            if lead in pivots:
                fac = row[lead]
                prow, pcomb = pivots[lead]
                for k, pv in prow.items():
                    nv = row.get(k, Fraction(0)) - fac * pv
                    if k != 0 and nv == 0:
                        row.pop(k, None)
                    else:
                        row[k] = nv
                for e, pc in pcomb.items():
                    nc = comb.get(e, Fraction(0)) - fac * pc
                    if nc == 0:
                        comb.pop(e, None)
                    else:
                        comb[e] = nc
            else:
                inv_l = Fraction(1) / row[lead]
                nrow = {k: v * inv_l for k, v in row.items() if k == 0 or v * inv_l != 0}
                ncomb = {e: c * inv_l for e, c in comb.items() if c * inv_l != 0}
                for pk in list(pivots.keys()):
                    prow, pcomb = pivots[pk]
                    if lead in prow:
                        f2 = prow[lead]
                        for k, nv2 in nrow.items():
                            val2 = prow.get(k, Fraction(0)) - f2 * nv2
                            if k != 0 and val2 == 0:
                                prow.pop(k, None)
                            else:
                                prow[k] = val2
                        for e, nc2 in ncomb.items():
                            vc2 = pcomb.get(e, Fraction(0)) - f2 * nc2
                            if vc2 == 0:
                                pcomb.pop(e, None)
                            else:
                                pcomb[e] = vc2
                pivots[lead] = (nrow, ncomb)
                return None

    for idx_e, (r_d, _, _) in enumerate(base_z_eqs):
        cid_contra = insert_row(r_d, {idx_e: Fraction(1)})
        if cid_contra is not None:
            pbp_path.write_text(logger.finish_unsat(cid_contra), encoding="utf-8")
            return len(logger.lines)

    touched_vars = set(fixed.keys()) | set(equiv.keys())
    for _peel_iter in range(1, 80):
        if touched_vars:
            affected = [
                ld for ld, (prow, _) in list(pivots.items())
                if ld in touched_vars or any(k in touched_vars for k in prow if k != 0)
            ]
            reinsert = []
            for ld in affected:
                prow, pcomb = pivots.pop(ld)
                cur_row: dict[int, Fraction] = defaultdict(Fraction, prow)
                cur_comb: dict[int, Fraction] = defaultdict(Fraction, pcomb)
                changed_v = True
                while changed_v:
                    changed_v = False
                    for k in [col for col in list(cur_row.keys()) if col != 0 and cur_row[col] != 0]:
                        coeff = cur_row[k]
                        if k in equiv:
                            lo, fl = equiv[k]
                            e_idx = get_equiv_eq_idx(k)
                            cur_row.pop(k)
                            if fl == 0:
                                cur_row[lo] += coeff
                                cur_comb[e_idx] -= coeff
                            else:
                                cur_row[lo] -= coeff
                                cur_row[0] -= coeff
                                cur_comb[e_idx] -= coeff
                            changed_v = True
                        elif k in fixed:
                            val = fixed[k]
                            u_idx = get_unit_eq_idx(k)
                            cur_row.pop(k)
                            cur_row[0] -= coeff * val
                            cur_comb[u_idx] -= coeff
                            changed_v = True
                reinsert.append((cur_row, cur_comb))
            touched_vars.clear()
            for r_d, c_d in reinsert:
                cid_contra = insert_row(r_d, c_d)
                if cid_contra is not None:
                    pbp_path.write_text(logger.finish_unsat(cid_contra), encoding="utf-8")
                    return len(logger.lines)

        prev_f, prev_e = set(fixed.keys()), set(equiv.keys())
        found_new = False

        for prow, pcomb in list(pivots.values()):
            cols = [k for k in prow.keys() if k != 0 and prow[k] != 0]
            if not cols or len(cols) > 80:
                continue
            lcm_d = 1
            for val in list(prow.values()) + list(pcomb.values()):
                lcm_d = math.lcm(lcm_d, val.denominator)
            i_coeffs = {k: int(prow[k] * lcm_d) for k in cols}
            i_rhs = int(prow[0] * lcm_d)

            g_all = 0
            for cv in i_coeffs.values():
                g_all = math.gcd(g_all, abs(cv))

            if g_all > 1 and (i_rhs % g_all != 0):
                id_raw_ge = emit_int_combination(pcomb, lcm_d, "ge")
                id_raw_le = emit_int_combination(pcomb, lcm_d, "le")
                id_div_ge = logger.emit_pol([id_raw_ge, g_all, "d"])
                id_div_le = logger.emit_pol([id_raw_le, g_all, "d"])
                cid_contra = logger.emit_pol([id_div_ge, id_div_le, "+"])
                pbp_path.write_text(logger.finish_unsat(cid_contra), encoding="utf-8")
                return len(logger.lines)

            row_id_ge: int | None = None
            row_id_le: int | None = None

            def ensure_row_ids() -> tuple[int, int]:
                nonlocal row_id_ge, row_id_le
                if row_id_ge is None or row_id_le is None:
                    rg = emit_int_combination(pcomb, lcm_d, "ge")
                    rl = emit_int_combination(pcomb, lcm_d, "le")
                    if g_all > 1:
                        rg = logger.emit_pol([rg, g_all, "d"])
                        rl = logger.emit_pol([rl, g_all, "d"])
                    row_id_ge, row_id_le = rg, rl
                return row_id_ge, row_id_le

            if g_all > 1:
                for k in cols:
                    i_coeffs[k] //= g_all
                i_rhs //= g_all

            min_s = sum(c for c in i_coeffs.values() if c < 0)
            max_s = sum(c for c in i_coeffs.values() if c > 0)
            if i_rhs < min_s or i_rhs > max_s:
                rg, rl = ensure_row_ids()
                if i_rhs > max_s:
                    rpn: list[int | str] = [rg]
                    for k, c in i_coeffs.items():
                        rpn.extend([f"~x{k}", c, "*", "+"] if c > 0 else [f"x{k}", -c, "*", "+"])
                    cid_c = logger.emit_pol(rpn)
                else:
                    rpn = [rl]
                    for k, c in i_coeffs.items():
                        rpn.extend([f"~x{k}", -c, "*", "+"] if c < 0 else [f"x{k}", c, "*", "+"])
                    cid_c = logger.emit_pol(rpn)
                pbp_path.write_text(logger.finish_unsat(cid_c), encoding="utf-8")
                return len(logger.lines)

            odd_vars = [k for k, c in i_coeffs.items() if (c & 1) == 1]
            rhs_mod2 = i_rhs & 1

            if len(odd_vars) == 0 and rhs_mod2 == 1:
                rg, rl = ensure_row_ids()
                d_ge = logger.emit_pol([rg, 2, "d"])
                d_le = logger.emit_pol([rl, 2, "d"])
                cid_c = logger.emit_pol([d_ge, d_le, "+"])
                pbp_path.write_text(logger.finish_unsat(cid_c), encoding="utf-8")
                return len(logger.lines)

            elif len(odd_vars) == 1:
                v0 = odd_vars[0]
                if v0 not in fixed:
                    rg, rl = ensure_row_ids()
                    lit_tok = f"x{v0}" if rhs_mod2 == 1 else f"~x{v0}"
                    p_a = logger.emit_pol([rg, lit_tok, "+", 2, "d"])
                    p_b = logger.emit_pol([rl, lit_tok, "+", 2, "d"])
                    id_u = logger.emit_pol([p_a, p_b, "+"])
                    record_unit(v0, rhs_mod2, id_u)
                    found_new = True

            elif len(odd_vars) == 2:
                v1, v2 = sorted(odd_vars)
                if v2 not in fixed and v2 not in equiv:
                    rg, rl = ensure_row_ids()
                    if rhs_mod2 == 1:
                        pa1 = logger.emit_pol([rg, f"x{v1}", "+", f"x{v2}", "+", 2, "d"])
                        pb1 = logger.emit_pol([rl, f"x{v1}", "+", f"x{v2}", "+", 2, "d"])
                        id_pos = logger.emit_pol([pa1, pb1, "+"])

                        pa2 = logger.emit_pol([rg, f"~x{v1}", "+", f"~x{v2}", "+", 2, "d"])
                        pb2 = logger.emit_pol([rl, f"~x{v1}", "+", f"~x{v2}", "+", 2, "d"])
                        id_neg = logger.emit_pol([pa2, pb2, "+"])
                        record_equiv(v2, v1, 1, (id_pos, id_neg))
                    else:
                        pa1 = logger.emit_pol([rg, f"~x{v1}", "+", f"x{v2}", "+", 2, "d"])
                        pb1 = logger.emit_pol([rl, f"~x{v1}", "+", f"x{v2}", "+", 2, "d"])
                        id_ge21 = logger.emit_pol([pa1, pb1, "+"])

                        pa2 = logger.emit_pol([rg, f"x{v1}", "+", f"~x{v2}", "+", 2, "d"])
                        pb2 = logger.emit_pol([rl, f"x{v1}", "+", f"~x{v2}", "+", 2, "d"])
                        id_le21 = logger.emit_pol([pa2, pb2, "+"])
                        record_equiv(v2, v1, 0, (id_ge21, id_le21))
                    found_new = True

        st, work, cid_u = bcp_and_log(work)
        if st == "UNSAT":
            assert cid_u is not None
            pbp_path.write_text(logger.finish_unsat(cid_u), encoding="utf-8")
            return len(logger.lines)

        touched_vars.update(set(fixed.keys()) - prev_f)
        touched_vars.update(set(equiv.keys()) - prev_e)
        if not found_new and not touched_vars:
            break

    raise RuntimeError("Adder telescoping did not reach a contradiction")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit and verify VeriPB 3.0 certificates for scrambled Schoolbook-vs-Wallace multiplier miters."
    )
    parser.add_argument("--bits", nargs="+", type=int, default=[6, 8, 10, 12, 16])
    parser.add_argument("--out-dir", type=Path, default=Path("results/veripb_proofs"))
    parser.add_argument("--json-out", type=Path, default=Path("results/veripb_results.json"))
    parser.add_argument("--veripb-bin", type=str, default=shutil.which("veripb") or "")
    args = parser.parse_args(argv)

    if not args.veripb_bin or not Path(args.veripb_bin).exists():
        raise FileNotFoundError("veripb binary not found on PATH; pass --veripb-bin or add veripb to PATH.")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    print("=" * 106)
    print("VeriPB 3.0.2 Certification on Scrambled 3-CNF Multiplier Miters (Schoolbook vs Wallace)")
    print("=" * 106)

    rows = []
    for kb in args.bits:
        nv0, cl0 = gen_schoolbook_vs_wallace_miter_3cnf(kb, unsat=True, seed=100 + kb)
        snv, scl = scramble_cnf(nv0, cl0, seed=200 + kb)
        cnf_file = args.out_dir / f"scrambled_miter_{kb}x{kb}.cnf"
        pbp_file = args.out_dir / f"scrambled_miter_{kb}x{kb}.pbp"

        t0 = time.perf_counter()
        n_lines = certify_adder_telescoping_veripb(snv, scl, cnf_file, pbp_file)
        solve_ms = round((time.perf_counter() - t0) * 1000.0, 2)

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
            raise AssertionError(f"VeriPB failed on {kb}x{kb}:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")

        print(
            f"  Scrambled_Miter_{kb:02d}x{kb:02d} (vars={snv:4d}, m={len(scl):5d}) | "
            f"pbp_lines={n_lines:5d} | emit={solve_ms:8.1f}ms | veripb={check_ms:6.1f}ms | s VERIFIED UNSATISFIABLE"
        )
        rows.append(
            {
                "instance": f"Scrambled_Schoolbook_vs_Wallace_{kb}x{kb}",
                "k_bits": kb,
                "vars": snv,
                "clauses": len(scl),
                "pbp_lines": n_lines,
                "emit_ms": solve_ms,
                "veripb_check_ms": check_ms,
                "veripb_status": "s VERIFIED UNSATISFIABLE",
                "cnf_path": str(cnf_file),
                "pbp_path": str(pbp_file),
            }
        )

    args.json_out.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
    print(f"\nVerified {len(rows)}/{len(rows)} proofs -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
