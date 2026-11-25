"""CNF utilities: DIMACS I/O, scrambling, (1,1)-chain unrolling, BCP/2-XOR propagation, and GF(2) helpers."""

from __future__ import annotations

import itertools
from collections import defaultdict
from pathlib import Path
import numpy as np

VAR_TT_CACHE: dict[int, list[int]] = {
    k: [sum((1 << idx) for idx in range(1 << k) if (idx >> (k - 1 - j)) & 1) for j in range(k)]
    for k in range(1, 13)
}


def write_dimacs(path: str | Path, n_vars: int, clauses: list[list[int]]) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        f.write(f"p cnf {n_vars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(x) for x in c) + " 0\n")


def read_dimacs(path: str | Path) -> tuple[int, list[list[int]]]:
    n_vars = 0
    clauses: list[list[int]] = []
    with Path(path).open("r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("c"):
                continue
            if s.startswith("p"):
                parts = s.split()
                if len(parts) >= 3:
                    n_vars = int(parts[2])
                continue
            lits = [int(tok) for tok in s.split() if tok != "0"]
            if lits:
                clauses.append(lits)
                for l in lits:
                    if abs(l) > n_vars:
                        n_vars = abs(l)
    return n_vars, clauses


def scramble_cnf(n_vars: int, clauses: list[list[int]], seed: int = 2026) -> tuple[int, list[list[int]]]:
    """Randomly permute variable IDs, literal polarities, literal order, and clause order."""
    rng = np.random.default_rng(seed)
    perm = rng.permutation(np.arange(1, n_vars + 1))
    signs = rng.choice([-1, 1], size=n_vars + 1)
    out: list[list[int]] = []
    for c in clauses:
        sc = []
        for lit in c:
            v = abs(lit)
            nv = int(perm[v - 1])
            sg = int(signs[v]) * (1 if lit > 0 else -1)
            sc.append(nv if sg > 0 else -nv)
        rng.shuffle(sc)
        out.append(sc)
    rng.shuffle(out)
    return n_vars, out


def compact_active_cnf(clauses: list[list[int]]) -> tuple[int, list[list[int]]]:
    """Relabel active variable IDs densely to 1..n_active."""
    active_vars = sorted({abs(lit) for c in clauses for lit in c})
    if not active_vars:
        return 0, []
    vmap = {old_v: new_v for new_v, old_v in enumerate(active_vars, start=1)}
    compacted = [[vmap[lit] if lit > 0 else -vmap[-lit] for lit in c] for c in clauses]
    return len(active_vars), compacted


def fast_unroll_11_chains(clauses: list[list[int]]) -> list[list[int]]:
    """Batch O(m log m) elimination of Tseitin splitting variables with occurrence count (1, 1)."""
    work = [sorted(set(c), key=lambda z: (abs(z), z)) for c in clauses]
    work = [c for c in work if not any(-x in c for x in c)]

    while True:
        pos: dict[int, list[int]] = defaultdict(list)
        neg: dict[int, list[int]] = defaultdict(list)
        for idx, c in enumerate(work):
            for lit in c:
                if lit > 0:
                    pos[lit].append(idx)
                else:
                    neg[-lit].append(idx)

        used_clauses: set[int] = set()
        merges: list[tuple[int, int, int]] = []
        for v, p_idxs in pos.items():
            if len(p_idxs) == 1:
                n_idxs = neg.get(v, ())
                if len(n_idxs) == 1:
                    pi, ni = p_idxs[0], n_idxs[0]
                    if pi != ni and pi not in used_clauses and ni not in used_clauses:
                        used_clauses.add(pi)
                        used_clauses.add(ni)
                        merges.append((v, pi, ni))

        if not merges:
            break

        nxt = [c for idx, c in enumerate(work) if idx not in used_clauses]
        for v, pi, ni in merges:
            cp = [x for x in work[pi] if x != v]
            cn = [x for x in work[ni] if x != -v]
            mset = set(cp) | set(cn)
            if not any(-x in mset for x in mset):
                nxt.append(sorted(mset, key=lambda z: (abs(z), z)))

        dedup: list[list[int]] = []
        seen: set[tuple[int, ...]] = set()
        for c in nxt:
            tc = tuple(c)
            if tc not in seen:
                seen.add(tc)
                dedup.append(c)
        work = dedup
    return work


def apply_fixed_and_equivs_to_clauses(
    clauses: list[list[int]],
    fixed: dict[int, int],
    equiv: dict[int, tuple[int, int]],
) -> tuple[str, list[list[int]]]:
    """Apply unit assignments and 2-XOR equivalences x_u == x_rep ^ flip to clauses."""
    def resolve_var(v: int) -> tuple[int, int]:
        flip = 0
        while v in equiv:
            v, f = equiv[v]
            flip ^= f
        return v, flip

    out: list[list[int]] = []
    seen: set[tuple[int, ...]] = set()
    for cl in clauses:
        new_cl: list[int] = []
        sat = False
        for lit in cl:
            v0 = abs(lit)
            pol = 1 if lit > 0 else 0
            rv, fl = resolve_var(v0)
            req_val = pol ^ fl
            if rv in fixed:
                if fixed[rv] == req_val:
                    sat = True
                    break
                continue
            nlit = rv if req_val == 1 else -rv
            if -nlit in new_cl:
                sat = True
                break
            if nlit not in new_cl:
                new_cl.append(nlit)
        if sat:
            continue
        if len(new_cl) == 0:
            return "UNSAT", []
        new_cl.sort(key=lambda z: (abs(z), z))
        tcl = tuple(new_cl)
        if tcl not in seen:
            seen.add(tcl)
            out.append(new_cl)
    return "OK", out


def propagate_bcp_2clause_and_2xor(
    work_cls: list[list[int]],
    fixed: dict[int, int],
    equiv: dict[int, tuple[int, int]],
) -> tuple[str, list[list[int]]]:
    """Monotone exact propagation of units, binary unit resolutions, and 2-XOR equivalences."""
    while True:
        st, work_cls = apply_fixed_and_equivs_to_clauses(work_cls, fixed, equiv)
        if st == "UNSAT":
            return "UNSAT", []
        chg = False
        cl_set = {tuple(sorted(c, key=lambda z: (abs(z), z))) for c in work_cls}
        for c in work_cls:
            if len(c) == 1:
                v = abs(c[0])
                val = 1 if c[0] > 0 else 0
                if v in fixed and fixed[v] != val:
                    return "UNSAT", []
                if v not in fixed:
                    fixed[v] = val
                    chg = True
            elif len(c) == 2 and abs(c[0]) != abs(c[1]):
                a, b = c[0], c[1]
                if tuple(sorted((-a, b), key=lambda z: (abs(z), z))) in cl_set:
                    vb, valb = abs(b), (1 if b > 0 else 0)
                    if vb in fixed and fixed[vb] != valb:
                        return "UNSAT", []
                    if vb not in fixed:
                        fixed[vb] = valb
                        chg = True
                if tuple(sorted((a, -b), key=lambda z: (abs(z), z))) in cl_set:
                    va, vala = abs(a), (1 if a > 0 else 0)
                    if va in fixed and fixed[va] != vala:
                        return "UNSAT", []
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
        if not chg:
            return "OK", work_cls


def simplify_and_bve(
    n_vars: int,
    clauses: list[list[int]],
    fixed: dict[int, int],
) -> tuple[str, dict[int, int], list[list[int]]]:
    """Full-formula equisatisfiable preprocessing: BCP + pure literals + non-increasing (<=2, <=2) BVE."""
    work = [list(c) for c in clauses]
    fixed = dict(fixed)

    while True:
        changed = False
        while True:
            bcp_step = False
            nxt = []
            seen_cl = set()
            for c in work:
                sat = False
                rem = []
                for lit in c:
                    v = abs(lit)
                    val = fixed.get(v, None)
                    if val is not None:
                        if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                            sat = True
                            break
                    else:
                        if -lit in rem:
                            sat = True
                            break
                        if lit not in rem:
                            rem.append(lit)
                if sat:
                    continue
                if len(rem) == 0:
                    return "UNSAT_BCP", fixed, []
                if len(rem) == 1:
                    uv = abs(rem[0])
                    uval = 1 if rem[0] > 0 else 0
                    if uv in fixed and fixed[uv] != uval:
                        return "UNSAT_BCP", fixed, []
                    if uv not in fixed:
                        fixed[uv] = uval
                        bcp_step = True
                        changed = True
                else:
                    rem.sort(key=lambda z: (abs(z), z))
                    t_rem = tuple(rem)
                    if t_rem not in seen_cl:
                        seen_cl.add(t_rem)
                        nxt.append(rem)
            work = nxt
            if not bcp_step:
                break

        pos_occ: dict[int, list[int]] = defaultdict(list)
        neg_occ: dict[int, list[int]] = defaultdict(list)
        for idx, c in enumerate(work):
            for lit in c:
                if lit > 0:
                    pos_occ[lit].append(idx)
                else:
                    neg_occ[-lit].append(idx)

        all_vars = sorted(set(pos_occ.keys()) | set(neg_occ.keys()))
        pure_fixed = False
        for v in all_vars:
            if v in fixed:
                continue
            p_list = pos_occ.get(v, ())
            n_list = neg_occ.get(v, ())
            if len(p_list) == 0 and len(n_list) > 0:
                fixed[v] = 0
                pure_fixed = True
            elif len(n_list) == 0 and len(p_list) > 0:
                fixed[v] = 1
                pure_fixed = True
        if pure_fixed:
            continue

        used_clauses: set[int] = set()
        batch_to_remove: set[int] = set()
        batch_resolvents: list[list[int]] = []
        for v in all_vars:
            if v in fixed:
                continue
            p_list = pos_occ.get(v, ())
            n_list = neg_occ.get(v, ())
            if 1 <= len(p_list) <= 2 and 1 <= len(n_list) <= 2:
                if any(ci in used_clauses for ci in p_list) or any(ci in used_clauses for ci in n_list):
                    continue
                res_list = []
                ok_res = True
                for pi in p_list:
                    cp = [x for x in work[pi] if x != v]
                    for ni in n_list:
                        cn = [x for x in work[ni] if x != -v]
                        merged = []
                        taut = False
                        for lit in cp + cn:
                            if -lit in merged:
                                taut = True
                                break
                            if lit not in merged:
                                merged.append(lit)
                        if taut:
                            continue
                        if len(merged) > 3:
                            ok_res = False
                            break
                        res_list.append(merged)
                    if not ok_res:
                        break
                if ok_res:
                    used_clauses.update(p_list)
                    used_clauses.update(n_list)
                    batch_to_remove.update(p_list)
                    batch_to_remove.update(n_list)
                    batch_resolvents.extend(res_list)

        if batch_to_remove:
            work = [c for idx, c in enumerate(work) if idx not in batch_to_remove] + batch_resolvents
            changed = True
        if not changed:
            break

    return "OK", fixed, work


def gf2_vec_rref(bitmasks: list[int]) -> list[int]:
    """Reduced row echelon form over GF(2) for integer bitmask vectors."""
    pivots: dict[int, int] = {}
    for m in bitmasks:
        cur = int(m)
        while cur:
            msb = cur.bit_length() - 1
            if msb in pivots:
                cur ^= pivots[msb]
            else:
                for k_lo, v_lo in pivots.items():
                    if (cur >> k_lo) & 1:
                        cur ^= v_lo
                for k in list(pivots.keys()):
                    if (pivots[k] >> msb) & 1:
                        pivots[k] ^= cur
                pivots[msb] = cur
                break
    return [pivots[k] for k in sorted(pivots.keys(), reverse=True)]


def gf2_in_span(vec: int, rref_basis: list[int]) -> bool:
    cur = int(vec)
    for b in rref_basis:
        msb = b.bit_length() - 1
        if (cur >> msb) & 1:
            cur ^= b
    return cur == 0


def truth_mask_on_vars(clause_tuples: tuple[tuple[int, ...], ...], dom_vars: tuple[int, ...]) -> int:
    k = len(dom_vars)
    mask = 0
    for idx, bits in enumerate(itertools.product((0, 1), repeat=k)):
        vmap = dict(zip(dom_vars, bits))
        ok = True
        for cl in clause_tuples:
            if not any((vmap[abs(l)] == 1 if l > 0 else vmap[abs(l)] == 0) for l in cl):
                ok = False
                break
        if ok:
            mask |= (1 << idx)
    return mask


def prime_cnf_of_mask(dom_t: tuple[int, ...], target_sat_mask: int) -> tuple[tuple[int, ...], ...]:
    """Exact prime-implicate CNF minimization on |dom_t| <= 6 via Quine-McCluskey."""
    k = len(dom_t)
    minterms_false = []
    for idx, bits in enumerate(itertools.product((0, 1), repeat=k)):
        if not ((target_sat_mask >> idx) & 1):
            cl = frozenset(-v if b == 1 else v for v, b in zip(dom_t, bits))
            minterms_false.append(cl)
    if not minterms_false:
        return ()

    current = set(minterms_false)
    primes: set[frozenset[int]] = set()
    while current:
        nxt: set[frozenset[int]] = set()
        used: set[frozenset[int]] = set()
        cur_list = list(current)
        for i in range(len(cur_list)):
            c1 = cur_list[i]
            for j in range(i + 1, len(cur_list)):
                c2 = cur_list[j]
                if len(c1) == len(c2):
                    diff = c1 ^ c2
                    if len(diff) == 2:
                        d_list = list(diff)
                        if d_list[0] == -d_list[1]:
                            merged = c1 - {d_list[0], d_list[1]}
                            nxt.add(merged)
                            used.add(c1)
                            used.add(c2)
        for c in cur_list:
            if c not in used:
                primes.add(c)
        current = nxt
    return tuple(sorted(tuple(sorted(p, key=lambda z: (abs(z), z))) for p in primes))
