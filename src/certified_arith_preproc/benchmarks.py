"""Synthetic benchmark generators for arithmetic miters, hybrid interpolants, and algebraic CNF families."""

from __future__ import annotations

import itertools
import numpy as np
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from .cnf_utils import fast_unroll_11_chains


def gen_php(pigeons: int, holes: int) -> tuple[int, list[list[int]]]:
    cls: list[list[int]] = []
    vid = lambda i, j: i * holes + j + 1
    top = pigeons * holes
    for i in range(pigeons):
        lits = [vid(i, j) for j in range(holes)]
        while len(lits) > 3:
            top += 1
            cls.append([lits[0], lits[1], top])
            lits = [-top] + lits[2:]
        cls.append(lits)
    for j in range(holes):
        for i1 in range(pigeons):
            for i2 in range(i1 + 1, pigeons):
                cls.append([-vid(i1, j), -vid(i2, j)])
    return top, cls


def gen_schoolbook_vs_wallace_miter_3cnf(
    k_bits: int = 10,
    unsat: bool = True,
    seed: int = 42,
) -> tuple[int, list[list[int]]]:
    """Generate a 3-CNF OR-miter comparing a ripple/schoolbook multiplier against a shuffled Wallace tree."""
    rng = np.random.default_rng(seed)
    pool = IDPool()
    clauses: list[list[int]] = []
    a_in = [pool.id(f"a_{i}") for i in range(k_bits)]
    b_in = [pool.id(f"b_{i}") for i in range(k_bits)]

    def new_and(u: int, v: int) -> int:
        z = pool.id(f"and_{pool.top + 1}")
        clauses.extend([[-z, u], [-z, v], [z, -u, -v]])
        return z

    def new_xor(u: int, v: int) -> int:
        z = pool.id(f"xor_{pool.top + 1}")
        clauses.extend([[-u, -v, -z], [u, v, -z], [-u, v, z], [u, -v, z]])
        return z

    def new_or(u: int, v: int) -> int:
        z = pool.id(f"or_{pool.top + 1}")
        clauses.extend([[z, -u], [z, -v], [-z, u, v]])
        return z

    def half_adder(u: int, v: int) -> tuple[int, int]:
        return new_xor(u, v), new_and(u, v)

    def full_adder(u: int, v: int, w: int) -> tuple[int, int]:
        t, c1 = half_adder(u, v)
        s, c2 = half_adder(t, w)
        return s, new_or(c1, c2)

    def ripple_add(vec1: list[int], vec2: list[int]) -> list[int]:
        n_m = max(len(vec1), len(vec2))
        res: list[int] = []
        carry: int | None = None
        for idx in range(n_m):
            x = vec1[idx] if idx < len(vec1) else None
            y = vec2[idx] if idx < len(vec2) else None
            if x is not None and y is not None:
                s, carry = half_adder(x, y) if carry is None else full_adder(x, y, carry)
            else:
                v = x if x is not None else y
                assert v is not None
                if carry is None:
                    s = v
                else:
                    s, carry = half_adder(v, carry)
            res.append(s)
        if carry is not None:
            res.append(carry)
        return res

    acc_a = [new_and(a_in[0], b_in[j]) for j in range(k_bits)]
    out_a: list[int] = []
    for i in range(1, k_bits):
        out_a.append(acc_a[0])
        acc_a = ripple_add(acc_a[1:], [new_and(a_in[i], b_in[j]) for j in range(k_bits)])
    out_a = (out_a + acc_a)[: 2 * k_bits]

    cols: list[list[int]] = [[] for _ in range(2 * k_bits + 2)]
    order_ij = [(i, j) for i in range(k_bits) for j in range(k_bits)]
    rng.shuffle(order_ij)
    for i, j in order_ij:
        cols[i + j].append(new_and(a_in[i], b_in[j]))
    out_b: list[int] = []
    for col_idx in range(2 * k_bits):
        bkt = cols[col_idx]
        while len(bkt) >= 3:
            s, c = full_adder(bkt[0], bkt[1], bkt[2])
            bkt = bkt[3:] + [s]
            cols[col_idx + 1].append(c)
        if len(bkt) == 2:
            s, c = half_adder(bkt[0], bkt[1])
            bkt = [s]
            cols[col_idx + 1].append(c)
        out_b.append(bkt[0])

    diff_wires = [new_xor(out_a[t], out_b[t]) for t in range(2 * k_bits)]
    if not unsat:
        diff_wires[-2] = -diff_wires[-2]
    cur = diff_wires
    while len(cur) > 3:
        aux = pool.id(f"miter_{pool.top + 1}")
        clauses.append([cur[0], cur[1], aux])
        cur = [-aux] + cur[2:]
    clauses.append(cur)
    return pool.top, clauses


def gen_prime_mult_miter_3cnf(N_val: int, k_bits: int) -> tuple[int, list[list[int]]]:
    """Schoolbook multiplier constraint p * q == N_val (with p, q > 1) encoded in 3-CNF."""
    pool = IDPool()
    clauses: list[list[int]] = []
    p = [pool.id(f"p_{i}") for i in range(k_bits)]
    q = [pool.id(f"q_{i}") for i in range(k_bits)]

    def add_alo(lits: list[int]) -> None:
        cur = list(lits)
        while len(cur) > 3:
            aux = pool.id(f"alo_{pool.top + 1}")
            clauses.append([cur[0], cur[1], aux])
            cur = [-aux] + cur[2:]
        clauses.append(cur)

    add_alo(p[1:])
    add_alo(q[1:])

    def new_and(a: int, b: int) -> int:
        z = pool.id(f"a_{pool.top + 1}")
        clauses.extend([[-z, a], [-z, b], [z, -a, -b]])
        return z

    def new_xor(a: int, b: int) -> int:
        z = pool.id(f"x_{pool.top + 1}")
        clauses.extend([[-a, -b, -z], [a, b, -z], [-a, b, z], [a, -b, z]])
        return z

    def new_or(a: int, b: int) -> int:
        z = pool.id(f"o_{pool.top + 1}")
        clauses.extend([[z, -a], [z, -b], [-z, a, b]])
        return z

    cols: list[list[int]] = [[] for _ in range(2 * k_bits + 2)]
    for i in range(k_bits):
        for j in range(k_bits):
            cols[i + j].append(new_and(p[i], q[j]))

    out_bits: list[int] = []
    for col_idx in range(2 * k_bits):
        bucket = cols[col_idx]
        while len(bucket) >= 3:
            a, b, c = bucket[0], bucket[1], bucket[2]
            t = new_xor(a, b)
            s_bit = new_xor(t, c)
            carry = new_or(new_and(a, b), new_and(t, c))
            bucket = bucket[3:] + [s_bit]
            cols[col_idx + 1].append(carry)
        if len(bucket) == 2:
            a, b = bucket[0], bucket[1]
            bucket = [new_xor(a, b)]
            cols[col_idx + 1].append(new_and(a, b))
        if len(bucket) == 1:
            out_bits.append(bucket[0])
        else:
            z0 = pool.id(f"z_{col_idx}")
            clauses.append([-z0])
            out_bits.append(z0)

    for b_idx, var_b in enumerate(out_bits):
        clauses.append([var_b if ((N_val >> b_idx) & 1) else -var_b])
    for rem in cols[2 * k_bits]:
        clauses.append([-rem])
    return pool.top, clauses


def gen_wire_eliminated_php_tseitin(
    pigeons: int = 13,
    holes: int = 12,
    tseitin_verts: int = 28,
) -> tuple[int, list[list[int]]]:
    """Generate wire-eliminated disjunctive interpolant OR_{s1^s2}(PHP_{p}^{h}, Tseitin_{V, odd})."""
    n1, c1 = gen_php(pigeons, holes)
    edges = []
    inc: list[list[int]] = [[] for _ in range(tseitin_verts)]
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

    c2: list[list[int]] = []
    for v_idx in range(tseitin_verts):
        e1, e2, e3 = inc[v_idx]
        ch = 1 if v_idx == 0 else 0
        for b1, b2, b3 in itertools.product((0, 1), repeat=3):
            if (b1 ^ b2 ^ b3) != ch:
                c2.append([-e1 if b1 else e1, -e2 if b2 else e2, -e3 if b3 else e3])

    n2 = len(edges)
    s1, s2 = n1 + n2 + 1, n1 + n2 + 2
    top = s2
    cls: list[list[int]] = []
    for b1, b2 in itertools.product((0, 1), repeat=2):
        gd = [-s1 if b1 else s1, -s2 if b2 else s2]
        target = c1 if (b1 ^ b2) == 0 else [[(x + n1 if x > 0 else x - n1) for x in c] for c in c2]
        for c in target:
            lits = gd + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls


def gen_deep_keccak_chi_sponge_php(
    pigeons: int = 6,
    holes: int = 5,
    n_layers: int = 4,
) -> tuple[int, list[list[int]]]:
    """PHP lifted over iterated Keccak-chi rounds with a top-level wire-eliminated MAJ_3 sponge."""
    _, c_orig = gen_php(pigeons, holes)
    n_ring = 13
    cur_layer = list(range(1, n_ring + 1))
    top = n_ring
    cls: list[list[int]] = []

    for _ in range(n_layers):
        nxt_layer = []
        for i in range(n_ring):
            v0 = cur_layer[i]
            v1 = cur_layer[(i + 1) % n_ring]
            v2 = cur_layer[(i + 2) % n_ring]
            top += 1
            and_w = top
            cls.extend([[-and_w, -v1], [-and_w, v2], [and_w, v1, -v2]])
            top += 1
            h_out = top
            cls.extend([[-v0, -and_w, -h_out], [v0, and_w, -h_out], [-v0, and_w, h_out], [v0, -and_w, h_out]])
            nxt_layer.append(h_out)
        cur_layer = nxt_layer

    for cl in c_orig:
        h_inv_idx = sorted({((abs(l) - 1 + off) % n_ring) for l in cl for off in (0, 1, 2, 3)})
        h_vars = [cur_layer[idx] for idx in h_inv_idx]
        for bits in itertools.product((0, 1), repeat=len(h_vars)):
            hmap = dict(zip(h_inv_idx, bits))
            sat_c = False
            for l in cl:
                v_idx = abs(l) - 1
                a = hmap[v_idx % n_ring]
                b = hmap[(v_idx + 1) % n_ring]
                c = hmap[(v_idx + 2) % n_ring]
                d = hmap[(v_idx + 3) % n_ring]
                xv = (1 if (a + b + c) >= 2 else 0) ^ d
                if (l > 0 and xv == 1) or (l < 0 and xv == 0):
                    sat_c = True
                    break
            if not sat_c:
                lits = [-hv if b == 1 else hv for hv, b in zip(h_vars, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def gen_shifted_cubic_sponge_miter(unsat: bool = True) -> tuple[int, list[list[int]]]:
    """Shifted cubic sponge miter over a 13-bit ring with no shared intermediate ray polynomials."""
    n_ring = 13
    u_wires = [n_ring + i for i in range(1, 6)]
    v_wires = [n_ring + 5 + i for i in range(1, 6)]
    top = n_ring + 10
    cls: list[list[int]] = []

    def f_val(vmap: dict[int, int], idx: int) -> int:
        a = vmap[(idx % n_ring) + 1]
        b = vmap[((idx + 1) % n_ring) + 1]
        c = vmap[((idx + 2) % n_ring) + 1]
        d = vmap[((idx + 3) % n_ring) + 1]
        return (a & b & c) ^ d

    def add_pair(idx1: int, idx2: int, wire_xors: list[int], rhs: int) -> None:
        nonlocal top
        z_vars = sorted({((idx + o) % n_ring) + 1 for idx in (idx1, idx2) for o in range(4)})
        all_v = z_vars + list(wire_xors)
        for bits in itertools.product((0, 1), repeat=len(all_v)):
            vmap = dict(zip(all_v, bits))
            val = f_val(vmap, idx1) ^ f_val(vmap, idx2)
            for w in wire_xors:
                val ^= vmap[w]
            if val != rhs:
                lits = [-v if b == 1 else v for v, b in zip(all_v, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)

    add_pair(0, 1, [u_wires[0]], 0)
    add_pair(2, 3, [u_wires[0], u_wires[1]], 0)
    add_pair(4, 5, [u_wires[1], u_wires[2]], 0)
    add_pair(6, 7, [u_wires[2], u_wires[3]], 0)
    add_pair(8, 9, [u_wires[3], u_wires[4]], 0)
    add_pair(10, 11, [u_wires[4]], 0)

    add_pair(1, 2, [v_wires[0]], 0)
    add_pair(3, 4, [v_wires[0], v_wires[1]], 0)
    add_pair(5, 6, [v_wires[1], v_wires[2]], 0)
    add_pair(7, 8, [v_wires[2], v_wires[3]], 0)
    add_pair(9, 10, [v_wires[3], v_wires[4]], 0)
    add_pair(11, 0, [v_wires[4]], 1 if unsat else 0)
    return top, cls


def gen_goldreich_prg_3cnf(
    n_seed: int = 20,
    m_out: int = 25,
    mode: str = "XOR_MAJ3",
    planted_sat: bool = False,
    seed: int = 2026,
) -> tuple[int, list[list[int]], dict[int, int] | None]:
    """Generate a 5-local Goldreich PRG instance (TSA or XOR-MAJ3) expanded directly to 3-CNF."""
    rng = np.random.default_rng(seed)
    while True:
        z_star = {v: int(rng.integers(0, 2)) for v in range(1, n_seed + 1)} if planted_sat else None
        tuples = []
        rhs = []
        for _ in range(m_out):
            five = [int(x) for x in rng.choice(np.arange(1, n_seed + 1), size=5, replace=False)]
            tuples.append(five)
            if planted_sat and z_star is not None:
                a, b, c, d, e = five
                if mode == "TSA":
                    yi = z_star[a] ^ z_star[b] ^ z_star[c] ^ (z_star[d] & z_star[e])
                else:
                    maj = (z_star[c] & z_star[d]) ^ (z_star[c] & z_star[e]) ^ (z_star[d] & z_star[e])
                    yi = z_star[a] ^ z_star[b] ^ maj
                rhs.append(int(yi))
            else:
                rhs.append(int(rng.integers(0, 2)))

        top = n_seed
        cls: list[list[int]] = []
        for (a, b, c, d, e), yi in zip(tuples, rhs):
            vs = (a, b, c, d, e)
            for bits in itertools.product((0, 1), repeat=5):
                if mode == "TSA":
                    val = bits[0] ^ bits[1] ^ bits[2] ^ (bits[3] & bits[4])
                else:
                    maj = (bits[2] & bits[3]) ^ (bits[2] & bits[4]) ^ (bits[3] & bits[4])
                    val = bits[0] ^ bits[1] ^ maj
                if val != yi:
                    lits = [-v if bit else v for v, bit in sorted(zip(vs, bits))]
                    while len(lits) > 3:
                        top += 1
                        cls.append([lits[0], lits[1], top])
                        lits = [-top] + lits[2:]
                    cls.append(lits)

        is_sat = Cadical195(bootstrap_with=cls).solve()
        if planted_sat and is_sat:
            return top, cls, z_star
        if (not planted_sat) and (not is_sat):
            return top, cls, None


def gen_hybrid_php_goldreich_interpolant(unsat: bool = True, seed: int = 2026) -> tuple[int, list[list[int]]]:
    """Wire-eliminated interpolant OR_{s1^s2}(PHP, Goldreich XOR-MAJ3)."""
    n1, c1 = gen_php(4 if unsat else 3, 3)
    _, c2_raw, _ = gen_goldreich_prg_3cnf(16, 22, mode="XOR_MAJ3", planted_sat=False, seed=seed)
    c2 = fast_unroll_11_chains(c2_raw)
    n2 = 16
    s1, s2 = n1 + n2 + 1, n1 + n2 + 2
    top = s2
    cls: list[list[int]] = []

    for b1, b2 in itertools.product((0, 1), repeat=2):
        guard_disj = [-s1 if b1 else s1, -s2 if b2 else s2]
        target = c1 if (b1 ^ b2) == 0 else [[(x + n1 if x > 0 else x - n1) for x in c] for c in c2]
        for c in target:
            lits = guard_disj + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls
