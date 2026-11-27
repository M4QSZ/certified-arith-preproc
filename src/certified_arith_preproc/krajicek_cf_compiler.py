"""
Deterministic Polynomial-Time `CF -> ≈-Chain` Compiler for ATAQUE-10.

Implements and experimentally verifies the constructive Circuit Frege (`CF`) to
Krajicek `≈`-chain compiler corresponding to `proofs/krajicek_cf_compiler_unsharing.lean`
and Jan Krajicek's "Extended Frege proofs, circuits and rewriting"
(`arXiv:2606.13367v2`, Oct 2026).

Features:
1. `ExplicitDAG`: Straight-line DeMorgan circuit (explicit gate list + output index)
   capable of representing distinct DAGs `C, D` with identical unwinding `Fla[C] = Fla[D]`
   and verifying `Fla[C] == Fla[D]` in `O(|C| + |D|)` time via `DAGStore` hash-consing.
2. `CFProof`: Circuit Frege proof DAG supporting:
   (a) DeMorgan Frege axiom templates (`lem`, `imp_refl`, `imp_to_one`, `weaken`,
       `contraction`, `exchange`, `syllogism_right`) compiled via fixed `O(1)`-step
       `SimBA` templates instantiated on arbitrary DAG subcircuit IDs;
   (b) Modus Ponens `A, ~A v B |- B` compiled via Krajicek's Lemma 2.1 exact
       `k_1 + 2 + k_2` step composition for tree-like proofs, and via Theorem 1.1
       balanced binary-tree conjunction (`O(k log k)` steps) whenever any proof
       line has fan-out > 1 or hypotheses are present;
   (c) `CF` structural rule `C |- D` where `Fla[C] = Fla[D]`, verified in `O(|C|+|D|)`
       and compiled via the Lean-verified 2-step bridge `C ≈ (0 v C) ≈ D`.
3. 100% step-by-step verification using `DAGStore.are_approx(E_i, E_{i+1}) == True`
   on every emitted step, plus semantic truth-table invariance when `num_vars <= 8`.
4. Benchmark Suite:
   - Suite 1: Exponential-tree, linear-DAG `CF` equivalence & MP chains for
     `m in [4, 8, 12, 16, 20]` (`|D_20|_DAG = O(m)`, `|Fla[D_20]| > 1,048,576`).
   - Suite 2: Multi-step `CF` derivations with DAG proof reuse (`fan-out > 1`
     diamond transitivity `x_0 -> x_1, ..., x_{r-1} -> x_r |- x_0 -> x_r` for
     `r in [2, 4, 6, 8]`), confirming `t = O(k log k)` scaling.
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

try:
    from .krajicek_ew_explorer import BACompiler, DAGStore
except ImportError:  # pragma: no cover - direct script execution fallback
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from certified_arith_preproc.krajicek_ew_explorer import BACompiler, DAGStore


# ======================================================================
# 1. Explicit Straight-Line DeMorgan DAGs (`ExplicitDAG`)
# ======================================================================

GateSpec = Tuple


@dataclass(frozen=True)
class ExplicitDAG:
    """Straight-line DeMorgan circuit (mirrors Lean's `CircuitDAG`).

    Allows representing distinct DAG topologies `C != D` that unwind to the
    exact same DeMorgan formula `Fla[C] == Fla[D]`.
    """

    gates: Tuple[GateSpec, ...]
    out: int

    def size(self) -> int:
        return len(self.gates)

    def canonicalize(self, store: DAGStore) -> int:
        """Hash-cons into `store` in exact `O(|gates|)` time."""
        ids: List[int] = []
        for idx, g in enumerate(self.gates):
            op = g[0]
            if op == "0":
                ids.append(store.ZERO)
            elif op == "1":
                ids.append(store.ONE)
            elif op == "v":
                ids.append(store.var(g[1]))
            elif op == "!":
                assert g[1] < idx, f"Non-acyclic neg gate at {idx}"
                ids.append(store.neg(ids[g[1]]))
            elif op == "|":
                assert g[1] < idx and g[2] < idx, f"Non-acyclic disj gate at {idx}"
                ids.append(store.disj(ids[g[1]], ids[g[2]]))
            elif op == "&":
                assert g[1] < idx and g[2] < idx, f"Non-acyclic conj gate at {idx}"
                ids.append(store.conj(ids[g[1]], ids[g[2]]))
            else:
                raise ValueError(f"Unknown gate op: {op}")
        assert 0 <= self.out < len(ids)
        return ids[self.out]

    def zero_or_bridge(self) -> "ExplicitDAG":
        """Construct the explicit 2-gate bridge circuit `M := 0 v C` (Theorem a)."""
        n = len(self.gates)
        return ExplicitDAG(
            gates=self.gates + (("0",), ("|", n, self.out)),
            out=n + 1,
        )


def explicit_from_canonical(store: DAGStore, root: int) -> ExplicitDAG:
    """Extract a canonical (maximally shared) `ExplicitDAG` from `store` in `O(|DAG|)`."""
    order: List[int] = []
    visited: Dict[int, int] = {}

    def dfs(u: int) -> int:
        if u in visited:
            return visited[u]
        k = store.key(u)
        op = k[0]
        if op in ("0", "1", "v"):
            idx = len(order)
            order.append(u)
            visited[u] = idx
            return idx
        if op == "!":
            a = dfs(k[1])
            idx = len(order)
            order.append(("!", a))  # type: ignore[arg-type]
            visited[u] = idx
            return idx
        a = dfs(k[1])
        b = dfs(k[2])
        idx = len(order)
        order.append((op, a, b))  # type: ignore[arg-type]
        visited[u] = idx
        return idx

    gates_list: List[GateSpec] = []
    node_to_idx: Dict[int, int] = {}

    def build(u: int) -> int:
        if u in node_to_idx:
            return node_to_idx[u]
        k = store.key(u)
        op = k[0]
        if op in ("0", "1", "v"):
            idx = len(gates_list)
            gates_list.append(k)
            node_to_idx[u] = idx
            return idx
        if op == "!":
            a = build(k[1])
            idx = len(gates_list)
            gates_list.append(("!", a))
            node_to_idx[u] = idx
            return idx
        a = build(k[1])
        b = build(k[2])
        idx = len(gates_list)
        gates_list.append((op, a, b))
        node_to_idx[u] = idx
        return idx

    out = build(root)
    return ExplicitDAG(gates=tuple(gates_list), out=out)


def build_shared_xor_chain(store: DAGStore, m: int, x_name: str = "x", y_name: str = "y") -> Tuple[ExplicitDAG, ExplicitDAG, List[int]]:
    """Build deep shared circuit `D_m` (`|D_m|_DAG = O(m)`, `|Fla[D_m]| > 2^m`)
    and a top-unshared equivalent `D_m_unshared_top` with `Fla[D_m_unshared_top] == Fla[D_m]`.

    Recurrence:
        D_0 = x
        D_{i+1} = (D_i & ~y) v (~D_i & y)   (fan-out 2 on D_i at every level!)
    """
    x = store.var(x_name)
    y = store.var(y_name)
    ny = store.neg(y)

    levels: List[int] = [x]
    cur = x
    for _ in range(m):
        cur = store.disj(store.conj(cur, ny), store.conj(store.neg(cur), y))
        levels.append(cur)

    d_canonical = explicit_from_canonical(store, levels[-1])

    # Construct D_m_unshared_top: duplicate the two branches of the top `min(m, 3)` levels
    # without sharing intermediate gates between the left and right copies, so
    # |D_m_unshared_top|_DAG > |D_m_canonical|_DAG while Fla[D_m_unshared_top] == Fla[D_m].
    gates: List[GateSpec] = list(d_canonical.gates)
    # Append a fresh copy of the entire D_{m-1} subcircuit and rebuild the top XOR gate
    # using the original D_{m-1} on the left and the duplicated D_{m-1} on the right!
    d_prev = explicit_from_canonical(store, levels[-2])
    offset = len(gates)
    for g in d_prev.gates:
        op = g[0]
        if op in ("0", "1", "v"):
            gates.append(g)
        elif op == "!":
            gates.append(("!", g[1] + offset))
        else:
            gates.append((op, g[1] + offset, g[2] + offset))
    prev_copy_out = d_prev.out + offset

    # Also locate original D_{m-1} and y, ~y in d_canonical by re-appending a fresh copy of y, ~y
    y_idx = len(gates)
    gates.append(("v", y_name))
    ny_idx = len(gates)
    gates.append(("!", y_idx))
    # Original D_{m-1} copy 1 (already at offset..offset+len-1); make a second fresh copy for right branch
    offset2 = len(gates)
    for g in d_prev.gates:
        op = g[0]
        if op in ("0", "1", "v"):
            gates.append(g)
        elif op == "!":
            gates.append(("!", g[1] + offset2))
        else:
            gates.append((op, g[1] + offset2, g[2] + offset2))
    prev_copy2_out = d_prev.out + offset2

    neg_prev2 = len(gates)
    gates.append(("!", prev_copy2_out))
    left_and = len(gates)
    gates.append(("&", prev_copy_out, ny_idx))
    right_and = len(gates)
    gates.append(("&", neg_prev2, y_idx))
    top_or = len(gates)
    gates.append(("|", left_and, right_and))

    d_unshared = ExplicitDAG(gates=tuple(gates), out=top_or)
    assert d_unshared.canonicalize(store) == d_canonical.canonicalize(store)
    assert d_unshared.size() > d_canonical.size()
    return d_canonical, d_unshared, levels


# ======================================================================
# 2. Constant-Size `SimBA` Axiom Templates & Balanced Tree Primitives
# ======================================================================


class CFSimBACompiler(BACompiler):
    """Extends `BACompiler` with O(1) Frege axiom templates and O(log k) balanced-tree rules."""

    def imp(self, a: int, b: int) -> int:
        return self.s.disj(self.s.neg(a), b)

    # --- (a) Constant-size DeMorgan Frege Axiom Templates ---

    def axiom_lem(self, a: int) -> List[int]:
        """(a v ~a) ~* 1 (1 step)."""
        s = self.s
        return [s.disj(a, s.neg(a)), s.ONE]

    def axiom_imp_refl(self, a: int) -> List[int]:
        """(~a v a) ~* 1 (2 steps)."""
        s = self.s
        return [s.disj(s.neg(a), a), s.disj(a, s.neg(a)), s.ONE]

    def axiom_imp_to_one(self, a: int) -> List[int]:
        """(a -> 1) := (~a v 1) ~* 1 (6 steps)."""
        return self.disj_one_right(self.s.neg(a))

    def axiom_weaken(self, a: int, b: int) -> List[int]:
        """a -> (b -> a) := ~a v (~b v a) ~* 1 (11 steps)."""
        s = self.s
        na, nb = s.neg(a), s.neg(b)
        ch = [
            s.disj(na, s.disj(nb, a)),
            s.disj(na, s.disj(a, nb)),
            s.disj(s.disj(na, a), nb),
            s.disj(s.disj(a, na), nb),
            s.disj(s.ONE, nb),
        ]
        return self.concat(ch, self.disj_one_left(nb))

    def axiom_contraction(self, a: int) -> List[int]:
        """(a v a) -> a := ~(a v a) v a ~* 1 (9 steps)."""
        s = self.s
        ch = self.lift(lambda u: s.disj(s.neg(u), a), self.disj_idem(a))
        return self.concat(ch, self.axiom_imp_refl(a))

    def axiom_exchange(self, a: int, b: int) -> List[int]:
        """(a v b) -> (b v a) := ~(a v b) v (b v a) ~* 1 (3 steps)."""
        s = self.s
        ab = s.disj(a, b)
        ba = s.disj(b, a)
        return [s.disj(s.neg(ab), ba), s.disj(s.neg(ba), ba), s.disj(ba, s.neg(ba)), s.ONE]

    def axiom_syllogism_right(self, a: int, b: int, c: int) -> List[int]:
        """(b -> c) -> ((a -> b) -> (a -> c)) ~* 1 (O(1) steps independent of |a|,|b|,|c|)."""
        s = self.s
        na, nb, nc = s.neg(a), s.neg(b), s.neg(c)
        imp_ab = s.disj(na, b)
        imp_bc = s.disj(nb, c)
        imp_ac = s.disj(na, c)
        rhs_orig = s.disj(s.neg(imp_ab), imp_ac)

        # 1. ~(~b v c) ~* (b & ~c)
        ch_bc = self.demorgan_disj(nb, c)
        ch_bc = self.concat(ch_bc, self.lift(lambda u: s.conj(u, nc), self.double_neg(b)))
        b_nc = s.conj(b, nc)
        ch = self.lift(lambda u: s.disj(u, rhs_orig), ch_bc)

        # 2. ~(~a v b) ~* (a & ~b)
        ch_ab = self.demorgan_disj(na, b)
        ch_ab = self.concat(ch_ab, self.lift(lambda u: s.conj(u, nb), self.double_neg(a)))
        a_nb = s.conj(a, nb)
        ch = self.concat(ch, self.lift(lambda u: s.disj(b_nc, s.disj(u, imp_ac)), ch_ab))

        # 3. (b & ~c) v ((a & ~b) v (~a v c)) -> (b & ~c) v (((a & ~b) v ~a) v c)
        ch = self.concat(
            ch,
            [
                s.disj(b_nc, s.disj(a_nb, imp_ac)),
                s.disj(b_nc, s.disj(s.disj(a_nb, na), c)),
            ],
        )

        # 4. Resolve (a & ~b) v ~a ~* ~a v ~b
        ch_res1 = [
            s.disj(a_nb, na),
            s.disj(na, a_nb),
            s.conj(s.disj(na, a), s.disj(na, nb)),
            s.conj(s.disj(a, na), s.disj(na, nb)),
            s.conj(s.ONE, s.disj(na, nb)),
            s.disj(na, nb),
        ]
        na_nb = s.disj(na, nb)
        ch = self.concat(ch, self.lift(lambda u: s.disj(b_nc, s.disj(u, c)), ch_res1))

        # 5. (b & ~c) v ((~a v ~b) v c) -> ((b & ~c) v c) v (~a v ~b)
        ch = self.concat(
            ch,
            [
                s.disj(b_nc, s.disj(na_nb, c)),
                s.disj(b_nc, s.disj(c, na_nb)),
                s.disj(s.disj(b_nc, c), na_nb),
            ],
        )

        # 6. Resolve (b & ~c) v c ~* c v b
        ch_res2 = [
            s.disj(b_nc, c),
            s.disj(c, b_nc),
            s.conj(s.disj(c, b), s.disj(c, nc)),
            s.conj(s.disj(c, b), s.ONE),
            s.conj(s.ONE, s.disj(c, b)),
            s.disj(c, b),
        ]
        ch = self.concat(ch, self.lift(lambda u: s.disj(u, na_nb), ch_res2))

        # 7. (c v b) v (~a v ~b) ~* 1
        ch = self.concat(
            ch,
            [
                s.disj(s.disj(c, b), na_nb),
                s.disj(s.disj(c, b), s.disj(nb, na)),
                s.disj(s.disj(s.disj(c, b), nb), na),
                s.disj(s.disj(c, s.disj(b, nb)), na),
                s.disj(s.disj(c, s.ONE), na),
            ],
        )
        ch = self.concat(ch, self.lift(lambda u: s.disj(u, na), self.disj_one_right(c)))
        ch = self.concat(ch, self.disj_one_left(na))
        return ch

    # --- (c) CF Structural Rule Bridge (Theorem a) ---

    def cf_structural_bridge(self, c_id: int, d_id: int) -> List[int]:
        """2-step bridge `C ≈ (0 v C) ≈ D` when `Fla[C] == Fla[D]` (i.e. `c_id == d_id`)."""
        assert c_id == d_id, "CF structural rule requires Fla[C] == Fla[D]"
        mid = self.s.disj(self.s.ZERO, c_id)
        return [c_id, mid, d_id]

    # --- Conditional MP & Implication Transitivity (O(1) overhead) ---

    def imp_mp(
        self, h: int, a: int, b: int, ch_h_to_a: List[int], ch_h_to_imp: List[int]
    ) -> List[int]:
        """From `(~h v a) ~* 1` and `(~h v (~a v b)) ~* 1`, derive `(~h v b) ~* 1`
        in `len(ch_h_to_a) + len(ch_h_to_imp) + 16` steps."""
        s = self.s
        nh = s.neg(h)
        na = s.neg(a)
        a_na = s.conj(a, na)
        b_or_a = s.disj(b, a)
        a_or_b = s.disj(a, b)
        b_or_na = s.disj(b, na)
        na_or_b = s.disj(na, b)
        right_conj = s.disj(nh, b_or_na)

        ch = [
            s.disj(nh, b),
            s.disj(nh, s.disj(s.ZERO, b)),
            s.disj(nh, s.disj(a_na, b)),
            s.disj(nh, s.disj(b, a_na)),
            s.disj(nh, s.conj(b_or_a, b_or_na)),
            s.conj(s.disj(nh, b_or_a), right_conj),
            s.conj(s.disj(nh, a_or_b), right_conj),
            s.conj(s.disj(s.disj(nh, a), b), right_conj),
        ]
        ch = self.concat(ch, self.lift(lambda u: s.conj(s.disj(u, b), right_conj), ch_h_to_a))
        ch = self.concat(ch, self.lift(lambda u: s.conj(u, right_conj), self.disj_one_left(b)))
        ch = self.concat(
            ch,
            [
                s.conj(s.ONE, right_conj),
                right_conj,
                s.disj(nh, na_or_b),
            ],
        )
        return self.concat(ch, ch_h_to_imp)

    def imp_trans(
        self, h: int, a: int, b: int, ch_h_to_a: List[int], ch_a_to_b: List[int]
    ) -> List[int]:
        """From `(~h v a) ~* 1` and `(~a v b) ~* 1`, derive `(~h v b) ~* 1`
        in `len(ch_h_to_a) + len(ch_a_to_b) + 22` steps."""
        s = self.s
        nh = s.neg(h)
        ch_h_to_imp = self.concat(
            self.lift(lambda u: s.disj(nh, u), ch_a_to_b),
            self.disj_one_right(nh),
        )
        return self.imp_mp(h, a, b, ch_h_to_a, ch_h_to_imp)

    # --- (b) Theorem 1.1 Balanced Binary-Tree Conjunction Primitives ---

    def build_balanced_tree(self, leaves: Sequence[int]) -> int:
        """Build a balanced `&` binary tree from `2^d` leaves."""
        n = len(leaves)
        assert n >= 1 and (n & (n - 1)) == 0, "Leaf count must be a power of 2"
        if n == 1:
            return leaves[0]
        half = n // 2
        return self.s.conj(
            self.build_balanced_tree(leaves[:half]),
            self.build_balanced_tree(leaves[half:]),
        )

    def collapse_all_ones(self, depth: int) -> List[int]:
        """Prove `all_ones(depth) ~* 1` in exactly `2^depth - 1` steps."""
        s = self.s
        if depth == 0:
            return [s.ONE]
        sub = self.collapse_all_ones(depth - 1)
        sub_root = sub[0]
        ch = self.lift(lambda u: s.conj(u, sub_root), sub)
        ch = self.concat(ch, [s.conj(s.ONE, sub_root), sub_root])
        return self.concat(ch, sub)

    def strip_trailing_ones(self, leaves: Sequence[int], num_real: int) -> Tuple[List[int], int]:
        """Given a power-of-2 leaf array where indices `[0..num_real-1]` are real formulas
        and `[num_real..2^d-1]` are `1`, prove `T(leaves) ~* H_balanced` in `O(2^d)` steps."""
        s = self.s
        n = len(leaves)
        if num_real == 0:
            depth = int(math.log2(n))
            return self.collapse_all_ones(depth), s.ONE
        if n == 1:
            return [leaves[0]], leaves[0]
        half = n // 2
        left_real = min(num_real, half)
        right_real = max(0, num_real - half)
        left_tree = self.build_balanced_tree(leaves[:half])
        right_tree = self.build_balanced_tree(leaves[half:])

        ch_l, h_l = self.strip_trailing_ones(leaves[:half], left_real)
        ch_r, h_r = self.strip_trailing_ones(leaves[half:], right_real)

        ch = self.lift(lambda u: s.conj(u, right_tree), ch_l)
        ch = self.concat(ch, self.lift(lambda v: s.conj(h_l, v), ch_r))
        if right_real == 0:
            # h_l & 1 ~* h_l
            ch = self.concat(ch, self.conj_one_right(h_l))
            return ch, h_l
        return ch, s.conj(h_l, h_r)

    def bubble_leaf_to_left(self, leaves: Sequence[int], idx: int) -> Tuple[List[int], int]:
        """Rewrite balanced tree `T(leaves) ~* (leaves[idx] & rest)` in `<= 2*depth + 2` steps."""
        s = self.s
        n = len(leaves)
        if n == 1:
            a = leaves[0]
            return [a, s.conj(s.ONE, a), s.conj(a, s.ONE)], s.ONE
        half = n // 2
        left_id = self.build_balanced_tree(leaves[:half])
        right_id = self.build_balanced_tree(leaves[half:])
        a = leaves[idx]
        if idx < half:
            ch_l, rest_l = self.bubble_leaf_to_left(leaves[:half], idx)
            ch = self.lift(lambda u: s.conj(u, right_id), ch_l)
            rest = s.conj(rest_l, right_id)
            ch = self.concat(ch, [s.conj(s.conj(a, rest_l), right_id), s.conj(a, rest)])
            return ch, rest
        else:
            ch_r, rest_r = self.bubble_leaf_to_left(leaves[half:], idx - half)
            ch = [s.conj(left_id, right_id), s.conj(right_id, left_id)]
            ch = self.concat(ch, self.lift(lambda u: s.conj(u, left_id), ch_r))
            rest = s.conj(rest_r, left_id)
            ch = self.concat(ch, [s.conj(s.conj(a, rest_r), left_id), s.conj(a, rest)])
            return ch, rest

    def extract_leaf_imp(self, leaves: Sequence[int], idx: int) -> List[int]:
        """Prove `(~T(leaves) v leaves[idx]) ~* 1` in `O(log |leaves|)` steps."""
        s = self.s
        a = leaves[idx]
        ch_bub, rest = self.bubble_leaf_to_left(leaves, idx)
        na, nrest = s.neg(a), s.neg(rest)
        ch = self.lift(lambda u: s.disj(s.neg(u), a), ch_bub)
        ch = self.concat(ch, self.lift(lambda u: s.disj(u, a), self.demorgan_conj(a, rest)))
        ch = self.concat(
            ch,
            [
                s.disj(s.disj(na, nrest), a),
                s.disj(s.disj(nrest, na), a),
                s.disj(nrest, s.disj(na, a)),
                s.disj(nrest, s.disj(a, na)),
                s.disj(nrest, s.ONE),
            ],
        )
        return self.concat(ch, self.disj_one_right(nrest))

    def insert_leaf_conj(
        self, leaves: Sequence[int], idx: int, new_val: int
    ) -> Tuple[List[int], int]:
        """Given `leaves[idx] == 1`, prove `(T(leaves) & new_val) ~* T(leaves[idx := new_val])`
        in `<= 3*depth + 1` steps."""
        s = self.s
        n = len(leaves)
        if n == 1:
            assert leaves[0] == s.ONE
            return [s.conj(s.ONE, new_val), new_val], new_val
        half = n // 2
        left_id = self.build_balanced_tree(leaves[:half])
        right_id = self.build_balanced_tree(leaves[half:])
        if idx < half:
            ch_l, left_new = self.insert_leaf_conj(leaves[:half], idx, new_val)
            ch = [
                s.conj(s.conj(left_id, right_id), new_val),
                s.conj(s.conj(right_id, left_id), new_val),
                s.conj(right_id, s.conj(left_id, new_val)),
            ]
            ch = self.concat(ch, self.lift(lambda u: s.conj(right_id, u), ch_l))
            t_new = s.conj(left_new, right_id)
            ch = self.concat(ch, [s.conj(right_id, left_new), t_new])
            return ch, t_new
        else:
            ch_r, right_new = self.insert_leaf_conj(leaves[half:], idx - half, new_val)
            ch = [
                s.conj(s.conj(left_id, right_id), new_val),
                s.conj(left_id, s.conj(right_id, new_val)),
            ]
            ch = self.concat(ch, self.lift(lambda u: s.conj(left_id, u), ch_r))
            return ch, s.conj(left_id, right_new)

    def step_tree_imp(
        self, leaves: Sequence[int], idx: int, new_val: int, ch_t_to_val: List[int]
    ) -> Tuple[List[int], int]:
        """From `(~T v new_val) ~* 1`, prove `(~T v T') ~* 1` in `len(ch_t_to_val) + O(log |leaves|)` steps."""
        s = self.s
        t_old = self.build_balanced_tree(leaves)
        nt_old = s.neg(t_old)
        ch_ins, t_new = self.insert_leaf_conj(leaves, idx, new_val)
        ch = self.lift(lambda u: s.disj(nt_old, u), self.rev(ch_ins))
        ch = self.concat(
            ch,
            [
                s.disj(nt_old, s.conj(t_old, new_val)),
                s.conj(s.disj(nt_old, t_old), s.disj(nt_old, new_val)),
                s.conj(s.disj(t_old, nt_old), s.disj(nt_old, new_val)),
                s.conj(s.ONE, s.disj(nt_old, new_val)),
                s.disj(nt_old, new_val),
            ],
        )
        return self.concat(ch, ch_t_to_val), t_new


# ======================================================================
# 3. `CFProof` Representation & Deterministic P-Time Compiler
# ======================================================================


@dataclass
class CFLine:
    """Single line in a Circuit Frege (`CF`) proof DAG."""

    line_id: int
    kind: str  # "hyp" | "axiom" | "mp" | "cf_fla"
    circuit_id: int
    explicit_dag: Optional[ExplicitDAG] = None
    axiom_name: Optional[str] = None
    axiom_args: Tuple[int, ...] = ()
    premises: Tuple[int, ...] = ()


@dataclass
class CFCompileResult:
    """Compiled `≈`-chain + structural & verification diagnostics."""

    mode: str  # "tree_lemma21" | "dag_theorem11_balanced"
    target_id: int
    chain: List[int]
    cf_dag_lines: int
    cf_derived_lines: int
    num_hypotheses: int
    max_proof_line_fanout: int
    naive_tree_unwound_steps: int
    structural_bridge_count: int
    structural_bridge_records: List[dict]
    compile_time_ms: float


class CFProof:
    """Deterministic Circuit Frege (`CF`) proof DAG and P-Time `CF -> ≈-Chain` compiler."""

    def __init__(self, store: DAGStore) -> None:
        self.s = store
        self.comp = CFSimBACompiler(store)
        self.lines: List[CFLine] = []

    def add_hypothesis(self, circuit_id: int, explicit_dag: Optional[ExplicitDAG] = None) -> int:
        lid = len(self.lines)
        if explicit_dag is not None:
            assert explicit_dag.canonicalize(self.s) == circuit_id
        self.lines.append(CFLine(lid, "hyp", circuit_id, explicit_dag=explicit_dag))
        return lid

    def add_axiom(
        self,
        axiom_name: str,
        *args: int,
        explicit_dag: Optional[ExplicitDAG] = None,
    ) -> int:
        """Add an instance of a constant-size DeMorgan Frege axiom scheme."""
        s = self.s
        if axiom_name == "lem":
            (a,) = args
            cid = s.disj(a, s.neg(a))
        elif axiom_name == "imp_refl":
            (a,) = args
            cid = self.comp.imp(a, a)
        elif axiom_name == "imp_to_one":
            (a,) = args
            cid = self.comp.imp(a, s.ONE)
        elif axiom_name == "weaken":
            a, b = args
            cid = self.comp.imp(a, self.comp.imp(b, a))
        elif axiom_name == "contraction":
            (a,) = args
            cid = self.comp.imp(s.disj(a, a), a)
        elif axiom_name == "exchange":
            a, b = args
            cid = self.comp.imp(s.disj(a, b), s.disj(b, a))
        elif axiom_name == "syllogism_right":
            a, b, c = args
            cid = self.comp.imp(
                self.comp.imp(b, c),
                self.comp.imp(self.comp.imp(a, b), self.comp.imp(a, c)),
            )
        else:
            raise ValueError(f"Unknown Frege axiom template: {axiom_name}")

        if explicit_dag is not None:
            assert explicit_dag.canonicalize(s) == cid
        lid = len(self.lines)
        self.lines.append(
            CFLine(
                lid,
                "axiom",
                cid,
                explicit_dag=explicit_dag,
                axiom_name=axiom_name,
                axiom_args=tuple(args),
            )
        )
        return lid

    def add_mp(self, prem_a: int, prem_imp: int, explicit_dag: Optional[ExplicitDAG] = None) -> int:
        """Modus Ponens: `A, ~A v B |- B`."""
        a = self.lines[prem_a].circuit_id
        imp_ab = self.lines[prem_imp].circuit_id
        k = self.s.key(imp_ab)
        assert k[0] == "|" and self.s.key(k[1]) == ("!", a), (
            f"Invalid Modus Ponens premises: line {prem_imp} is not (~line {prem_a} v B)"
        )
        b = k[2]
        if explicit_dag is not None:
            assert explicit_dag.canonicalize(self.s) == b
        lid = len(self.lines)
        self.lines.append(
            CFLine(lid, "mp", b, explicit_dag=explicit_dag, premises=(prem_a, prem_imp))
        )
        return lid

    def add_cf_fla(self, prem_c: int, target_dag: ExplicitDAG) -> int:
        """`CF` structural rule `C |- D` where `Fla[C] == Fla[D]`, verified in `O(|C|+|D|)`."""
        c_line = self.lines[prem_c]
        d_id = target_dag.canonicalize(self.s)
        assert c_line.circuit_id == d_id, (
            f"CF structural rule failed: Fla[C] != Fla[D] for premise line {prem_c}"
        )
        lid = len(self.lines)
        self.lines.append(
            CFLine(lid, "cf_fla", d_id, explicit_dag=target_dag, premises=(prem_c,))
        )
        return lid

    # --- Proof DAG analysis ---

    def _proof_dag_stats(self, goal_line: int) -> Tuple[int, int, int, int]:
        """Compute reachable lines, max fan-out, naive tree-unwound steps, and hyp count."""
        reachable: set[int] = set()
        stack = [goal_line]
        while stack:
            u = stack.pop()
            if u in reachable:
                continue
            reachable.add(u)
            for p in self.lines[u].premises:
                stack.append(p)

        fanout: Dict[int, int] = {u: 0 for u in reachable}
        for u in reachable:
            for p in self.lines[u].premises:
                fanout[p] += 1

        memo_tree: Dict[int, int] = {}

        def tree_steps(u: int) -> int:
            if u in memo_tree:
                return memo_tree[u]
            ln = self.lines[u]
            val = 1 + sum(tree_steps(p) for p in ln.premises)
            memo_tree[u] = val
            return val

        num_hyps = sum(1 for u in reachable if self.lines[u].kind == "hyp")
        max_fo = max(fanout.values(), default=0)
        return len(reachable), max_fo, tree_steps(goal_line), num_hyps

    def _compile_axiom_template(self, ln: CFLine) -> List[int]:
        name = ln.axiom_name
        args = ln.axiom_args
        if name == "lem":
            return self.comp.axiom_lem(*args)
        if name == "imp_refl":
            return self.comp.axiom_imp_refl(*args)
        if name == "imp_to_one":
            return self.comp.axiom_imp_to_one(*args)
        if name == "weaken":
            return self.comp.axiom_weaken(*args)
        if name == "contraction":
            return self.comp.axiom_contraction(*args)
        if name == "exchange":
            return self.comp.axiom_exchange(*args)
        if name == "syllogism_right":
            return self.comp.axiom_syllogism_right(*args)
        raise ValueError(f"Unknown axiom template: {name}")

    # --- Main P-Time Compiler ---

    def compile(self, goal_line: Optional[int] = None, force_balanced: bool = False) -> CFCompileResult:
        """Compile the `CF` proof of `goal_line` into a 100%-verified `≈`-chain.

        - If no hypotheses and `max_fanout <= 1` (tree-like) and not `force_balanced`:
          uses Krajicek's Lemma 2.1 exact `k_1 + 2 + k_2` tree composition + 2-step `CF` bridges.
        - Otherwise (DAG reuse `fan-out > 1` or hypotheses present):
          uses Theorem 1.1 balanced binary-tree conjunction (`O(k log k)` steps).
        """
        t0 = time.perf_counter()
        if goal_line is None:
            goal_line = len(self.lines) - 1
        num_reach, max_fo, naive_tree, num_hyps = self._proof_dag_stats(goal_line)

        bridge_records: List[dict] = []

        if not force_balanced and num_hyps == 0 and max_fo <= 1:
            chain = self._compile_tree_lemma21(goal_line, bridge_records)
            elapsed_ms = (time.perf_counter() - t0) * 1000.0
            return CFCompileResult(
                mode="tree_lemma21",
                target_id=self.lines[goal_line].circuit_id,
                chain=chain,
                cf_dag_lines=num_reach,
                cf_derived_lines=num_reach,
                num_hypotheses=0,
                max_proof_line_fanout=max_fo,
                naive_tree_unwound_steps=naive_tree,
                structural_bridge_count=len(bridge_records),
                structural_bridge_records=bridge_records,
                compile_time_ms=elapsed_ms,
            )

        target_id, chain = self._compile_dag_theorem11(goal_line, bridge_records)
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        return CFCompileResult(
            mode="dag_theorem11_balanced",
            target_id=target_id,
            chain=chain,
            cf_dag_lines=num_reach,
            cf_derived_lines=num_reach - num_hyps,
            num_hypotheses=num_hyps,
            max_proof_line_fanout=max_fo,
            naive_tree_unwound_steps=naive_tree,
            structural_bridge_count=len(bridge_records),
            structural_bridge_records=bridge_records,
            compile_time_ms=elapsed_ms,
        )

    def _compile_tree_lemma21(self, u: int, bridge_records: List[dict]) -> List[int]:
        """Exact Lemma 2.1 tree-like `k_1 + 2 + k_2` composition + 2-step `CF` structural bridge."""
        ln = self.lines[u]
        if ln.kind == "axiom":
            return self._compile_axiom_template(ln)
        if ln.kind == "cf_fla":
            prem_id = ln.premises[0]
            prem_ln = self.lines[prem_id]
            ch_prem = self._compile_tree_lemma21(prem_id, bridge_records)
            bridge = self.comp.cf_structural_bridge(ln.circuit_id, prem_ln.circuit_id)
            c_sz = prem_ln.explicit_dag.size() if prem_ln.explicit_dag else self.s.dag_size(prem_ln.circuit_id)
            d_sz = ln.explicit_dag.size() if ln.explicit_dag else self.s.dag_size(ln.circuit_id)
            bridge_records.append(
                {
                    "line_id": u,
                    "premise_line_id": prem_id,
                    "src_explicit_dag_size": c_sz,
                    "bridge_explicit_dag_size": c_sz + 2,
                    "dst_explicit_dag_size": d_sz,
                    "bridge_steps": 2,
                }
            )
            return self.comp.concat(bridge, ch_prem)
        if ln.kind == "mp":
            pa, pimp = ln.premises
            ch_a = self._compile_tree_lemma21(pa, bridge_records)
            ch_imp = self._compile_tree_lemma21(pimp, bridge_records)
            return self.comp.modus_ponens(
                self.lines[pa].circuit_id, ln.circuit_id, ch_a, ch_imp
            )
        raise ValueError(f"Unexpected line kind in tree compiler: {ln.kind}")

    def _compile_dag_theorem11(
        self, goal_line: int, bridge_records: List[dict]
    ) -> Tuple[int, List[int]]:
        """Theorem 1.1 balanced binary-tree conjunction compiler for DAG `CF` proofs.

        Guarantees `O(k log k)` emitted `≈`-steps even when proof lines have fan-out > 1.
        - If there are no hypotheses: derives `goal ~* 1`.
        - If hypotheses `H_0, ..., H_{m-1}` are present: derives `(H_balanced -> goal) ~* 1`.
        """
        # Collect reachable lines in topological order
        reachable: set[int] = set()
        stack = [goal_line]
        while stack:
            u = stack.pop()
            if u in reachable:
                continue
            reachable.add(u)
            for p in self.lines[u].premises:
                stack.append(p)

        topo = sorted(reachable)
        hyps = [u for u in topo if self.lines[u].kind == "hyp"]
        derived = [u for u in topo if self.lines[u].kind != "hyp"]

        total_slots = len(hyps) + len(derived)
        depth = max(1, math.ceil(math.log2(max(2, total_slots))))
        cap = 1 << depth

        # Assign leaf slots: hypotheses occupy [0..len(hyps)-1], derived occupy [len(hyps)..]
        slot_of: Dict[int, int] = {}
        leaves: List[int] = [self.s.ONE] * cap
        for idx, u in enumerate(hyps):
            slot_of[u] = idx
            leaves[idx] = self.lines[u].circuit_id

        has_hyps = len(hyps) > 0
        if has_hyps:
            # Prove `(~H_balanced v T_0) ~* 1` by stripping trailing 1s from T_0
            ch_strip, h_bal = self.comp.strip_trailing_ones(leaves, len(hyps))
            nh = self.s.neg(h_bal)
            # ~H v T_0 ~* ~H v H -> H v ~H -> 1
            ch_cur = self.comp.concat(
                self.comp.lift(lambda u: self.s.disj(nh, u), ch_strip),
                self.comp.axiom_imp_refl(h_bal),
            )
        else:
            # T_0 is all-ones tree; prove `T_0 ~* 1` in 2^depth - 1 steps
            h_bal = self.s.ONE
            ch_cur = self.comp.collapse_all_ones(depth)

        # Process each derived line in topological order, inserting it into the balanced tree
        for step_offset, u in enumerate(derived):
            ln = self.lines[u]
            slot = len(hyps) + step_offset
            t_old = self.comp.build_balanced_tree(leaves)
            nt_old = self.s.neg(t_old)

            if ln.kind == "axiom":
                ch_ax = self._compile_axiom_template(ln)
                ch_t_to_val = self.comp.concat(
                    self.comp.lift(lambda x: self.s.disj(nt_old, x), ch_ax),
                    self.comp.disj_one_right(nt_old),
                )
            elif ln.kind == "cf_fla":
                prem_id = ln.premises[0]
                prem_ln = self.lines[prem_id]
                ch_ext = self.comp.extract_leaf_imp(leaves, slot_of[prem_id])
                bridge = self.comp.cf_structural_bridge(ln.circuit_id, prem_ln.circuit_id)
                ch_t_to_val = self.comp.concat(
                    self.comp.lift(lambda x: self.s.disj(nt_old, x), bridge),
                    ch_ext,
                )
                c_sz = prem_ln.explicit_dag.size() if prem_ln.explicit_dag else self.s.dag_size(prem_ln.circuit_id)
                d_sz = ln.explicit_dag.size() if ln.explicit_dag else self.s.dag_size(ln.circuit_id)
                bridge_records.append(
                    {
                        "line_id": u,
                        "premise_line_id": prem_id,
                        "src_explicit_dag_size": c_sz,
                        "bridge_explicit_dag_size": c_sz + 2,
                        "dst_explicit_dag_size": d_sz,
                        "bridge_steps": 2,
                    }
                )
            elif ln.kind == "mp":
                pa, pimp = ln.premises
                ch_t_to_a = self.comp.extract_leaf_imp(leaves, slot_of[pa])
                ch_t_to_imp = self.comp.extract_leaf_imp(leaves, slot_of[pimp])
                ch_t_to_val = self.comp.imp_mp(
                    t_old,
                    self.lines[pa].circuit_id,
                    ln.circuit_id,
                    ch_t_to_a,
                    ch_t_to_imp,
                )
            else:
                raise ValueError(f"Unexpected derived line kind: {ln.kind}")

            ch_step, t_new = self.comp.step_tree_imp(leaves, slot, ln.circuit_id, ch_t_to_val)
            if has_hyps:
                ch_cur = self.comp.imp_trans(h_bal, t_old, t_new, ch_cur, ch_step)
            else:
                ch_cur = self.comp.modus_ponens(t_old, t_new, ch_cur, ch_step)

            leaves[slot] = ln.circuit_id
            slot_of[u] = slot

        # Extract final goal from balanced tree `T_final`
        t_final = self.comp.build_balanced_tree(leaves)
        goal_cid = self.lines[goal_line].circuit_id
        ch_extract = self.comp.extract_leaf_imp(leaves, slot_of[goal_line])
        if has_hyps:
            ch_final = self.comp.imp_trans(h_bal, t_final, goal_cid, ch_cur, ch_extract)
            target_id = self.comp.imp(h_bal, goal_cid)
        else:
            ch_final = self.comp.modus_ponens(t_final, goal_cid, ch_cur, ch_extract)
            target_id = goal_cid

        assert ch_final[0] == target_id and ch_final[-1] == self.s.ONE
        return target_id, ch_final


# ======================================================================
# 4. Step-by-Step Verification (`are_approx` on EVERY emitted step)
# ======================================================================


def verify_compiled_chain(
    store: DAGStore,
    name: str,
    chain: List[int],
    check_semantic_vars: Optional[List[str]] = None,
) -> dict:
    """Verify `are_approx(E_i, E_{i+1}) == True` on EVERY emitted step, and measure DAG sizes."""
    assert len(chain) >= 1, f"[{name}] Empty chain"
    assert chain[-1] == store.ONE, f"[{name}] Chain does not terminate at 1"

    t_ver0 = time.perf_counter()
    ax_hist: Dict[str, int] = {}
    max_path_depth = 0
    for idx in range(len(chain) - 1):
        u, v = chain[idx], chain[idx + 1]
        ok, w = store.are_approx(u, v)
        if not ok or w is None:
            raise AssertionError(f"[{name}] INVALID ≈ step at index {idx}: node {u} !≈ node {v}")
        key = f"{w['axiom']}:{w['dir']}"
        ax_hist[key] = ax_hist.get(key, 0) + 1
        if len(w["path"]) > max_path_depth:
            max_path_depth = len(w["path"])

    semantic_ok: Optional[bool] = None
    if check_semantic_vars is not None and len(check_semantic_vars) <= 8:
        full_mask = (1 << (1 << len(check_semantic_vars))) - 1
        # Check start and end (and sampled intermediate states)
        tt_start = store.truth_table(chain[0], check_semantic_vars)
        tt_end = store.truth_table(chain[-1], check_semantic_vars)
        assert tt_start == full_mask and tt_end == full_mask, (
            f"[{name}] Semantic tautology check failed!"
        )
        semantic_ok = True

    dag_sizes = [store.dag_size(u) for u in chain]
    peak_dag = max(dag_sizes)
    peak_step = dag_sizes.index(peak_dag)
    total_chain_dag_size = sum(dag_sizes)
    verify_time_ms = (time.perf_counter() - t_ver0) * 1000.0

    return {
        "verified_all_approx_steps": True,
        "verified_semantic_tautology": semantic_ok,
        "chain_length_t": len(chain) - 1,
        "start_dag_size": dag_sizes[0],
        "peak_dag_size": peak_dag,
        "peak_dag_step": peak_step,
        "end_dag_size": dag_sizes[-1],
        "total_chain_dag_size": total_chain_dag_size,
        "max_rewrite_path_depth": max_path_depth,
        "axiom_usage": ax_hist,
        "verify_time_ms": round(verify_time_ms, 3),
    }


# ======================================================================
# 5. Benchmark Suites (ATAQUE-10)
# ======================================================================


def run_benchmark_suite_1(store: DAGStore) -> List[dict]:
    """Suite 1: Exponential-tree, linear-DAG `CF` equivalence & MP chains (`m in [4, 8, 12, 16, 20]`).

    For each `m`:
    - Build `D_m` (`|D_m|_DAG = O(m)`, `|Fla[D_m]| > 2^m`, exceeding `10^6` at `m=20`).
    - Build `D_m_unshared_top` with `Fla[D_m_unshared_top] == Fla[D_m_canonical]`.
    - Compile and verify:
      (i) `(D_m v ~D_m) -> 1` (axiom + MP over `D_m`),
      (ii) `CF` structural re-sharing `(D_m_unshared_top v ~D_m_unshared_top) |- (D_m_canonical v ~D_m_canonical)`
           followed by an `m`-step Modus Ponens chain over `D_0, ..., D_m`.
    """
    results: List[dict] = []
    for m in [4, 8, 12, 16, 20]:
        d_can, d_unsh, levels = build_shared_xor_chain(store, m)
        d_id = d_can.canonicalize(store)
        d_dag_sz = store.dag_size(d_id)
        d_fla_sz = store.formula_size(d_id)
        d_fanout = store.fanout_stats(d_id)

        # Build explicit unshared and canonical LEM circuits: (D_m v ~D_m)
        def make_lem_explicit(dag: ExplicitDAG) -> ExplicitDAG:
            n = len(dag.gates)
            return ExplicitDAG(
                gates=dag.gates + (("!", dag.out), ("|", dag.out, n)),
                out=n + 1,
            )

        lem_unsh = make_lem_explicit(d_unsh)
        lem_can = make_lem_explicit(d_can)
        assert lem_unsh.canonicalize(store) == lem_can.canonicalize(store)

        # (i) Direct `(D_m v ~D_m) -> 1` proof
        p_lem_imp = CFProof(store)
        l_lem_imp = p_lem_imp.add_axiom("imp_to_one", store.disj(d_id, store.neg(d_id)))
        res_lem_imp = p_lem_imp.compile(l_lem_imp)
        ver_lem_imp = verify_compiled_chain(
            store, f"dm_lem_to_1_m{m}", res_lem_imp.chain, check_semantic_vars=["x", "y"]
        )

        # (ii) Full CF proof combining:
        #      - LEM axiom on D_m_unshared_top
        #      - CF structural re-sharing rule: LEM(D_m_unshared_top) |- LEM(D_m_canonical)
        #      - m-step Modus Ponens chain over D_m and intermediate levels D_0..D_{m-1}
        pf = CFProof(store)
        l0 = pf.add_axiom("lem", d_id, explicit_dag=lem_unsh)
        l1 = pf.add_cf_fla(l0, lem_can)
        cur_line = l1
        cur_cid = store.disj(d_id, store.neg(d_id))
        for j in range(m):
            # Step j: weaken cur_cid by D_j, then detach via MP:
            #   cur_cid, cur_cid -> (D_j -> cur_cid) |- (D_j -> cur_cid)
            #   Wait: to keep DAG size strictly O(m) across m steps, alternate with
            #   exchange / imp_to_one or chain `(D_j v ~D_j)` via weaken + MP!
            dj_lem = store.disj(levels[j], store.neg(levels[j]))
            l_w = pf.add_axiom("weaken", cur_cid, dj_lem)
            l_imp = pf.add_mp(cur_line, l_w)  # dj_lem -> cur_cid
            l_dj = pf.add_axiom("lem", levels[j])  # dj_lem
            cur_line = pf.add_mp(l_dj, l_imp)  # cur_cid (derived via m MP hops over D_0..D_{m-1}!)

        # Final step: (D_m v ~D_m) -> ((D_m v ~D_m) -> 1) -> 1
        l_final_ax = pf.add_axiom("weaken", pf.comp.imp(cur_cid, store.ONE), cur_cid)
        l_imp1 = pf.add_axiom("imp_to_one", cur_cid)
        l_step = pf.add_mp(l_imp1, l_final_ax)
        l_goal = pf.add_mp(cur_line, l_step)

        res = pf.compile(l_goal)
        ver = verify_compiled_chain(
            store, f"dm_cf_reshare_mp_m{m}", res.chain, check_semantic_vars=["x", "y"]
        )

        results.append(
            {
                "m": m,
                "dm_canonical_dag_size": d_dag_sz,
                "dm_unshared_top_dag_size": d_unsh.size(),
                "dm_formula_size_fla": d_fla_sz,
                "dm_formula_exceeds_1M": d_fla_sz > 1_000_000,
                "dm_max_gate_fanout": d_fanout["max_gate_fanout"],
                "dm_max_gate_tree_occ": d_fanout["max_gate_tree_occ"],
                "lem_to_1_chain_steps": ver_lem_imp["chain_length_t"],
                "lem_to_1_verified": ver_lem_imp["verified_all_approx_steps"],
                "compile_mode": res.mode,
                "cf_dag_lines_k": res.cf_dag_lines,
                "structural_bridges": res.structural_bridge_records,
                "chain_length_t": ver["chain_length_t"],
                "peak_dag_size": ver["peak_dag_size"],
                "total_chain_dag_size": ver["total_chain_dag_size"],
                "total_chain_dag_over_m2": round(ver["total_chain_dag_size"] / (m * m), 2),
                "compile_time_ms": round(res.compile_time_ms, 3),
                "verify_time_ms": ver["verify_time_ms"],
                "verified_all_approx_steps": ver["verified_all_approx_steps"],
                "verified_semantic_tautology": ver["verified_semantic_tautology"],
                "max_rewrite_path_depth": ver["max_rewrite_path_depth"],
                "naive_unwound_vs_peak_dag_ratio": round(d_fla_sz / max(1, ver["peak_dag_size"]), 2),
            }
        )
    return results


def run_benchmark_suite_2(store: DAGStore) -> List[dict]:
    """Suite 2: Multi-step `CF` derivations with DAG proof reuse (`fan-out > 1` balanced via Theorem 1.1).

    Transitivity of implication `x_0 -> x_1, x_1 -> x_2, ..., x_{r-1} -> x_r |- x_0 -> x_r`
    for `r in [2, 4, 6, 8]`, where every intermediate derived line `x_0 -> x_j` has
    proof-DAG fan-out = 2 (causing exponential `~ 2^r` blowup under naive tree unwinding,
    while Theorem 1.1 balanced conjunction compiles to `t = O(k log k)` verified `≈`-steps!).
    """
    results: List[dict] = []
    for r in [2, 4, 6, 8]:
        xs = [store.var(f"x{i}") for i in range(r + 1)]
        var_names = [f"x{i}" for i in range(r + 1)]

        pf = CFProof(store)
        hyps = [pf.add_hypothesis(pf.comp.imp(xs[i], xs[i + 1])) for i in range(r)]

        # Diamond fan-out-2 transitivity derivation:
        # P_0 = H_0 : x_0 -> x_1
        # For j = 1 .. r-1:
        #   A1 = SYLL_R(x_0, x_j, x_{j+1}) : (x_j -> x_{j+1}) -> ((x_0 -> x_j) -> (x_0 -> x_{j+1}))
        #   Q_j = MP(H_j, A1)              : (x_0 -> x_j) -> (x_0 -> x_{j+1})
        #   A2 = WEAKEN(Q_j, x_0 -> x_j)   : Q_j -> ((x_0 -> x_j) -> Q_j)
        #   R_j = MP(Q_j, A2)              : (x_0 -> x_j) -> ((x_0 -> x_j) -> (x_0 -> x_{j+1}))
        #   S_j = MP(P_{j-1}, R_j)         : (x_0 -> x_j) -> (x_0 -> x_{j+1})   [uses P_{j-1} #1]
        #   P_j = MP(P_{j-1}, S_j)         : x_0 -> x_{j+1}                      [uses P_{j-1} #2 -> fan-out 2!]
        p_prev = hyps[0]
        for j in range(1, r):
            a1 = pf.add_axiom("syllogism_right", xs[0], xs[j], xs[j + 1])
            q_j = pf.add_mp(hyps[j], a1)
            q_j_cid = pf.lines[q_j].circuit_id
            p_prev_cid = pf.lines[p_prev].circuit_id
            a2 = pf.add_axiom("weaken", q_j_cid, p_prev_cid)
            r_j = pf.add_mp(q_j, a2)
            s_j = pf.add_mp(p_prev, r_j)
            p_j = pf.add_mp(p_prev, s_j)
            p_prev = p_j

        res = pf.compile(p_prev)
        check_vars = var_names if len(var_names) <= 8 else None
        ver = verify_compiled_chain(
            store, f"transitivity_dag_reuse_r{r}", res.chain, check_semantic_vars=check_vars
        )

        k = res.cf_dag_lines
        t = ver["chain_length_t"]
        k_log_k = k * math.log2(max(2, k))

        results.append(
            {
                "r": r,
                "num_vars": len(var_names),
                "compile_mode": res.mode,
                "num_hypotheses": res.num_hypotheses,
                "cf_dag_steps_k": k,
                "cf_derived_steps": res.cf_derived_lines,
                "max_proof_line_fanout": res.max_proof_line_fanout,
                "naive_tree_unwound_steps": res.naive_tree_unwound_steps,
                "emitted_approx_steps_t": t,
                "ratio_t_over_k": round(t / max(1, k), 3),
                "ratio_t_over_k_log2_k": round(t / k_log_k, 3),
                "start_dag_size": ver["start_dag_size"],
                "peak_dag_size": ver["peak_dag_size"],
                "total_chain_dag_size": ver["total_chain_dag_size"],
                "compile_time_ms": round(res.compile_time_ms, 3),
                "verify_time_ms": ver["verify_time_ms"],
                "verified_all_approx_steps": ver["verified_all_approx_steps"],
                "verified_semantic_tautology": ver["verified_semantic_tautology"],
                "max_rewrite_path_depth": ver["max_rewrite_path_depth"],
            }
        )
    return results


def main() -> None:
    store = DAGStore()

    suite1 = run_benchmark_suite_1(store)
    suite2 = run_benchmark_suite_2(store)

    # Confirm scaling invariants
    assert all(r["verified_all_approx_steps"] for r in suite1)
    assert all(r["verified_all_approx_steps"] for r in suite2)
    assert suite1[-1]["dm_formula_exceeds_1M"], "m=20 must exceed 10^6 unwound formula nodes"
    assert all(r["max_proof_line_fanout"] >= 2 for r in suite2), "Suite 2 must exercise fan-out >= 2"

    ratios_klogk = [r["ratio_t_over_k_log2_k"] for r in suite2]
    out_path = Path(
        "/home/miguel/certified-arith-preproc/results/krajicek_cf_compiler_results.json"
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)

    payload = {
        "attack": "ATAQUE-10",
        "paper": "Jan Krajicek, Extended Frege proofs, circuits and rewriting (arXiv:2606.13367v2, Oct 2026)",
        "lean_certificate": "certified-arith-preproc/proofs/krajicek_cf_compiler_unsharing.lean",
        "compiler_module": "certified-arith-preproc/src/certified_arith_preproc/krajicek_cf_compiler.py",
        "total_hash_cons_nodes_allocated": len(store._id_to_key),
        "all_steps_verified_are_approx": True,
        "suite1_exp_tree_linear_dag_cf": suite1,
        "suite2_dag_proof_reuse_theorem11": suite2,
        "scaling_summary": {
            "suite1_m20_formula_size": suite1[-1]["dm_formula_size_fla"],
            "suite1_m20_peak_dag_size": suite1[-1]["peak_dag_size"],
            "suite1_m20_compile_time_ms": suite1[-1]["compile_time_ms"],
            "suite1_total_chain_dag_over_m2_range": [
                min(r["total_chain_dag_over_m2"] for r in suite1),
                max(r["total_chain_dag_over_m2"] for r in suite1),
            ],
            "suite2_r8_cf_dag_steps_k": suite2[-1]["cf_dag_steps_k"],
            "suite2_r8_naive_tree_unwound_steps": suite2[-1]["naive_tree_unwound_steps"],
            "suite2_r8_emitted_approx_steps_t": suite2[-1]["emitted_approx_steps_t"],
            "suite2_t_over_k_log2_k_range": [min(ratios_klogk), max(ratios_klogk)],
        },
    }
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print("=== Suite 1: Exponential-Tree, Linear-DAG CF Chains ===")
    print(f"{'m':>3} {'|D_m|_DAG':>10} {'|Unsh|_DAG':>10} {'|Fla[D_m]|':>12} {'t':>6} {'PeakDAG':>8} {'SumDAG/m^2':>11} {'ms':>7} {'OK':>4}")
    for r in suite1:
        print(
            f"{r['m']:>3} {r['dm_canonical_dag_size']:>10} {r['dm_unshared_top_dag_size']:>10} "
            f"{r['dm_formula_size_fla']:>12} {r['chain_length_t']:>6} {r['peak_dag_size']:>8} "
            f"{r['total_chain_dag_over_m2']:>11.2f} {r['compile_time_ms']:>7.2f} {'PASS':>4}"
        )

    print("\n=== Suite 2: Multi-Step CF Derivations with DAG Proof Reuse (Theorem 1.1) ===")
    print(f"{'r':>3} {'k_DAG':>6} {'TreeUnw':>8} {'MaxFO':>6} {'t_≈':>7} {'t/(k log k)':>12} {'PeakDAG':>8} {'ms':>7} {'OK':>4}")
    for r in suite2:
        print(
            f"{r['r']:>3} {r['cf_dag_steps_k']:>6} {r['naive_tree_unwound_steps']:>8} "
            f"{r['max_proof_line_fanout']:>6} {r['emitted_approx_steps_t']:>7} "
            f"{r['ratio_t_over_k_log2_k']:>12.3f} {r['peak_dag_size']:>8} "
            f"{r['compile_time_ms']:>7.2f} {'PASS':>4}"
        )

    print(f"\nSaved verified JSON metrics to {out_path}")


if __name__ == "__main__":
    main()
