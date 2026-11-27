/-
  Soundness of Tetrahedral RM(3, 4) Collisions & Witt 2-Pair Triangle CG Cuts (ATAQUE-11)
  ======================================================================================
  Standalone Lean 4.36.0 formalization (zero imports, zero external axioms, zero `sorry`):
    1. `universal_4clause_collision_rm3_drop`:
       For any two 4-clauses `(a1,a2,a3,a4)` and `(b1,b2,b3,b4)` sharing the 4-variable
       support `{x1,x2,x3,x4}`, the degree-4 monomial `x1 && x2 && x3 && x4` appears with
       coefficient `1` in both falsifying indicators and cancels identically modulo `2`,
       yielding an exact degree-3 polynomial `collision4RM3` in `RM(3, 4)` that vanishes
       whenever both 4-clauses are satisfied.
    2. `tetrahedral_3clause_resolvent_rm3_soundness`:
       Resolving two 3-clauses `(w ∨ l1 ∨ l2)` and `(¬w ∨ l3 ∨ l4)` yields the 4-clause
       `(l1 ∨ l2 ∨ l3 ∨ l4)`, and colliding two 4-clauses on `{x1,x2,x3,x4}` drops into
       `RM(3, 4)` without degree-4 monomials.
    3. `witt_2pair_triangle_cg_cut`:
       On any triangle `{x1, x2, x3}` with pair witnesses `p12 = x1 && x2`,
       `p13 = x1 && x3`, `p23 = x2 && x3`, whenever `¬x1 ∨ ¬x2 ∨ ¬x3` holds,
       `b2n x1 + b2n x2 + b2n x3 ≤ 1 + b2n p12 + b2n p13 + b2n p23` (equivalently
       `x1 + x2 + x3 - p12 - p13 - p23 ≤ 1` in `Int`/`Nat` arithmetic).
-/

namespace TetrahedralRM3CollisionSoundness

/-- Embed `Bool` into `Nat` (`true ↦ 1`, `false ↦ 0`). -/
def b2n (b : Bool) : Nat :=
  if b then 1 else 0

@[simp]
theorem b2n_not (b : Bool) : b2n (!b) = 1 - b2n b := by
  cases b <;> rfl

/-- Falsifying indicator `(x1 ⊕ p1) ∧ (x2 ⊕ p2) ∧ (x3 ⊕ p3) ∧ (x4 ⊕ p4)` of a 4-clause
    on `{x1, x2, x3, x4}` with polarity tuple `(p1, p2, p3, p4)`
    (equals `false` iff the 4-clause is satisfied). -/
def clause4Indicator (p1 p2 p3 p4 x1 x2 x3 x4 : Bool) : Bool :=
  (xor x1 p1) && (xor x2 p2) && (xor x3 p3) && (xor x4 p4)

/-- Exact degree-≤3 part of `clause4Indicator p1 p2 p3 p4 x1 x2 x3 x4` in `RM(3, 4)`. -/
def clause4RM3Tail (p1 p2 p3 p4 x1 x2 x3 x4 : Bool) : Bool :=
  let deg3 :=
    xor (p1 && (x2 && x3 && x4))
      (xor (p2 && (x1 && x3 && x4))
        (xor (p3 && (x1 && x2 && x4))
             (p4 && (x1 && x2 && x3))))
  let deg2 :=
    xor ((p1 && p2) && (x3 && x4))
      (xor ((p1 && p3) && (x2 && x4))
        (xor ((p1 && p4) && (x2 && x3))
          (xor ((p2 && p3) && (x1 && x4))
            (xor ((p2 && p4) && (x1 && x3))
                 ((p3 && p4) && (x1 && x2))))))
  let deg1 :=
    xor ((p1 && p2 && p3) && x4)
      (xor ((p1 && p2 && p4) && x3)
        (xor ((p1 && p3 && p4) && x2)
             ((p2 && p3 && p4) && x1)))
  let deg0 := p1 && p2 && p3 && p4
  xor deg3 (xor deg2 (xor deg1 deg0))

/-- Every 4-clause indicator decomposes over `F₂` into the unique degree-4 monomial
    `x1 && x2 && x3 && x4` (with coefficient `1`) plus `clause4RM3Tail` in `RM(3, 4)`. -/
theorem clause4Indicator_eq_deg4_xor_rm3 (p1 p2 p3 p4 x1 x2 x3 x4 : Bool) :
    clause4Indicator p1 p2 p3 p4 x1 x2 x3 x4 =
      xor (x1 && x2 && x3 && x4) (clause4RM3Tail p1 p2 p3 p4 x1 x2 x3 x4) := by
  cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;>
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;>
    rfl

/-- Exact degree-≤3 `RM(3, 4)` polynomial obtained by XOR-colliding two 4-clauses
    `(a1,a2,a3,a4)` and `(b1,b2,b3,b4)` on `{x1, x2, x3, x4}`. -/
def collision4RM3 (a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 : Bool) : Bool :=
  xor (clause4RM3Tail a1 a2 a3 a4 x1 x2 x3 x4)
      (clause4RM3Tail b1 b2 b3 b4 x1 x2 x3 x4)

private theorem xor_cancel_left (m a b : Bool) :
    xor (xor m a) (xor m b) = xor a b := by
  cases m <;> cases a <;> cases b <;> rfl

/-- Universal 4-Clause `RM(3, 4)` Collision Drop:
    for ANY two 4-clauses `(a1,a2,a3,a4)` and `(b1,b2,b3,b4)` sharing `{x1,x2,x3,x4}`,
    the degree-4 monomial `x1 && x2 && x3 && x4` cancels identically modulo `2`,
    yielding `collision4RM3` in `RM(3, 4)` which vanishes whenever both 4-clauses
    are satisfied. -/
theorem universal_4clause_collision_rm3_drop
    (a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 : Bool) :
    (xor (clause4Indicator a1 a2 a3 a4 x1 x2 x3 x4)
         (clause4Indicator b1 b2 b3 b4 x1 x2 x3 x4) =
      collision4RM3 a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4) ∧
    (clause4Indicator a1 a2 a3 a4 x1 x2 x3 x4 = false →
     clause4Indicator b1 b2 b3 b4 x1 x2 x3 x4 = false →
     collision4RM3 a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 = false) := by
  have h_eq :
      xor (clause4Indicator a1 a2 a3 a4 x1 x2 x3 x4)
          (clause4Indicator b1 b2 b3 b4 x1 x2 x3 x4) =
        collision4RM3 a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 := by
    rw [clause4Indicator_eq_deg4_xor_rm3 a1 a2 a3 a4 x1 x2 x3 x4,
        clause4Indicator_eq_deg4_xor_rm3 b1 b2 b3 b4 x1 x2 x3 x4]
    exact xor_cancel_left (x1 && x2 && x3 && x4)
      (clause4RM3Tail a1 a2 a3 a4 x1 x2 x3 x4)
      (clause4RM3Tail b1 b2 b3 b4 x1 x2 x3 x4)
  refine ⟨h_eq, ?_⟩
  intro ha hb
  rw [← h_eq, ha, hb]
  rfl

/-- Resolution soundness on 3-clauses `(w ∨ l1 ∨ l2)` and `(¬w ∨ l3 ∨ l4)` yielding
    the 4-clause `(l1 ∨ l2 ∨ l3 ∨ l4)`, combined with `RM(3, 4)` collision drop
    when two 4-clauses share `{x1, x2, x3, x4}`. -/
theorem tetrahedral_3clause_resolvent_rm3_soundness
    (w l1 l2 l3 l4 : Bool)
    (a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 : Bool) :
    ((w || l1 || l2) = true →
     (!w || l3 || l4) = true →
     (l1 || l2 || l3 || l4) = true) ∧
    (clause4Indicator a1 a2 a3 a4 x1 x2 x3 x4 = false →
     clause4Indicator b1 b2 b3 b4 x1 x2 x3 x4 = false →
     collision4RM3 a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4 = false) := by
  refine ⟨?_, (universal_4clause_collision_rm3_drop a1 a2 a3 a4 b1 b2 b3 b4 x1 x2 x3 x4).2⟩
  cases w <;> cases l1 <;> cases l2 <;> cases l3 <;> cases l4 <;> simp

/-- Witt 2-Pair Triangle Chvátal-Gomory Cut:
    on any triangle `{x1, x2, x3}` with pair witnesses `p12 = x1 && x2`,
    `p13 = x1 && x3`, `p23 = x2 && x3`, whenever `¬x1 ∨ ¬x2 ∨ ¬x3` holds,
    `x1 + x2 + x3 - p12 - p13 - p23 ≤ 1` in `b2n` arithmetic. -/
theorem witt_2pair_triangle_cg_cut
    (x1 x2 x3 p12 p13 p23 : Bool)
    (hp12 : p12 = (x1 && x2))
    (hp13 : p13 = (x1 && x3))
    (hp23 : p23 = (x2 && x3))
    (h_tri : (!x1 || !x2 || !x3) = true) :
    b2n x1 + b2n x2 + b2n x3 ≤ 1 + b2n p12 + b2n p13 + b2n p23 := by
  subst hp12 hp13 hp23
  cases x1 <;> cases x2 <;> cases x3 <;> simp [b2n] at h_tri ⊢

/-! ## Axiom Footprint Audit (`0 sorryAx`, Kernel Axioms Only) -/

#print axioms clause4Indicator_eq_deg4_xor_rm3
#print axioms universal_4clause_collision_rm3_drop
#print axioms tetrahedral_3clause_resolvent_rm3_soundness
#print axioms witt_2pair_triangle_cg_cut

end TetrahedralRM3CollisionSoundness
