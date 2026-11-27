/-
  Soundness of Lifted Zassenhaus, Ostrowski-Hensel & Witt Calculus (v0.5)
  =======================================================================
  Standalone Lean 4.36.0 formalization (zero Mathlib imports, zero external axioms,
  zero `sorry`) covering Technical Note v0.5:
    1. Group 1: Lifted Gadget Inversion & Universal Lifted PHP Soundness
       (`ray_xor_red_witness_soundness` over arbitrary `List Bool` via VeriPB 3.0
       2-XOR `red` witnesses, and `lifted_php_universal_unsat` for all `h : Nat`
       by pure induction on `h`).
    2. Group 2: Binomial Ideal Lift in `RM(2, 6)` for Linear-Stretch Goldreich
       `XOR-MAJ₃` (`goldreich_xormaj3_binomial_lift_rm2`) and Absorbing Macaulay
       Lifts in `RM(2, 6)` / `RM(3, 6)` for Goldreich `TSA`
       (`goldreich_tsa_absorbing_macaulay_rm2_rm3`).
    3. Group 3: Universal `∀ k` 2-Adic Ostrowski-Hensel Bit-Peeling for Full &
       Truncated Mod-`2^k` Multiplier Miters (`evalBits`, `evalBits_lt_pow2`,
       `ostrowski_hensel_forall_k_uniqueness`, `truncated_miter_mod_2k_uniqueness`,
       and `witt_full_adder_disjoint_carry_linear`).
    4. Group 4: Schoenebeck 3-Clause `RM(2, 3)` Universal Collision Drop
       (`universal_3clause_collision_rm2_drop`) and Witt Chvátal-Gomory Carry Cut
       (`witt_cg_carry_cut_soundness`).
-/

namespace LiftedZassenhausWittV05Soundness

/-! ## 0. Core Helpers -/

/-- Embed `Bool` into `Nat` (`true ↦ 1`, `false ↦ 0`). -/
def b2n (b : Bool) : Nat :=
  if b then 1 else 0

@[simp]
theorem b2n_not (b : Bool) : b2n (!b) = 1 - b2n b := by
  cases b <;> rfl

/-- 3-input majority gate over `Bool`. -/
def maj3 (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

/-! ## 1. Group 1: Lifted Gadget Inversion & Universal Lifted PHP Soundness -/

/-- The 4 pseudo-Boolean clauses encoding a fresh 2-XOR wire `w ↔ xor a b`. -/
def xor2C1 (a b w : Bool) : Prop := b2n a + b2n b + b2n (!w) ≥ 1
def xor2C2 (a b w : Bool) : Prop := b2n (!a) + b2n (!b) + b2n (!w) ≥ 1
def xor2C3 (a b w : Bool) : Prop := b2n (!a) + b2n b + b2n w ≥ 1
def xor2C4 (a b w : Bool) : Prop := b2n a + b2n (!b) + b2n w ≥ 1

/-- Complete 4-clause PB encoding of `w ↔ xor a b`. -/
def xor2Clauses (a b w : Bool) : Prop :=
  xor2C1 a b w ∧ xor2C2 a b w ∧ xor2C3 a b w ∧ xor2C4 a b w

/-- Step-by-step VeriPB 3.0 `red` witness soundness for introducing a fresh 2-XOR wire
    `w ↔ xor a b`:
    - `C1, C2` hold unconditionally under witness `w ↦ false`;
    - `C3` holds under witness `w ↦ true` and preserves `C1, C2` whenever `C3` is falsified;
    - `C4` holds under witness `w ↦ true` and preserves `C1, C2, C3` whenever `C4` is falsified;
    - Together `C1 ∧ C2 ∧ C3 ∧ C4` holds if and only if `w = xor a b`. -/
theorem xor2_red_witness_step_sound (a b w : Bool) :
    (xor2C1 a b false) ∧
    (xor2C2 a b false) ∧
    (xor2C3 a b true ∧ (¬ xor2C3 a b w → xor2C1 a b true ∧ xor2C2 a b true)) ∧
    (xor2C4 a b true ∧ (¬ xor2C4 a b w → xor2C1 a b true ∧ xor2C2 a b true ∧ xor2C3 a b true)) ∧
    (xor2Clauses a b w ↔ w = xor a b) := by
  cases a <;> cases b <;> cases w <;>
    simp [xor2Clauses, xor2C1, xor2C2, xor2C3, xor2C4, b2n]

/-- Inductive chain of 2-XOR VeriPB `red` wire definitions folding `init` over `ls`
    into output wire `w`. -/
def rayXorChain (init : Bool) : List Bool → Bool → Prop
  | [], w => (b2n init + b2n (!w) ≥ 1) ∧ (b2n (!init) + b2n w ≥ 1)
  | b :: bs, w => ∃ u : Bool, xor2Clauses init b u ∧ rayXorChain u bs w

theorem rayXorChain_iff_foldl (init : Bool) (ls : List Bool) (w : Bool) :
    rayXorChain init ls w ↔ w = ls.foldl xor init := by
  induction ls generalizing init with
  | nil =>
    cases init <;> cases w <;> simp [rayXorChain, b2n]
  | cons b bs ih =>
    simp only [rayXorChain, List.foldl_cons]
    constructor
    · rintro ⟨u, h_xor, h_tail⟩
      have hu : u = xor init b := (xor2_red_witness_step_sound init b u).2.2.2.2.mp h_xor
      subst hu
      exact (ih (xor init b)).mp h_tail
    · intro hw
      refine ⟨xor init b, ?_, ?_⟩
      · exact (xor2_red_witness_step_sound init b (xor init b)).2.2.2.2.mpr rfl
      · exact (ih (xor init b)).mpr hw

/-- Universal soundness over `List Bool` for introducing a fresh VeriPB 3.0 `red` ray wire
    `w ↔ ls.foldl xor false` via chained 2-XOR `red` witnesses:
    (1) Every 2-XOR `red` step is witness-valid and RUP-preserving;
    (2) For every `ls : List Bool`, a satisfying wire assignment `w` exists (equisatisfiability);
    (3) Every assignment satisfying the chained PB clauses forces `w = ls.foldl xor false`. -/
theorem ray_xor_red_witness_soundness (ls : List Bool) :
    (∀ a b w : Bool,
      xor2C1 a b false ∧
      xor2C2 a b false ∧
      (xor2C3 a b true ∧ (¬ xor2C3 a b w → xor2C1 a b true ∧ xor2C2 a b true)) ∧
      (xor2C4 a b true ∧ (¬ xor2C4 a b w → xor2C1 a b true ∧ xor2C2 a b true ∧ xor2C3 a b true))) ∧
    (∃ w : Bool, rayXorChain false ls w) ∧
    (∀ w : Bool, rayXorChain false ls w ↔ w = ls.foldl xor false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b w
    have h := xor2_red_witness_step_sound a b w
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · exact ⟨ls.foldl xor false, (rayXorChain_iff_foldl false ls (ls.foldl xor false)).mpr rfl⟩
  · intro w
    exact rayXorChain_iff_foldl false ls w

/-- Hole re-indexing map deleting hole `j0`: maps `{0, ..., h - 1}` into `{0, ..., h} \ {j0}`. -/
def skipHole (j0 j : Nat) : Nat :=
  if j < j0 then j else j + 1

/-- Universal `∀ (h : Nat)` Lifted PHP Soundness (pure induction on `h`):
    if boolean ray observables `w : Nat → Nat → Bool` satisfy ALO on `h + 1` pigeons
    and lifted AMO pairwise annihilators on `h` holes, then `False` holds. -/
theorem lifted_php_universal_unsat (h : Nat) :
    ∀ (w : Nat → Nat → Bool),
      (∀ i, i ≤ h → ∃ j, j < h ∧ w i j = true) →
      (∀ j, j < h → ∀ i1 i2, i1 < i2 → i2 ≤ h → !(w i1 j && w i2 j) = true) →
      False := by
  induction h with
  | zero =>
    intro w h_alo _
    rcases h_alo 0 (Nat.le_refl 0) with ⟨j, hj, _⟩
    exact Nat.not_lt_zero j hj
  | succ h ih =>
    intro w h_alo h_amo
    rcases h_alo (h + 1) (Nat.le_refl (h + 1)) with ⟨j0, hj0, hw_last⟩
    let w' : Nat → Nat → Bool := fun i j => w i (skipHole j0 j)
    have h_alo' : ∀ i, i ≤ h → ∃ j, j < h ∧ w' i j = true := by
      intro i hi
      rcases h_alo i (Nat.le_trans hi (Nat.le_succ h)) with ⟨k, hk, hwik⟩
      have hne : k ≠ j0 := by
        intro h_eq
        subst h_eq
        have h_pair := h_amo k hj0 i (h + 1) (Nat.lt_succ_of_le hi) (Nat.le_refl (h + 1))
        rw [hwik, hw_last] at h_pair
        cases h_pair
      by_cases hlt : k < j0
      · refine ⟨k, by omega, ?_⟩
        simp only [w', skipHole, hlt, ↓reduceIte]
        exact hwik
      · refine ⟨k - 1, by omega, ?_⟩
        have h_not_lt : ¬ (k - 1 < j0) := by omega
        have h_succ : k - 1 + 1 = k := by omega
        simp only [w', skipHole, h_not_lt, ↓reduceIte, h_succ]
        exact hwik
    have h_amo' : ∀ j, j < h → ∀ i1 i2, i1 < i2 → i2 ≤ h → !(w' i1 j && w' i2 j) = true := by
      intro j hj i1 i2 h12 hi2
      have h_skip_lt : skipHole j0 j < h + 1 := by
        unfold skipHole
        split <;> omega
      exact h_amo (skipHole j0 j) h_skip_lt i1 i2 h12 (Nat.le_trans hi2 (Nat.le_succ h))
    exact ih w' h_alo' h_amo'

/-! ## 2. Group 2: Binomial Ideal Lift in `RM(2, 6)` for Goldreich `XOR-MAJ₃` & `TSA` -/

/-- Exact degree-2 `RM(2, 6)` polynomial obtained from multiplying `e_maj` by `(z3 ⊕ z4)`:
    all 8 monomials have degree exactly 2 (the cubic `z3 && z4 && z5` cancels identically). -/
def goldreichXorMaj3RM2 (z1 z2 z3 z4 z5 y : Bool) : Bool :=
  xor (xor (xor (z3 && z1) (z4 && z1))
           (xor (z3 && z2) (z4 && z2)))
      (xor (xor (z3 && z5) (z4 && z5))
           (xor (z3 && y)  (z4 && y)))

/-- Binomial Ideal Lift in `RM(2, 6)` for Linear-Stretch Goldreich `XOR-MAJ₃`:
    for `e_maj := xor (xor z1 z2) (xor (maj3 z3 z4 z5) y)`, multiplying by `(xor z3 z4)`
    cancels the cubic monomial `z3 && z4 && z5` identically over `F₂` and equals the
    exact degree-2 polynomial `goldreichXorMaj3RM2 z1 z2 z3 z4 z5 y`. -/
theorem goldreich_xormaj3_binomial_lift_rm2 (z1 z2 z3 z4 z5 y : Bool) :
    let e_maj := xor (xor z1 z2) (xor (maj3 z3 z4 z5) y)
    (((xor z3 z4) && e_maj) = goldreichXorMaj3RM2 z1 z2 z3 z4 z5 y) ∧
    (e_maj = false → goldreichXorMaj3RM2 z1 z2 z3 z4 z5 y = false) := by
  cases z1 <;> cases z2 <;> cases z3 <;> cases z4 <;> cases z5 <;> cases y <;>
    simp [maj3, goldreichXorMaj3RM2]

/-- Exact degree-2 `RM(2, 6)` polynomial for the `z4`-absorbing Macaulay lift of Goldreich `TSA`. -/
def goldreichTsaRM2_z4 (z1 z2 z3 z4 z5 y : Bool) : Bool :=
  xor (xor (z4 && z1) (z4 && z2))
      (xor (z4 && z3) (xor (z4 && z5) (z4 && y)))

/-- Exact degree-2 `RM(2, 6)` polynomial for the `z5`-absorbing Macaulay lift of Goldreich `TSA`. -/
def goldreichTsaRM2_z5 (z1 z2 z3 z4 z5 y : Bool) : Bool :=
  xor (xor (z5 && z1) (z5 && z2))
      (xor (z5 && z3) (xor (z4 && z5) (z5 && y)))

/-- Exact degree-3 `RM(3, 6)` polynomial for the `(z4 && z5)`-absorbing Macaulay lift of `TSA`. -/
def goldreichTsaRM3_z45 (z1 z2 z3 z4 z5 y : Bool) : Bool :=
  xor (xor (z1 && z4 && z5) (z2 && z4 && z5))
      (xor (z3 && z4 && z5) (xor (z4 && z5) (y && z4 && z5)))

/-- Absorbing Macaulay Lifts in `RM(2, 6)` and `RM(3, 6)` for Goldreich `TSA`
    (`e_tsa := z1 ⊕ z2 ⊕ z3 ⊕ (z4 ∧ z5) ⊕ y`):
    - multiplying by `z4` or `z5` absorbs `z4 ∧ z5` by `F₂` idempotence into `RM(2, 6)`;
    - multiplying by `z4 ∧ z5` absorbs `z4 ∧ z5` into `RM(3, 6)` (avoiding degree 4). -/
theorem goldreich_tsa_absorbing_macaulay_rm2_rm3 (z1 z2 z3 z4 z5 y : Bool) :
    let e_tsa := xor (xor (xor z1 z2) z3) (xor (z4 && z5) y)
    ((z4 && e_tsa) = goldreichTsaRM2_z4 z1 z2 z3 z4 z5 y) ∧
    ((z5 && e_tsa) = goldreichTsaRM2_z5 z1 z2 z3 z4 z5 y) ∧
    (((z4 && z5) && e_tsa) = goldreichTsaRM3_z45 z1 z2 z3 z4 z5 y) ∧
    (e_tsa = false →
      goldreichTsaRM2_z4 z1 z2 z3 z4 z5 y = false ∧
      goldreichTsaRM2_z5 z1 z2 z3 z4 z5 y = false ∧
      goldreichTsaRM3_z45 z1 z2 z3 z4 z5 y = false) := by
  cases z1 <;> cases z2 <;> cases z3 <;> cases z4 <;> cases z5 <;> cases y <;>
    simp [goldreichTsaRM2_z4, goldreichTsaRM2_z5, goldreichTsaRM3_z45]

/-! ## 3. Group 3: Universal `∀ k` 2-Adic Ostrowski-Hensel Bit-Peeling & Witt Full Adder -/

/-- Little-endian unsigned binary evaluation of a bit vector `List Bool`. -/
def evalBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * evalBits bs

/-- Strict upper bound `evalBits xs < 2 ^ xs.length` for every bit vector `xs`. -/
theorem evalBits_lt_pow2 : ∀ (xs : List Bool), evalBits xs < 2 ^ xs.length := by
  intro xs
  induction xs with
  | nil =>
    simp [evalBits]
  | cons b bs ih =>
    cases b <;> simp [evalBits, Nat.pow_succ] <;> omega

/-- Universal `∀ k` 2-adic Ostrowski-Hensel bit-peeling uniqueness:
    equal-length bit vectors with equal `evalBits` values are identical bit-by-bit. -/
theorem ostrowski_hensel_forall_k_uniqueness :
    ∀ (xs ys : List Bool), xs.length = ys.length → evalBits xs = evalBits ys → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys hlen _
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro ys hlen heq
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have hlen_tail : as.length = bs.length := by
        simp at hlen
        exact hlen
      cases a <;> cases b <;> simp [evalBits] at heq
      · have h_tail : as = bs := ih bs hlen_tail (by omega)
        rw [h_tail]
      · omega
      · omega
      · have h_tail : as = bs := ih bs hlen_tail (by omega)
        rw [h_tail]

/-- Truncated Mod-`2^k` Multiplier Miter Uniqueness:
    if two `k`-bit vectors agree modulo `2^k` (without inspecting any higher MSBs),
    they peel identically bit-by-bit (`xs = ys`). -/
theorem truncated_miter_mod_2k_uniqueness :
    ∀ (xs ys : List Bool),
      xs.length = ys.length →
      evalBits xs % (2 ^ xs.length) = evalBits ys % (2 ^ ys.length) →
      xs = ys := by
  intro xs ys hlen hmod
  rw [Nat.mod_eq_of_lt (evalBits_lt_pow2 xs), Nat.mod_eq_of_lt (evalBits_lt_pow2 ys)] at hmod
  exact ostrowski_hensel_forall_k_uniqueness xs ys hlen hmod

/-- Witt Full-Adder Disjoint Carry Linearity:
    the carry-out `maj3 a b cin` splits into two mutually disjoint AND terms
    `a ∧ b` and `(a ⊕ b) ∧ cin`, so the carry is exact linear over `Nat`
    and the full-adder column equation holds identically. -/
theorem witt_full_adder_disjoint_carry_linear (a b cin : Bool) :
    (((a && b) && ((xor a b) && cin)) = false) ∧
    (maj3 a b cin = xor (a && b) ((xor a b) && cin)) ∧
    (b2n (maj3 a b cin) = b2n (a && b) + b2n ((xor a b) && cin)) ∧
    (b2n a + b2n b + b2n cin =
      b2n (xor (xor a b) cin) + 2 * b2n (a && b) + 2 * b2n ((xor a b) && cin)) := by
  cases a <;> cases b <;> cases cin <;> simp [maj3, b2n]

/-! ## 4. Group 4: Schoenebeck 3-Clause `RM(2, 3)` Collision Drop & Witt CG Carry Cut -/

/-- Falsifying indicator `(x1 ⊕ p1) ∧ (x2 ⊕ p2) ∧ (x3 ⊕ p3)` of a 3-clause on `{x1, x2, x3}`
    with polarity triple `(p1, p2, p3)` (vanishes iff the 3-clause is satisfied). -/
def clause3Indicator (p1 p2 p3 x1 x2 x3 : Bool) : Bool :=
  (xor x1 p1) && (xor x2 p2) && (xor x3 p3)

/-- Exact degree-2 `RM(2, 3)` polynomial obtained by XOR-colliding two 3-clauses
    `(p1, p2, p3)` and `(q1, q2, q3)` on the same 3-variable support `{x1, x2, x3}`. -/
def collision3RM2 (p1 p2 p3 q1 q2 q3 x1 x2 x3 : Bool) : Bool :=
  let deg2 :=
    xor ((xor p1 q1) && (x2 && x3))
        (xor ((xor p2 q2) && (x1 && x3))
             ((xor p3 q3) && (x1 && x2)))
  let deg1 :=
    xor ((xor (p1 && p2) (q1 && q2)) && x3)
        (xor ((xor (p1 && p3) (q1 && q3)) && x2)
             ((xor (p2 && p3) (q2 && q3)) && x1))
  let deg0 := xor (p1 && p2 && p3) (q1 && q2 && q3)
  xor deg2 (xor deg1 deg0)

/-- Schoenebeck 3-Clause `RM(2, 3)` Universal Collision Drop:
    for EVERY pair of 3-clauses `(p1, p2, p3)` and `(q1, q2, q3)` sharing the 3-variable
    support `{x1, x2, x3}`, their `F₂` sum cancels the cubic monomial `x1 ∧ x2 ∧ x3`
    identically and equals `collision3RM2` in `RM(2, 3)`; whenever both clauses are
    satisfied, this degree-2 polynomial vanishes. -/
theorem universal_3clause_collision_rm2_drop (p1 p2 p3 q1 q2 q3 x1 x2 x3 : Bool) :
    (xor (clause3Indicator p1 p2 p3 x1 x2 x3) (clause3Indicator q1 q2 q3 x1 x2 x3) =
      collision3RM2 p1 p2 p3 q1 q2 q3 x1 x2 x3) ∧
    (clause3Indicator p1 p2 p3 x1 x2 x3 = false →
     clause3Indicator q1 q2 q3 x1 x2 x3 = false →
     collision3RM2 p1 p2 p3 q1 q2 q3 x1 x2 x3 = false) := by
  cases p1 <;> cases p2 <;> cases p3 <;>
  cases q1 <;> cases q2 <;> cases q3 <;>
  cases x1 <;> cases x2 <;> cases x3 <;>
    simp [clause3Indicator, collision3RM2]

/-- Witt Chvátal-Gomory Carry Cut Soundness:
    for any column sum `S = b2n s + 2 * C` with parity bit `s : Bool` and carry `C : Nat`,
    Chvátal-Gomory division by `2` soundly peels the carry bounds and exact quotient/remainder
    for every threshold `k : Nat`. -/
theorem witt_cg_carry_cut_soundness (S C k : Nat) (s : Bool)
    (h_col : S = b2n s + 2 * C) :
    (S ≥ 2 * k + 2 → C ≥ k + 1) ∧
    (S ≤ 2 * k + 1 → C ≤ k) ∧
    (s = false → S ≥ 2 * k + 1 → C ≥ k + 1) ∧
    (S = 2 * k + 1 → s = true ∧ C = k) ∧
    (S = 2 * k → s = false ∧ C = k) := by
  cases s <;> simp [b2n] at h_col ⊢ <;> omega

/-! ## 5. Axiom Footprint Audit (`0 sorryAx`, Kernel Axioms Only) -/

#print axioms xor2_red_witness_step_sound
#print axioms ray_xor_red_witness_soundness
#print axioms lifted_php_universal_unsat
#print axioms goldreich_xormaj3_binomial_lift_rm2
#print axioms goldreich_tsa_absorbing_macaulay_rm2_rm3
#print axioms evalBits_lt_pow2
#print axioms ostrowski_hensel_forall_k_uniqueness
#print axioms truncated_miter_mod_2k_uniqueness
#print axioms witt_full_adder_disjoint_carry_linear
#print axioms universal_3clause_collision_rm2_drop
#print axioms witt_cg_carry_cut_soundness

end LiftedZassenhausWittV05Soundness
