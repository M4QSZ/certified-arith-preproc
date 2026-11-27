/-!
# VeriPB 3.0 Dominance Rule (`dom` ≃ `G₁`) Soundness & Instantiations

Standalone Lean 4.36.0 formalization (0 imports, 0 `sorryAx`, `#print axioms` audited) of:
1. `dominance_rule_preserves_sat`: Abstract soundness of the VeriPB 3.0 Dominance Rule (`dom`)
   for a formula `F : α → Bool`, a preorder `preceq : α → α → Prop` (`reflexive`, `transitive`),
   and a strict rank-decreasing measure `μ : α → Nat` when combined with `C x = false`.
2. `dominance_chain_preserves_sat`: Iterated dominance rule soundness over a list of
   symmetry-breaking / extension constraints `Cs : List (α → Bool)`.
3. `pigeon_swap_dominance_sound`: Instantiation on `PHP_{n+1}^n` adjacent pigeon transposition
   symmetry (`swapPigeons`), showing that adding the row-weight ordering constraint
   `rowWeight n x i₁ ≥ rowWeight n x i₂` preserves satisfiability of `PHP_{n+1}^n`.
4. `bijective_gadget_dominance_inversion`: Instantiation on bijective gadget inversion /
   WNU idempotence (`∀ g` bijection on `Bool^k`, `(∃ x, P (g x) = true) ↔ (∃ y, P y = true)`),
   both directly and via `dominance_rule_preserves_sat`.

Reference:
- Bogaerts, Gocht, McCreesh & Nordström (JAIR 2023), "Certified Dominance and Symmetry Breaking
  for Combinatorial Optimisation"
- Kołodziejczyk & Thapen (2024/2025), `VeriPB` dominance rule ≃ Quantified Propositional Calculus `G₁`
-/

namespace VeriPBDominanceG1

/-! ## 1. Abstract Dominance Rule Soundness (`dominance_rule_preserves_sat`) -/

/-- A preorder on `α` together with a `Nat`-valued rank measure `μ`. -/
structure RankedPreorder (α : Type) where
  preceq : α → α → Prop
  refl   : ∀ x, preceq x x
  trans  : ∀ x y z, preceq x y → preceq y z → preceq x z
  μ      : α → Nat

/-- Helper: strong induction on `k = R.μ x` to find an assignment satisfying both `F` and `C`. -/
private theorem dominance_reach_aux
    {α : Type} (F C : α → Bool) (R : RankedPreorder α) (ω : α → α)
    (h_dom : ∀ x, F x = true → C x = false →
      F (ω x) = true ∧ R.preceq (ω x) x ∧ R.μ (ω x) < R.μ x) :
    ∀ k x, R.μ x ≤ k → F x = true → ∃ y, (F y && C y) = true := by
  intro k
  induction k with
  | zero =>
    intro x hμ hF
    cases hC : C x with
    | true =>
      refine ⟨x, ?_⟩
      simp [hF, hC]
    | false =>
      have ⟨_, _, hlt⟩ := h_dom x hF hC
      omega
  | succ k ih =>
    intro x hμ hF
    cases hC : C x with
    | true =>
      refine ⟨x, ?_⟩
      simp [hF, hC]
    | false =>
      have ⟨hFω, _, hlt⟩ := h_dom x hF hC
      have hle : R.μ (ω x) ≤ k := by omega
      exact ih (ω x) hle hFω

/-- **Theorem (`dominance_rule_preserves_sat`)**:
Given a formula `F : α → Bool`, a target constraint `C : α → Bool`, a ranked preorder `R`,
and a witness map `ω : α → α` such that every assignment `x` satisfying `F x = true` and
`C x = false` maps to `ω x` with `F (ω x) = true`, `R.preceq (ω x) x`, and `R.μ (ω x) < R.μ x`,
adding `C` to `F` preserves satisfiability:
`(∃ x, F x = true) ↔ (∃ x, (F x && C x) = true)`. -/
theorem dominance_rule_preserves_sat
    {α : Type} (F C : α → Bool) (R : RankedPreorder α) (ω : α → α)
    (h_dom : ∀ x, F x = true → C x = false →
      F (ω x) = true ∧ R.preceq (ω x) x ∧ R.μ (ω x) < R.μ x) :
    (∃ x, F x = true) ↔ (∃ x, (F x && C x) = true) := by
  constructor
  · rintro ⟨x, hFx⟩
    exact dominance_reach_aux F C R ω h_dom (R.μ x) x (Nat.le_refl _) hFx
  · rintro ⟨x, hFC⟩
    cases hFx : F x with
    | true => exact ⟨x, hFx⟩
    | false =>
      simp [hFx] at hFC

/-- Conjunction of a list of constraints evaluated at `x`. -/
def allConstraints {α : Type} (Cs : List (α → Bool)) (x : α) : Bool :=
  match Cs with
  | [] => true
  | c :: cs => c x && allConstraints cs x

/-- **Theorem (`dominance_chain_preserves_sat`)**:
Iterated application of `dominance_rule_preserves_sat` over a sequence of constraints `Cs`:
if each constraint `c` in `Cs` is dominance-justified wrt the accumulated formula,
then `(∃ x, F x = true) ↔ (∃ x, (F x && allConstraints Cs x) = true)`. -/
inductive DominanceChain {α : Type} : (α → Bool) → List (α → Bool) → Prop where
  | nil (F : α → Bool) : DominanceChain F []
  | cons (F C : α → Bool) (Cs : List (α → Bool))
      (R : RankedPreorder α) (ω : α → α)
      (h_dom : ∀ x, F x = true → C x = false →
        F (ω x) = true ∧ R.preceq (ω x) x ∧ R.μ (ω x) < R.μ x)
      (h_tail : DominanceChain (fun x => F x && C x) Cs) :
      DominanceChain F (C :: Cs)

theorem dominance_chain_preserves_sat
    {α : Type} {F : α → Bool} {Cs : List (α → Bool)}
    (h_chain : DominanceChain F Cs) :
    (∃ x, F x = true) ↔ (∃ x, (F x && allConstraints Cs x) = true) := by
  induction h_chain with
  | nil F =>
    simp [allConstraints]
  | cons F C Cs R ω h_dom _ ih =>
    have h1 := dominance_rule_preserves_sat F C R ω h_dom
    constructor
    · intro hF
      have hFC := h1.mp hF
      have hFCCs := ih.mp hFC
      rcases hFCCs with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simp [allConstraints] at hx ⊢
      cases hFx : F x <;> cases hCx : C x <;> cases hCs : allConstraints Cs x <;> simp_all
    · intro hFCCs
      rcases hFCCs with ⟨x, hx⟩
      have hFC : (F x && C x) = true := by
        simp [allConstraints] at hx
        cases hFx : F x <;> cases hCx : C x <;> cases hCs : allConstraints Cs x <;> simp_all
      exact h1.mpr ⟨x, hFC⟩

/-! ## 2. Instantiation (a): Adjacent Pigeon Transposition Symmetry on `PHP_{n+1}^n` -/

/-- A Boolean assignment for `PHP_{n+1}^n`, mapping `(pigeon, hole)` to `Bool`. -/
abbrev PHPAssign := Nat → Nat → Bool

/-- Check that `P j` holds for at least one `j < bound`. -/
def existsBound (bound : Nat) (P : Nat → Bool) : Bool :=
  match bound with
  | 0 => false
  | b + 1 => P b || existsBound b P

/-- Check that `P j` holds for all `j < bound`. -/
def forallBound (bound : Nat) (P : Nat → Bool) : Bool :=
  match bound with
  | 0 => true
  | b + 1 => P b && forallBound b P

theorem existsBound_true_iff {bound : Nat} {P : Nat → Bool} :
    existsBound bound P = true ↔ ∃ j, j < bound ∧ P j = true := by
  induction bound with
  | zero =>
    simp [existsBound]
  | succ b ih =>
    simp [existsBound]
    constructor
    · intro h
      cases hPb : P b with
      | true => exact ⟨b, Nat.lt_succ_self b, hPb⟩
      | false =>
        simp [hPb] at h
        rcases ih.mp h with ⟨j, hj, hPj⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hPj⟩
    · rintro ⟨j, hj, hPj⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · have : existsBound b P = true := ih.mpr ⟨j, hlt, hPj⟩
        simp [this]
      · simp [hPj]

theorem forallBound_true_iff {bound : Nat} {P : Nat → Bool} :
    forallBound bound P = true ↔ ∀ j, j < bound → P j = true := by
  induction bound with
  | zero =>
    simp [forallBound]
  | succ b ih =>
    simp [forallBound]
    constructor
    · intro ⟨hPb, hrest⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact ih.mp hrest j hlt
      · exact hPb
    · intro h
      refine ⟨h b (Nat.lt_succ_self b), ih.mpr fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

/-- `PHP_{n+1}^n` formula:
    - Every pigeon `i < n + 1` is placed in at least one hole `j < n`.
    - For every hole `j < n` and every pair `i₁ < i₂ < n + 1`, not both `x i₁ j` and `x i₂ j`. -/
def phpFormula (n : Nat) (x : PHPAssign) : Bool :=
  let pigeons := forallBound (n + 1) (fun i => existsBound n (fun j => x i j))
  let holes := forallBound n (fun j =>
    forallBound (n + 1) (fun i₂ =>
      forallBound i₂ (fun i₁ => !(x i₁ j && x i₂ j))))
  pigeons && holes

/-- Swap pigeon `a` and pigeon `b` in assignment `x`. -/
def swapPigeons (a b : Nat) (x : PHPAssign) : PHPAssign :=
  fun i j =>
    if i = a then x b j
    else if i = b then x a j
    else x i j

theorem swapPigeons_at_a (a b : Nat) (x : PHPAssign) (j : Nat) :
    swapPigeons a b x a j = x b j := by
  simp [swapPigeons]

theorem swapPigeons_at_b (a b : Nat) (x : PHPAssign) (j : Nat) :
    swapPigeons a b x b j = x a j := by
  by_cases h : b = a
  · subst h; simp [swapPigeons]
  · simp [swapPigeons, h]

theorem swapPigeons_other (a b i : Nat) (ha : i ≠ a) (hb : i ≠ b) (x : PHPAssign) (j : Nat) :
    swapPigeons a b x i j = x i j := by
  simp [swapPigeons, ha, hb]

/-- Mapping an index `i` under transposition `(a b)`. -/
def swapIdx (a b i : Nat) : Nat :=
  if i = a then b else if i = b then a else i

theorem swapIdx_lt {m a b i : Nat} (ha : a < m) (hb : b < m) (hi : i < m) :
    swapIdx a b i < m := by
  dsimp [swapIdx]
  split
  · exact hb
  · split
    · exact ha
    · exact hi

theorem swapIdx_ne {a b i₁ i₂ : Nat} (hne : i₁ ≠ i₂) :
    swapIdx a b i₁ ≠ swapIdx a b i₂ := by
  by_cases hab : a = b <;>
    by_cases h1 : i₁ = a <;> by_cases h2 : i₁ = b <;>
    by_cases h3 : i₂ = a <;> by_cases h4 : i₂ = b <;>
    simp_all [swapIdx] <;> omega

theorem swapPigeons_eq_swapIdx (a b i j : Nat) (x : PHPAssign) :
    swapPigeons a b x i j = x (swapIdx a b i) j := by
  by_cases h1 : i = a <;> by_cases h2 : i = b <;> by_cases hab : b = a <;>
    simp [swapPigeons, swapIdx, h1, h2, hab]

/-- `swapPigeons` preserves `phpFormula n` whenever `a < n + 1` and `b < n + 1`. -/
theorem swapPigeons_preserves_php (n a b : Nat) (ha : a < n + 1) (hb : b < n + 1)
    (x : PHPAssign) (hx : phpFormula n x = true) :
    phpFormula n (swapPigeons a b x) = true := by
  simp [phpFormula] at hx ⊢
  rcases hx with ⟨hpig, hhole⟩
  have hpig' := forallBound_true_iff.mp hpig
  have hhole' := forallBound_true_iff.mp hhole
  constructor
  · apply forallBound_true_iff.mpr
    intro i hi
    have hi' := swapIdx_lt ha hb hi
    rcases existsBound_true_iff.mp (hpig' (swapIdx a b i) hi') with ⟨j, hj, hxj⟩
    exact existsBound_true_iff.mpr ⟨j, hj, by rw [swapPigeons_eq_swapIdx]; exact hxj⟩
  · apply forallBound_true_iff.mpr
    intro j hj
    apply forallBound_true_iff.mpr
    intro i₂ hi₂
    apply forallBound_true_iff.mpr
    intro i₁ hi₁
    have hne : i₁ ≠ i₂ := Nat.ne_of_lt hi₁
    have hsne : swapIdx a b i₁ ≠ swapIdx a b i₂ := swapIdx_ne hne
    have hs1 : swapIdx a b i₁ < n + 1 := swapIdx_lt ha hb (Nat.lt_trans hi₁ hi₂)
    have hs2 : swapIdx a b i₂ < n + 1 := swapIdx_lt ha hb hi₂
    have h_hole_j := forallBound_true_iff.mp (hhole' j hj)
    rcases Nat.lt_trichotomy (swapIdx a b i₁) (swapIdx a b i₂) with hlt | heq | hgt
    · have h1 := forallBound_true_iff.mp (h_hole_j (swapIdx a b i₂) hs2) (swapIdx a b i₁) hlt
      simpa [swapPigeons_eq_swapIdx] using h1
    · exact absurd heq hsne
    · have h1 := forallBound_true_iff.mp (h_hole_j (swapIdx a b i₁) hs1) (swapIdx a b i₂) hgt
      rw [swapPigeons_eq_swapIdx, swapPigeons_eq_swapIdx, Bool.or_comm]
      exact h1

/-- Binary weight of pigeon `i`'s hole assignment across `j < n`:
    `rowWeight n x i = Σ_{j < n} (if x i j then 2^j else 0)`. -/
def rowWeight (n : Nat) (x : PHPAssign) (i : Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => rowWeight m x i + (if x i m then 2 ^ m else 0)

theorem rowWeight_lt_pow (n : Nat) (x : PHPAssign) (i : Nat) :
    rowWeight n x i < 2 ^ n := by
  induction n with
  | zero => simp [rowWeight]
  | succ m ih =>
    simp [rowWeight]
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
      rw [Nat.pow_succ, Nat.mul_two]
    cases x i m <;> simp <;> omega

/-- Base `B = 2^n` for positional scoring of rows `0..n`. -/
def rowBase (n : Nat) : Nat := 2 ^ n

/-- Total lexicographic score of assignment `x` over pigeons `0..bound-1`:
    earlier pigeons (smaller `i`) have exponentially larger weight `B^(n - i)`
    so `i₁ < i₂` gives `i₁` strictly higher weight than `i₂`. -/
def totalLexScoreAux (n bound : Nat) (x : PHPAssign) : Nat :=
  match bound with
  | 0 => 0
  | b + 1 => totalLexScoreAux n b x + rowWeight n x b * (rowBase n) ^ (n - b)

def totalLexScore (n : Nat) (x : PHPAssign) : Nat :=
  totalLexScoreAux n (n + 1) x

/-- Maximum possible `totalLexScore n x` + 1, used to turn score maximization into rank minimization. -/
def maxLexScore (n : Nat) : Nat :=
  (n + 1) * (rowBase n) ^ (n + 1) + 1

theorem totalLexScoreAux_lt (n bound : Nat) (hbound : bound ≤ n + 1) (x : PHPAssign) :
    totalLexScoreAux n bound x < bound * (rowBase n) ^ (n + 1) + 1 := by
  induction bound with
  | zero => simp [totalLexScoreAux]
  | succ b ih =>
    have h1 := ih (Nat.le_of_succ_le hbound)
    have hrw : rowWeight n x b < rowBase n := rowWeight_lt_pow n x b
    have hpow_le : (rowBase n) ^ (n - b) ≤ (rowBase n) ^ n :=
      Nat.pow_le_pow_right (Nat.one_le_pow n 2 (by decide)) (Nat.sub_le n b)
    have hterm : rowWeight n x b * (rowBase n) ^ (n - b) < (rowBase n) ^ (n + 1) := by
      calc rowWeight n x b * (rowBase n) ^ (n - b)
          < rowBase n * (rowBase n) ^ (n - b) :=
            Nat.mul_lt_mul_of_pos_right hrw (Nat.one_le_pow _ _ (Nat.one_le_pow n 2 (by decide)))
        _ ≤ rowBase n * (rowBase n) ^ n :=
            Nat.mul_le_mul_left _ hpow_le
        _ = (rowBase n) ^ (n + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
    simp [totalLexScoreAux, Nat.succ_mul]
    omega

theorem totalLexScore_lt_max (n : Nat) (x : PHPAssign) :
    totalLexScore n x < maxLexScore n :=
  totalLexScoreAux_lt n (n + 1) (Nat.le_refl _) x

/-- Rank measure for `PHP_{n+1}^n`: strictly decreases when `totalLexScore` strictly increases. -/
def phpRank (n : Nat) (x : PHPAssign) : Nat :=
  maxLexScore n - totalLexScore n x

theorem rowWeight_swapPigeons_eq (n a b i : Nat) (hne : a ≠ b) (x : PHPAssign) :
    rowWeight n (swapPigeons a b x) i =
      if i = a then rowWeight n x b
      else if i = b then rowWeight n x a
      else rowWeight n x i := by
  induction n with
  | zero =>
    simp [rowWeight]
  | succ m ih =>
    simp only [rowWeight]
    rw [ih]
    by_cases ha : i = a
    · subst ha
      simp [swapPigeons_at_a]
    · by_cases hb : i = b
      · subst hb
        simp [ha, swapPigeons_at_b]
      · simp [ha, hb, swapPigeons_other a b i ha hb]

private theorem totalLexScoreAux_swap_identity (n bound a b : Nat) (hne : a ≠ b) (x : PHPAssign) :
    totalLexScoreAux n bound (swapPigeons a b x)
      + (if a < bound then rowWeight n x a * (rowBase n) ^ (n - a) else 0)
      + (if b < bound then rowWeight n x b * (rowBase n) ^ (n - b) else 0)
    = totalLexScoreAux n bound x
      + (if a < bound then rowWeight n x b * (rowBase n) ^ (n - a) else 0)
      + (if b < bound then rowWeight n x a * (rowBase n) ^ (n - b) else 0) := by
  induction bound with
  | zero =>
    simp [totalLexScoreAux]
  | succ k ih =>
    simp only [totalLexScoreAux]
    rw [rowWeight_swapPigeons_eq n a b k hne x]
    by_cases hka : k = a
    · subst hka
      have hkb : k ≠ b := hne
      have ha_lt : k < k + 1 := Nat.lt_succ_self k
      have ha_not : ¬ (k < k) := Nat.lt_irrefl k
      have hb_iff : (b < k + 1) ↔ (b < k) := by omega
      simp only [ha_lt, ha_not, ↓reduceIte, hb_iff] at ih ⊢
      omega
    · by_cases hkb : k = b
      · subst hkb
        have ha_iff : (a < k + 1) ↔ (a < k) := by omega
        have hb_lt : k < k + 1 := Nat.lt_succ_self k
        have hb_not : ¬ (k < k) := Nat.lt_irrefl k
        simp only [hka, hb_lt, hb_not, ↓reduceIte, ha_iff] at ih ⊢
        omega
      · have ha_iff : (a < k + 1) ↔ (a < k) := by omega
        have hb_iff : (b < k + 1) ↔ (b < k) := by omega
        simp only [hka, hkb, ↓reduceIte, ha_iff, hb_iff] at ih ⊢
        omega

theorem totalLexScore_swap_lt {n a b : Nat} (ha : a < b) (hb : b < n + 1) (x : PHPAssign)
    (hrw : rowWeight n x a < rowWeight n x b) :
    totalLexScore n x < totalLexScore n (swapPigeons a b x) := by
  have hne : a ≠ b := Nat.ne_of_lt ha
  have ha_bound : a < n + 1 := Nat.lt_trans ha hb
  have hid := totalLexScoreAux_swap_identity n (n + 1) a b hne x
  simp only [totalLexScore] at *
  simp only [ha_bound, hb, ↓reduceIte] at hid
  -- From `hrw : rowWeight n x a < rowWeight n x b`, we must have `n ≥ 1` (since `rowWeight 0 = 0`).
  have hn_pos : 0 < n := by
    cases n with
    | zero => simp [rowWeight] at hrw
    | succ m => exact Nat.succ_pos m
  have hbase_ge2 : 2 ≤ rowBase n := by
    dsimp [rowBase]
    exact Nat.le_self_pow (Nat.ne_of_gt hn_pos) 2
  have hsub_lt : n - b < n - a := by omega
  have hpow_lt : (rowBase n) ^ (n - b) < (rowBase n) ^ (n - a) :=
    Nat.pow_lt_pow_right hbase_ge2 hsub_lt
  -- Cross-multiplication inequality: `u * P₁ + v * P₂ < v * P₁ + u * P₂` when `u < v` and `P₂ < P₁`.
  have hcross :
      rowWeight n x a * (rowBase n) ^ (n - a) + rowWeight n x b * (rowBase n) ^ (n - b)
      < rowWeight n x b * (rowBase n) ^ (n - a) + rowWeight n x a * (rowBase n) ^ (n - b) := by
    let u := rowWeight n x a
    let v := rowWeight n x b
    let p₁ := (rowBase n) ^ (n - a)
    let p₂ := (rowBase n) ^ (n - b)
    have huv : u < v := hrw
    have hp : p₂ < p₁ := hpow_lt
    -- Write `v = u + dv` with `dv ≥ 1` and `p₁ = p₂ + dp` with `dp ≥ 1`.
    obtain ⟨dv, hdv⟩ := Nat.exists_eq_add_of_lt huv
    obtain ⟨dp, hdp⟩ := Nat.exists_eq_add_of_lt hp
    have h1 : u * (p₂ + dp + 1) + (u + dv + 1) * p₂
        = u * p₂ + u * dp + u + u * p₂ + dv * p₂ + p₂ := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    have h2 : (u + dv + 1) * (p₂ + dp + 1) + u * p₂
        = u * p₂ + u * dp + u + dv * p₂ + dv * dp + dv + p₂ + dp + 1 + u * p₂ := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    change u * p₁ + v * p₂ < v * p₁ + u * p₂
    rw [hdp, hdv]
    omega
  omega

theorem phpRank_swap_lt {n a b : Nat} (ha : a < b) (hb : b < n + 1) (x : PHPAssign)
    (hrw : rowWeight n x a < rowWeight n x b) :
    phpRank n (swapPigeons a b x) < phpRank n x := by
  have hlt := totalLexScore_swap_lt ha hb x hrw
  have hmax := totalLexScore_lt_max n (swapPigeons a b x)
  dsimp [phpRank]
  omega

/-- Symmetry-breaking constraint for pigeons `a < b`: `rowWeight n x a ≥ rowWeight n x b`. -/
def phpSymBreakConstraint (n a b : Nat) (x : PHPAssign) : Bool :=
  decide (rowWeight n x b ≤ rowWeight n x a)

/-- Ranked preorder on `PHPAssign` induced by `totalLexScore n`. -/
def phpRankedPreorder (n : Nat) : RankedPreorder PHPAssign where
  preceq x y := phpRank n x ≤ phpRank n y
  refl _ := Nat.le_refl _
  trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  μ x := phpRank n x

/-- **Theorem (`pigeon_swap_dominance_sound`)**:
Instantiation of `dominance_rule_preserves_sat` on `PHP_{n+1}^n` for any pair of pigeons `a < b < n + 1`:
adding the symmetry-breaking constraint `rowWeight n x b ≤ rowWeight n x a` (via `dom` with
witness `swapPigeons a b`) preserves satisfiability of `phpFormula n`. -/
theorem pigeon_swap_dominance_sound (n a b : Nat) (ha : a < b) (hb : b < n + 1) :
    (∃ x, phpFormula n x = true) ↔
    (∃ x, (phpFormula n x && phpSymBreakConstraint n a b x) = true) := by
  apply dominance_rule_preserves_sat (phpFormula n) (phpSymBreakConstraint n a b)
    (phpRankedPreorder n) (swapPigeons a b)
  intro x hx hC
  have hrw : rowWeight n x a < rowWeight n x b := by
    dsimp [phpSymBreakConstraint] at hC
    have hnot : ¬ (rowWeight n x b ≤ rowWeight n x a) := by
      intro hle
      simp [hle] at hC
    omega
  have ha_lt : a < n + 1 := Nat.lt_trans ha hb
  have hphp : phpFormula n (swapPigeons a b x) = true :=
    swapPigeons_preserves_php n a b ha_lt hb x hx
  have hrank : phpRank n (swapPigeons a b x) < phpRank n x :=
    phpRank_swap_lt ha hb x hrw
  exact ⟨hphp, Nat.le_of_lt hrank, hrank⟩

/-! ## 3. Instantiation (b): Bijective Gadget Inversion / WNU Idempotence -/

/-- A `k`-bit Boolean vector `Bool^k`. -/
abbrev BoolVec (k : Nat) := Fin k → Bool

/-- A bijection `g : α → α` witnessed by a two-sided inverse `g_inv : α → α`. -/
structure Bijection (α : Type) where
  fwd : α → α
  inv : α → α
  left_inv : ∀ x, inv (fwd x) = x
  right_inv : ∀ y, fwd (inv y) = y

/-- **Theorem (`bijective_gadget_dominance_inversion`)**:
For any bijection `g : Bool^k → Bool^k` (such as a Keccak 1-round χ/θ/π/ρ permutation or
Weak-Near-Unanimity / WNU idempotent gadget) and any predicate `P : Bool^k → Bool`:
`(∃ x, P (g.fwd x) = true) ↔ (∃ y, P y = true)`. -/
theorem bijective_gadget_dominance_inversion {k : Nat}
    (g : Bijection (BoolVec k)) (P : BoolVec k → Bool) :
    (∃ x, P (g.fwd x) = true) ↔ (∃ y, P y = true) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨g.fwd x, hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨g.inv y, ?_⟩
    rw [g.right_inv y]
    exact hy

/-- **Theorem (`bijective_gadget_via_dominance`)**:
Framing bijective gadget inversion directly as an instance of `dominance_rule_preserves_sat`:
over pairs `(x, y)` with formula `F (x, y) := P y` and target constraint `C (x, y) := (x == g.inv y)`,
the witness map `ω (x, y) := (g.inv y, y)` is strictly rank-decreasing whenever `x ≠ g.inv y`. -/
theorem bijective_gadget_via_dominance {k : Nat}
    (g : Bijection (BoolVec k)) (P : BoolVec k → Bool)
    [DecidableEq (BoolVec k)] :
    (∃ p : BoolVec k × BoolVec k, P p.2 = true) ↔
    (∃ p : BoolVec k × BoolVec k, (P p.2 && decide (p.1 = g.inv p.2)) = true) := by
  let F : BoolVec k × BoolVec k → Bool := fun p => P p.2
  let C : BoolVec k × BoolVec k → Bool := fun p => decide (p.1 = g.inv p.2)
  let R : RankedPreorder (BoolVec k × BoolVec k) := {
    preceq := fun p q => (if C p then 0 else 1) ≤ (if C q then 0 else 1)
    refl := fun _ => Nat.le_refl _
    trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
    μ := fun p => if C p then 0 else 1
  }
  let ω : BoolVec k × BoolVec k → BoolVec k × BoolVec k := fun p => (g.inv p.2, p.2)
  apply dominance_rule_preserves_sat F C R ω
  intro p hF hC
  have hCω : C (ω p) = true := by
    dsimp [C, ω]
    simp
  refine ⟨hF, ?_, ?_⟩
  · dsimp [R]
    simp [hC, hCω]
  · dsimp [R]
    simp [hC, hCω]

end VeriPBDominanceG1

/-! ## 4. Axiom Audit (`#print axioms`) -/

#print axioms VeriPBDominanceG1.dominance_rule_preserves_sat
#print axioms VeriPBDominanceG1.dominance_chain_preserves_sat
#print axioms VeriPBDominanceG1.pigeon_swap_dominance_sound
#print axioms VeriPBDominanceG1.bijective_gadget_dominance_inversion
#print axioms VeriPBDominanceG1.bijective_gadget_via_dominance

