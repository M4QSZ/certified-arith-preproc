/-
  Soundness of Higher-Order Veronese `RM(d, n)` & Cubic Homology Calculus (v0.4)
  ==============================================================================
  Standalone Lean 4.36.0 formalization (zero Mathlib imports, zero external axioms,
  zero `sorry`) covering:
    1. Group 1: Universal `∀ ls : List Bool` arbitrary-degree Veronese monomial witness
       (`p ↔ ⋀_{u ∈ ls} u`) `VeriPB 3.0` `red` validity, RUP preservation under `p ↦ false`,
       and exact `p = allTrue ls` PB characterization.
    2. Group 2: Lucas Majority-Degree Law over `F₂` (`MAJ₅ = e₃ ⊕ e₄` of degree 4, and
       `MAJ₇ = e₄` collapsing from 7 inputs to pure degree 4) + `K₅` 4-simplex cubic
       boundary cancellation (`∂₃ ∂₄ = 0`: sum of `e₃` over the 5 tetrahedral faces = 0).
    3. Group 3: Universal `∀ n, ∀ x, ∀ tets` inductive `F₂`-simplicial 3-cycle vanishing
       theorem (`simplicial_3cycle_e3_vanishes` over arbitrary 4-tuple lists).
    4. Group 4: Mechanical Degree-4 Barrier Theorem (`and5_no_deg4_annihilator`):
       across ALL `2³¹ = 2,147,483,648` polynomials in `RM(4, 5)`, `0` is the unique
       polynomial vanishing on the `31` satisfying points of `x₁ ∧ x₂ ∧ x₃ ∧ x₄ ∧ x₅ = false`.
-/

namespace HigherVeroneseSoundness

/-! ## 0. Core Helpers -/

def b2n (b : Bool) : Nat :=
  if b then 1 else 0

@[simp]
theorem b2n_not (b : Bool) : b2n (!b) = 1 - b2n b := by
  cases b <;> rfl

theorem xor_assoc_bool (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_comm_bool (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

/-! ## 1. Group 1: Universal `∀ d` (`List Bool`) Veronese Monomial `red` Soundness -/

/-- Conjunction `⋀_{b ∈ ls} b` of an arbitrary-arity literal list. -/
def allTrue : List Bool → Bool
  | [] => true
  | b :: bs => b && allTrue bs

/-- Sum `∑_{b ∈ ls} b2n (!b)` appearing in `and_all: ∑ ~u_j + p ≥ 1`. -/
def negSum : List Bool → Nat
  | [] => 0
  | b :: bs => b2n (!b) + negSum bs

/-- `and_all` holds unconditionally under witness `p ↦ true` for EVERY arity `d`. -/
theorem veronese_monom_red_1_witness (ls : List Bool) :
    negSum ls + b2n true ≥ 1 := by
  simp [b2n]

theorem negSum_pos_of_mem_false (ls : List Bool) (h : false ∈ ls) :
    negSum ls ≥ 1 := by
  induction ls with
  | nil => cases h
  | cons b bs ih =>
    cases h with
    | head => simp [negSum, b2n]
    | tail _ hm =>
      have hpos := ih hm
      simp only [negSum]
      omega

/-- For EVERY member `u ∈ ls` of an arbitrary-degree monomial, `and_0_u: u + ~p ≥ 1`
    is satisfied by witness `p ↦ false` AND preserves `and_all` whenever `and_0_u` is
    falsified (`u = false, p = true`). -/
theorem veronese_monom_red_0_rup_preserved (ls : List Bool) (u p : Bool) (hu : u ∈ ls) :
    (b2n u + b2n (!false) ≥ 1) ∧
    (¬ (b2n u + b2n (!p) ≥ 1) → negSum ls + b2n false ≥ 1) := by
  refine ⟨by simp [b2n], ?_⟩
  intro h_fals
  cases u with
  | true =>
    simp [b2n] at h_fals
  | false =>
    have h_pos := negSum_pos_of_mem_false ls hu
    simp only [b2n]
    omega

theorem negSum_eq_zero_iff_allTrue (ls : List Bool) :
    negSum ls = 0 ↔ allTrue ls = true := by
  induction ls with
  | nil => simp [negSum, allTrue]
  | cons b bs ih =>
    cases b with
    | false =>
      simp [negSum, allTrue, b2n]
    | true =>
      simp [negSum, allTrue, b2n, ih]

theorem not_mem_false_iff_allTrue (ls : List Bool) :
    ¬ (false ∈ ls) ↔ allTrue ls = true := by
  induction ls with
  | nil => simp [allTrue]
  | cons b bs ih =>
    cases b <;> simp [allTrue, ih]

/-- Universal `∀ ls : List Bool` exactness of the `(d + 1)`-clause Veronese `red` encoding:
    `and_all` together with `∀ u ∈ ls, u + ~p ≥ 1` holds IF AND ONLY IF `p = allTrue ls`. -/
theorem veronese_monom_clauses_characterize_all (ls : List Bool) (p : Bool) :
    ((negSum ls + b2n p ≥ 1) ∧ (∀ b ∈ ls, b2n b + b2n (!p) ≥ 1)) ↔ p = allTrue ls := by
  cases p with
  | true =>
    simp [b2n]
    exact not_mem_false_iff_allTrue ls
  | false =>
    simp [b2n]
    constructor
    · intro h_neg
      cases h_at : allTrue ls with
      | false => rfl
      | true =>
        have hz := (negSum_eq_zero_iff_allTrue ls).mpr h_at
        omega
    · intro h_at_false
      have h_nz : negSum ls ≠ 0 := by
        intro hz
        have h_tr := (negSum_eq_zero_iff_allTrue ls).mp hz
        rw [h_at_false] at h_tr
        cases h_tr
      omega

/-! ## 2. Group 2: Lucas Majority-Degree Law & `K₅` Cubic Boundary Identity (`∂₃ ∂₄ = 0`) -/

def sym3_4 (a b c d : Bool) : Bool :=
  xor (xor (a && b && c) (a && b && d)) (xor (a && c && d) (b && c && d))

def sym3_5 (x1 x2 x3 x4 x5 : Bool) : Bool :=
  xor (xor (xor (x1 && x2 && x3) (x1 && x2 && x4))
           (xor (x1 && x2 && x5) (x1 && x3 && x4)))
      (xor (xor (x1 && x3 && x5) (x1 && x4 && x5))
           (xor (xor (x2 && x3 && x4) (x2 && x3 && x5))
                (xor (x2 && x4 && x5) (x3 && x4 && x5))))

def sym4_5 (x1 x2 x3 x4 x5 : Bool) : Bool :=
  xor (xor (x1 && x2 && x3 && x4) (x1 && x2 && x3 && x5))
      (xor (x1 && x2 && x4 && x5)
           (xor (x1 && x3 && x4 && x5) (x2 && x3 && x4 && x5)))

def maj5 (x1 x2 x3 x4 x5 : Bool) : Bool :=
  decide (b2n x1 + b2n x2 + b2n x3 + b2n x4 + b2n x5 ≥ 3)

/-- Exact degree-4 ANF of `MAJ₅`: `MAJ₅(x₁..x₅) = e₃(x₁..x₅) ⊕ e₄(x₁..x₅)`. -/
theorem maj5_anf_e3_xor_e4 (x1 x2 x3 x4 x5 : Bool) :
    maj5 x1 x2 x3 x4 x5 = xor (sym3_5 x1 x2 x3 x4 x5) (sym4_5 x1 x2 x3 x4 x5) := by
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> rfl

/-- Evaluate elementary symmetric polynomial `e₄` on 7 Boolean inputs (`35` quartic terms). -/
def sym4_7 (x1 x2 x3 x4 x5 x6 x7 : Bool) : Bool :=
  decide (((b2n x1 + b2n x2 + b2n x3 + b2n x4 + b2n x5 + b2n x6 + b2n x7) / 4) % 2 == 1)

def maj7 (x1 x2 x3 x4 x5 x6 x7 : Bool) : Bool :=
  decide (b2n x1 + b2n x2 + b2n x3 + b2n x4 + b2n x5 + b2n x6 + b2n x7 ≥ 4)

/-- Lucas Degree-Collapse Law for `MAJ₇`: for every `(x₁..x₇) ∈ {0, 1}⁷`,
    `MAJ₇(x₁..x₇)` equals the parity of `⌊∑ xᵢ / 4⌋ = (binom(∑ xᵢ, 4) mod 2) = e₄(x₁..x₇)`,
    collapsing from 7 variables to algebraic degree 4! -/
theorem maj7_lucas_deg4_collapse (x1 x2 x3 x4 x5 x6 x7 : Bool) :
    maj7 x1 x2 x3 x4 x5 x6 x7 = sym4_7 x1 x2 x3 x4 x5 x6 x7 := by
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;>
  cases x5 <;> cases x6 <;> cases x7 <;> rfl

/-- `K₅` 4-Simplex Cubic Boundary Identity (`∂₃ ∂₄ = 0`): the `F₂` sum of `sym3_4`
    over the 5 distinct tetrahedral faces of `{u0, u1, u2, u3, u4}` vanishes identically! -/
theorem k5_4simplex_sym3_boundary_zero (u0 u1 u2 u3 u4 : Bool) :
    xor (sym3_4 u0 u1 u2 u3)
      (xor (sym3_4 u0 u1 u2 u4)
        (xor (sym3_4 u0 u1 u3 u4)
          (xor (sym3_4 u0 u2 u3 u4) (sym3_4 u1 u2 u3 u4)))) = false := by
  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;> cases u4 <;> rfl

/-! ## 3. Group 3: Universal `∀ n` Simplicial 3-Cycle Cubic Vanishing (`∂₃ C = 0 ⇒ ⨁ e₃ = 0`) -/

/-- Flip ordered 2-face `(u, v, w)` (`u < v < w`) in a 2-skeleton table `F : Nat → Nat → Nat → Bool`. -/
def flipOrd3 (u v w : Nat) (F : Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Bool :=
  fun i j k => if (i == u) && ((j == v) && (k == w)) then !(F i j k) else F i j k

/-- Apply the F₂ boundary `∂₃(a, b, c, d)` of an ordered 3-simplex `a < b < c < d`. -/
def applyTetBoundary (F : Nat → Nat → Nat → Bool) (q : Nat × Nat × Nat × Nat) :
    Nat → Nat → Nat → Bool :=
  flipOrd3 q.2.1 q.2.2.1 q.2.2.2
    (flipOrd3 q.1 q.2.2.1 q.2.2.2
      (flipOrd3 q.1 q.2.1 q.2.2.2
        (flipOrd3 q.1 q.2.1 q.2.2.1 F)))

def boundaryFaces3 (tets : List (Nat × Nat × Nat × Nat)) : Nat → Nat → Nat → Bool :=
  tets.foldl applyTetBoundary (fun _ _ _ => false)

def cubicXor1 (v w : Nat) (x : Nat → Bool) (F : Nat → Nat → Nat → Bool) : Nat → Bool
  | 0 => false
  | u + 1 => xor (cubicXor1 v w x F u) (F u v w && (x u && x v && x w))

def cubicXor2 (w : Nat) (x : Nat → Bool) (F : Nat → Nat → Nat → Bool) : Nat → Bool
  | 0 => false
  | v + 1 => xor (cubicXor2 w x F v) (cubicXor1 v w x F v)

def cubicXor3 (x : Nat → Bool) (F : Nat → Nat → Nat → Bool) : Nat → Bool
  | 0 => false
  | w + 1 => xor (cubicXor3 x F w) (cubicXor2 w x F w)

def tetsSym3Parity (x : Nat → Bool) : List (Nat × Nat × Nat × Nat) → Bool
  | [] => false
  | (a, b, c, d) :: qs => xor (sym3_4 (x a) (x b) (x c) (x d)) (tetsSym3Parity x qs)

theorem cubicXor1_zero (v w k : Nat) (x : Nat → Bool) :
    cubicXor1 v w x (fun _ _ _ => false) k = false := by
  induction k with
  | zero => rfl
  | succ u ih => simp [cubicXor1, ih]

theorem cubicXor2_zero (w m : Nat) (x : Nat → Bool) :
    cubicXor2 w x (fun _ _ _ => false) m = false := by
  induction m with
  | zero => rfl
  | succ v ih => simp [cubicXor2, ih, cubicXor1_zero]

theorem cubicXor3_zero (n : Nat) (x : Nat → Bool) :
    cubicXor3 x (fun _ _ _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ w ih => simp [cubicXor3, ih, cubicXor2_zero]

theorem cubicXor1_flip_ne (v w a b c k : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hne : v ≠ b ∨ w ≠ c) :
    cubicXor1 v w x (flipOrd3 a b c F) k = cubicXor1 v w x F k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    have hcond : ((u == a) && ((v == b) && (w == c))) = false := by
      cases hne with
      | inl hvb =>
        have h1 : (v == b) = false := beq_false_of_ne hvb
        simp [h1]
      | inr hwc =>
        have h2 : (w == c) = false := beq_false_of_ne hwc
        simp [h2]
    simp only [cubicXor1, flipOrd3, hcond, ih]
    rfl

theorem cubicXor1_flip_le (b c a k : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hle : k ≤ a) :
    cubicXor1 b c x (flipOrd3 a b c F) k = cubicXor1 b c x F k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    have hua : (u == a) = false := beq_false_of_ne (Nat.ne_of_lt hle)
    simp only [cubicXor1, flipOrd3, hua, Bool.false_and, ih (Nat.le_of_succ_le hle)]
    rfl

theorem cubicXor1_flip_gt (b c a k : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hgt : a < k) :
    cubicXor1 b c x (flipOrd3 a b c F) k =
      xor (cubicXor1 b c x F k) (x a && x b && x c) := by
  induction k with
  | zero => exact absurd hgt (Nat.not_lt_zero a)
  | succ u ih =>
    by_cases h_eq : a = u
    · subst h_eq
      have h_le := cubicXor1_flip_le b c a a x F (Nat.le_refl a)
      simp only [cubicXor1, flipOrd3, h_le, beq_self_eq_true, Bool.and_self]
      cases (cubicXor1 b c x F a) <;> cases (F a b c) <;> cases (x a && x b && x c) <;> rfl
    · have h_lt : a < u := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hgt) h_eq
      have hua : (u == a) = false := beq_false_of_ne (Ne.symm h_eq)
      simp only [cubicXor1, flipOrd3, hua, Bool.false_and, ih h_lt]
      have hif : (if false = true then !(F u b c) else F u b c) = F u b c := rfl
      rw [hif]
      cases (cubicXor1 b c x F u) <;> cases (x a && x b && x c) <;>
        cases (F u b c && (x u && x b && x c)) <;> rfl

theorem cubicXor2_flip_ne_w (w a b c m : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hne : w ≠ c) :
    cubicXor2 w x (flipOrd3 a b c F) m = cubicXor2 w x F m := by
  induction m with
  | zero => rfl
  | succ v ih =>
    simp [cubicXor2, ih, cubicXor1_flip_ne v w a b c v x F (Or.inr hne)]

theorem cubicXor2_flip_le_b (c a b m : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hle : m ≤ b) :
    cubicXor2 c x (flipOrd3 a b c F) m = cubicXor2 c x F m := by
  induction m with
  | zero => rfl
  | succ v ih =>
    have hvb : v ≠ b := Nat.ne_of_lt hle
    simp [cubicXor2, ih (Nat.le_of_succ_le hle), cubicXor1_flip_ne v c a b c v x F (Or.inl hvb)]

theorem cubicXor2_flip_gt_b (c a b m : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hab : a < b) (hbm : b < m) :
    cubicXor2 c x (flipOrd3 a b c F) m =
      xor (cubicXor2 c x F m) (x a && x b && x c) := by
  induction m with
  | zero => exact absurd hbm (Nat.not_lt_zero b)
  | succ v ih =>
    by_cases h_eq : b = v
    · subst h_eq
      have h_le := cubicXor2_flip_le_b c a b b x F (Nat.le_refl b)
      have h_c1 := cubicXor1_flip_gt b c a b x F hab
      simp only [cubicXor2, h_le, h_c1]
      cases (cubicXor2 c x F b) <;> cases (cubicXor1 b c x F b) <;> cases (x a && x b && x c) <;> rfl
    · have h_lt : b < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hbm) h_eq
      have h_c1 := cubicXor1_flip_ne v c a b c v x F (Or.inl (Ne.symm h_eq))
      simp only [cubicXor2, h_c1, ih h_lt]
      cases (cubicXor2 c x F v) <;> cases (x a && x b && x c) <;> cases (cubicXor1 v c x F v) <;> rfl

theorem cubicXor3_flip_le_c (a b c n : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hle : n ≤ c) :
    cubicXor3 x (flipOrd3 a b c F) n = cubicXor3 x F n := by
  induction n with
  | zero => rfl
  | succ w ih =>
    have hwc : w ≠ c := Nat.ne_of_lt hle
    simp [cubicXor3, ih (Nat.le_of_succ_le hle), cubicXor2_flip_ne_w w a b c w x F hwc]

theorem cubicXor3_flip_lt (a b c n : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (hab : a < b) (hbc : b < c) (hcn : c < n) :
    cubicXor3 x (flipOrd3 a b c F) n =
      xor (cubicXor3 x F n) (x a && x b && x c) := by
  induction n with
  | zero => exact absurd hcn (Nat.not_lt_zero c)
  | succ w ih =>
    by_cases h_eq : c = w
    · subst h_eq
      have h_le := cubicXor3_flip_le_c a b c c x F (Nat.le_refl c)
      have h_c2 := cubicXor2_flip_gt_b c a b c x F hab hbc
      simp only [cubicXor3, h_le, h_c2]
      cases (cubicXor3 x F c) <;> cases (cubicXor2 c x F c) <;> cases (x a && x b && x c) <;> rfl
    · have h_lt : c < w := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hcn) h_eq
      have h_c2 := cubicXor2_flip_ne_w w a b c w x F (Ne.symm h_eq)
      simp only [cubicXor3, h_c2, ih h_lt]
      cases (cubicXor3 x F w) <;> cases (x a && x b && x c) <;> cases (cubicXor2 w x F w) <;> rfl

/-- Ordered 4-tuple predicate `a < b < c < d < n` (canonical vertices of a 3-simplex). -/
def ValidOrderedTet (n : Nat) (q : Nat × Nat × Nat × Nat) : Prop :=
  q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < n

theorem cubicXor3_applyTetBoundary (n : Nat) (x : Nat → Bool)
    (F : Nat → Nat → Nat → Bool) (q : Nat × Nat × Nat × Nat) (hq : ValidOrderedTet n q) :
    cubicXor3 x (applyTetBoundary F q) n =
      xor (cubicXor3 x F n) (sym3_4 (x q.1) (x q.2.1) (x q.2.2.1) (x q.2.2.2)) := by
  rcases q with ⟨a, b, c, d⟩
  rcases hq with ⟨hab, hbc, hcd, hdn⟩
  have hac : a < c := Nat.lt_trans hab hbc
  have hbd : b < d := Nat.lt_trans hbc hcd
  have hcn : c < n := Nat.lt_trans hcd hdn
  unfold applyTetBoundary
  simp only
  rw [cubicXor3_flip_lt b c d n x _ hbc hcd hdn]
  rw [cubicXor3_flip_lt a c d n x _ hac hcd hdn]
  rw [cubicXor3_flip_lt a b d n x _ hab hbd hdn]
  rw [cubicXor3_flip_lt a b c n x _ hab hbc hcn]
  unfold sym3_4
  cases (cubicXor3 x F n) <;> cases (x a && x b && x c) <;> cases (x a && x b && x d) <;>
    cases (x a && x c && x d) <;> cases (x b && x c && x d) <;> rfl

theorem cubicXor1_congr (v w k : Nat) (x : Nat → Bool)
    (F1 F2 : Nat → Nat → Nat → Bool) (h : ∀ u, u < k → F1 u v w = F2 u v w) :
    cubicXor1 v w x F1 k = cubicXor1 v w x F2 k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    simp [cubicXor1, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h u (Nat.lt_succ_self u)]

theorem cubicXor2_congr (w m : Nat) (x : Nat → Bool)
    (F1 F2 : Nat → Nat → Nat → Bool) (h : ∀ u v, u < v → v < m → F1 u v w = F2 u v w) :
    cubicXor2 w x F1 m = cubicXor2 w x F2 m := by
  induction m with
  | zero => rfl
  | succ v ih =>
    have h1 := ih (fun i j hij hjv => h i j hij (Nat.lt_succ_of_lt hjv))
    have h2 := cubicXor1_congr v w v x F1 F2 (fun u huv => h u v huv (Nat.lt_succ_self v))
    simp [cubicXor2, h1, h2]

theorem cubicXor3_congr (n : Nat) (x : Nat → Bool)
    (F1 F2 : Nat → Nat → Nat → Bool)
    (h : ∀ u v w, u < v → v < w → w < n → F1 u v w = F2 u v w) :
    cubicXor3 x F1 n = cubicXor3 x F2 n := by
  induction n with
  | zero => rfl
  | succ w ih =>
    have h1 := ih (fun i j k hij hjk hkw => h i j k hij hjk (Nat.lt_succ_of_lt hkw))
    have h2 := cubicXor2_congr w w x F1 F2 (fun u v huv hvw => h u v w huv hvw (Nat.lt_succ_self w))
    simp [cubicXor3, h1, h2]

theorem cubicXor3_foldl_tets (n : Nat) (x : Nat → Bool)
    (tets : List (Nat × Nat × Nat × Nat)) (F : Nat → Nat → Nat → Bool)
    (h_valid : ∀ q ∈ tets, ValidOrderedTet n q) :
    cubicXor3 x (tets.foldl applyTetBoundary F) n =
      xor (cubicXor3 x F n) (tetsSym3Parity x tets) := by
  induction tets generalizing F with
  | nil => simp [tetsSym3Parity]
  | cons q qs ih =>
    have hq := h_valid q (List.Mem.head qs)
    have hqs : ∀ q' ∈ qs, ValidOrderedTet n q' := fun q' hm => h_valid q' (List.Mem.tail q hm)
    rcases q with ⟨a, b, c, d⟩
    simp only [List.foldl_cons, tetsSym3Parity]
    rw [ih (applyTetBoundary F (a, b, c, d)) hqs]
    rw [cubicXor3_applyTetBoundary n x F (a, b, c, d) hq]
    rw [xor_assoc_bool]

/-- Universal F₂-Simplicial 3-Cycle Cubic Vanishing Theorem (`∂₃ C = 0 ⇒ ⨁ e₃ = 0`):
    for EVERY `n : Nat`, EVERY assignment `x : Nat → Bool`, and EVERY list of ordered
    tetrahedra `tets` in `{0, ..., n-1}` whose 2-skeleton boundary has even multiplicity
    on every triangle `(u, v, w)`, the global XOR sum of `sym3_4` vanishes identically! -/
theorem simplicial_3cycle_e3_vanishes (n : Nat) (x : Nat → Bool)
    (tets : List (Nat × Nat × Nat × Nat))
    (h_valid : ∀ q ∈ tets, ValidOrderedTet n q)
    (h_cycle : ∀ u v w, u < v → v < w → w < n → boundaryFaces3 tets u v w = false) :
    tetsSym3Parity x tets = false := by
  have h_fold := cubicXor3_foldl_tets n x tets (fun _ _ _ => false) h_valid
  rw [cubicXor3_zero, Bool.false_xor] at h_fold
  have h_congr := cubicXor3_congr n x (boundaryFaces3 tets) (fun _ _ _ => false) h_cycle
  rw [cubicXor3_zero] at h_congr
  unfold boundaryFaces3 at h_congr
  rw [← h_fold, h_congr]

/-! ## 4. Group 4: Mechanical Degree-4 Barrier Theorem (`RM(4, 5)` on `AND₅`) -/

/-- Evaluate a general 31-coefficient degree-≤ 4 polynomial in `RM(4, 5)` on `(x1..x5)` over `F₂`. -/
def evalRM4_5
    (c0
     c1 c2 c3 c4 c5
     c12 c13 c14 c15 c23 c24 c25 c34 c35 c45
     c123 c124 c125 c134 c135 c145 c234 c235 c245 c345
     c1234 c1235 c1245 c1345 c2345
     x1 x2 x3 x4 x5 : Bool) : Bool :=
  let d01 := xor c0 (xor (c1 && x1) (xor (c2 && x2) (xor (c3 && x3) (xor (c4 && x4) (c5 && x5)))))
  let d2a := xor (c12 && (x1 && x2)) (xor (c13 && (x1 && x3)) (xor (c14 && (x1 && x4)) (xor (c15 && (x1 && x5)) (c23 && (x2 && x3)))))
  let d2b := xor (c24 && (x2 && x4)) (xor (c25 && (x2 && x5)) (xor (c34 && (x3 && x4)) (xor (c35 && (x3 && x5)) (c45 && (x4 && x5)))))
  let d3a := xor (c123 && (x1 && x2 && x3)) (xor (c124 && (x1 && x2 && x4)) (xor (c125 && (x1 && x2 && x5)) (xor (c134 && (x1 && x3 && x4)) (c135 && (x1 && x3 && x5)))))
  let d3b := xor (c145 && (x1 && x4 && x5)) (xor (c234 && (x2 && x3 && x4)) (xor (c235 && (x2 && x3 && x5)) (xor (c245 && (x2 && x4 && x5)) (c345 && (x3 && x4 && x5)))))
  let d4  := xor (c1234 && (x1 && x2 && x3 && x4)) (xor (c1235 && (x1 && x2 && x3 && x5)) (xor (c1245 && (x1 && x2 && x4 && x5)) (xor (c1345 && (x1 && x3 && x4 && x5)) (c2345 && (x2 && x3 && x4 && x5)))))
  xor (xor d01 (xor d2a d2b)) (xor (xor d3a d3b) d4)

/-- Mechanical Degree-4 Barrier Theorem (`RM(4, 5)` Vanishing Ideal = `{0}` on `AND₅ = 0`):
    across ALL `2³¹ = 2,147,483,648` degree-≤ 4 polynomials in `RM(4, 5)`, if `P(x₁..x₅)`
    vanishes on the 31 satisfying assignments of `x₁ ∧ x₂ ∧ x₃ ∧ x₄ ∧ x₅ = false` (all points
    of Hamming weight `≤ 4`), then ALL 31 coefficients of `P` are `false`! -/
theorem and5_no_deg4_annihilator
    (c0
     c1 c2 c3 c4 c5
     c12 c13 c14 c15 c23 c24 c25 c34 c35 c45
     c123 c124 c125 c134 c135 c145 c234 c235 c245 c345
     c1234 c1235 c1245 c1345 c2345 : Bool)
    (h : ∀ x1 x2 x3 x4 x5 : Bool,
      (x1 && x2 && x3 && x4 && x5) = false →
      evalRM4_5 c0 c1 c2 c3 c4 c5
        c12 c13 c14 c15 c23 c24 c25 c34 c35 c45
        c123 c124 c125 c134 c135 c145 c234 c235 c245 c345
        c1234 c1235 c1245 c1345 c2345
        x1 x2 x3 x4 x5 = false) :
    c0 = false ∧
    c1 = false ∧ c2 = false ∧ c3 = false ∧ c4 = false ∧ c5 = false ∧
    c12 = false ∧ c13 = false ∧ c14 = false ∧ c15 = false ∧ c23 = false ∧
    c24 = false ∧ c25 = false ∧ c34 = false ∧ c35 = false ∧ c45 = false ∧
    c123 = false ∧ c124 = false ∧ c125 = false ∧ c134 = false ∧ c135 = false ∧
    c145 = false ∧ c234 = false ∧ c235 = false ∧ c245 = false ∧ c345 = false ∧
    c1234 = false ∧ c1235 = false ∧ c1245 = false ∧ c1345 = false ∧ c2345 = false := by
  have w0    := h false false false false false rfl
  have w1    := h true  false false false false rfl
  have w2    := h false true  false false false rfl
  have w3    := h false false true  false false rfl
  have w4    := h false false false true  false rfl
  have w5    := h false false false false true  rfl
  have w12   := h true  true  false false false rfl
  have w13   := h true  false true  false false rfl
  have w14   := h true  false false true  false rfl
  have w15   := h true  false false false true  rfl
  have w23   := h false true  true  false false rfl
  have w24   := h false true  false true  false rfl
  have w25   := h false true  false false true  rfl
  have w34   := h false false true  true  false rfl
  have w35   := h false false true  false true  rfl
  have w45   := h false false false true  true  rfl
  have w123  := h true  true  true  false false rfl
  have w124  := h true  true  false true  false rfl
  have w125  := h true  true  false false true  rfl
  have w134  := h true  false true  true  false rfl
  have w135  := h true  false true  false true  rfl
  have w145  := h true  false false true  true  rfl
  have w234  := h false true  true  true  false rfl
  have w235  := h false true  true  false true  rfl
  have w245  := h false true  false true  true  rfl
  have w345  := h false false true  true  true  rfl
  have w1234 := h true  true  true  true  false rfl
  have w1235 := h true  true  true  false true  rfl
  have w1245 := h true  true  false true  true  rfl
  have w1345 := h true  false true  true  true  rfl
  have w2345 := h false true  true  true  true  rfl
  clear h
  simp [evalRM4_5] at w0 w1 w2 w3 w4 w5 w12 w13 w14 w15 w23 w24 w25 w34 w35 w45
  simp [evalRM4_5] at w123 w124 w125 w134 w135 w145 w234 w235 w245 w345 w1234 w1235 w1245 w1345 w2345
  have z0 : c0 = false := by cases c0 <;> simp at w0 ⊢
  simp only [z0] at w1 w2 w3 w4 w5 w12 w13 w14 w15 w23 w24 w25 w34 w35 w45 w123 w124 w125 w134 w135 w145 w234 w235 w245 w345 w1234 w1235 w1245 w1345 w2345 ⊢
  have z1 : c1 = false := by cases c1 <;> simp at w1 ⊢
  have z2 : c2 = false := by cases c2 <;> simp at w2 ⊢
  have z3 : c3 = false := by cases c3 <;> simp at w3 ⊢
  have z4 : c4 = false := by cases c4 <;> simp at w4 ⊢
  have z5 : c5 = false := by cases c5 <;> simp at w5 ⊢
  simp only [z1, z2, z3, z4, z5] at w12 w13 w14 w15 w23 w24 w25 w34 w35 w45 w123 w124 w125 w134 w135 w145 w234 w235 w245 w345 w1234 w1235 w1245 w1345 w2345 ⊢
  have z12 : c12 = false := by cases c12 <;> simp at w12 ⊢
  have z13 : c13 = false := by cases c13 <;> simp at w13 ⊢
  have z14 : c14 = false := by cases c14 <;> simp at w14 ⊢
  have z15 : c15 = false := by cases c15 <;> simp at w15 ⊢
  have z23 : c23 = false := by cases c23 <;> simp at w23 ⊢
  have z24 : c24 = false := by cases c24 <;> simp at w24 ⊢
  have z25 : c25 = false := by cases c25 <;> simp at w25 ⊢
  have z34 : c34 = false := by cases c34 <;> simp at w34 ⊢
  have z35 : c35 = false := by cases c35 <;> simp at w35 ⊢
  have z45 : c45 = false := by cases c45 <;> simp at w45 ⊢
  simp only [z12, z13, z14, z15, z23, z24, z25, z34, z35, z45] at w123 w124 w125 w134 w135 w145 w234 w235 w245 w345 w1234 w1235 w1245 w1345 w2345 ⊢
  have z123 : c123 = false := by cases c123 <;> simp at w123 ⊢
  have z124 : c124 = false := by cases c124 <;> simp at w124 ⊢
  have z125 : c125 = false := by cases c125 <;> simp at w125 ⊢
  have z134 : c134 = false := by cases c134 <;> simp at w134 ⊢
  have z135 : c135 = false := by cases c135 <;> simp at w135 ⊢
  have z145 : c145 = false := by cases c145 <;> simp at w145 ⊢
  have z234 : c234 = false := by cases c234 <;> simp at w234 ⊢
  have z235 : c235 = false := by cases c235 <;> simp at w235 ⊢
  have z245 : c245 = false := by cases c245 <;> simp at w245 ⊢
  have z345 : c345 = false := by cases c345 <;> simp at w345 ⊢
  simp only [z123, z124, z125, z134, z135, z145, z234, z235, z245, z345] at w1234 w1235 w1245 w1345 w2345 ⊢
  have z1234 : c1234 = false := by cases c1234 <;> simp at w1234 ⊢
  have z1235 : c1235 = false := by cases c1235 <;> simp at w1235 ⊢
  have z1245 : c1245 = false := by cases c1245 <;> simp at w1245 ⊢
  have z1345 : c1345 = false := by cases c1345 <;> simp at w1345 ⊢
  have z2345 : c2345 = false := by cases c2345 <;> simp at w2345 ⊢
  simp only [z1234, z1235, z1245, z1345, z2345, and_self]

/-! ## 5. Axiom Footprint Audit (`0 sorryAx`, Kernel Axioms Only) -/

#print axioms veronese_monom_red_1_witness
#print axioms veronese_monom_red_0_rup_preserved
#print axioms veronese_monom_clauses_characterize_all
#print axioms maj5_anf_e3_xor_e4
#print axioms maj7_lucas_deg4_collapse
#print axioms k5_4simplex_sym3_boundary_zero
#print axioms simplicial_3cycle_e3_vanishes
#print axioms and5_no_deg4_annihilator

end HigherVeroneseSoundness
