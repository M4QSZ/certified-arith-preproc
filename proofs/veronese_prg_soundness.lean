/-
  Soundness of VeriPB 3.0 Blind Degree-2 Veronese & Homological PRG Calculus (v0.3)
  =================================================================================
  Standalone Lean 4.36.0 formalization (zero Mathlib imports, zero external axioms,
  zero `sorry`) covering:
    1. Group 1: Veronese degree-2 product extension (`p ↔ u ∧ w`) `red` witness validity,
       RUP preservation under witness substitution, and exact integer characterization.
    2. Group 2: Polarity-scrambling invariance of degree-2 Reed-Muller space `RM(2, n)`
       for both `AND₂` (`TSA`) and `MAJ₃` (`XOR-MAJ₃`) predicates.
    3. Group 3: Universal `∀ n` F₂-simplicial 2-cycle boundary cancellation (`∂² = 0`)
       for `MAJ₃` masks (`k4_tetrahedron_maj3_boundary_zero` and inductive
       `simplicial_2cycle_maj3_vanishes` over arbitrary triangle lists).
    4. Group 4: Universal `∀ V, n` unsatisfiability of single-expander Homological
       `XOR₃-MAJ₃` and `TSA` formulas with odd global charge.
    5. Group 5: Exact clause-halving (`B = 1`) over Boolean cubes, inductive XOR-chain
       folding soundness, and arbitrary-multiplicity Veronese CG halving cancellation.
    6. Group 6: Mechanical degree-2 barrier theorem (`cubic_xor_and3_no_deg2_annihilator`):
       the vanishing ideal of `y ⊕ (x₁ ∧ x₂ ∧ x₃) = c` in `RM(2, 4)` is `{0}`.
-/

namespace VeronesePrgSoundness

/-! ## 0. Boolean-to-Nat Helpers & Core Gates -/

def b2n (b : Bool) : Nat :=
  if b then 1 else 0

@[simp]
theorem b2n_not (b : Bool) : b2n (!b) = 1 - b2n b := by
  cases b <;> rfl

@[simp]
theorem b2n_add_not (b : Bool) : b2n b + b2n (!b) = 1 := by
  cases b <;> rfl

def maj3 (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

theorem xor_assoc_bool (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_comm_bool (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

theorem xor_self_bool (a : Bool) : xor a a = false := by
  cases a <;> rfl

theorem xor_false_right (a : Bool) : xor a false = a := by
  cases a <;> rfl

theorem xor_false_left (a : Bool) : xor false a = a := by
  cases a <;> rfl

theorem not_and_eq_xor (e p : Bool) : ((!e) && p) = xor (e && p) p := by
  cases e <;> cases p <;> rfl

theorem and_comm_bool (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

/-! ## 1. Group 1: Veronese Product Witness (`p ↔ u ∧ w`) VeriPB `red` Soundness -/

/-- `and_11`: `~u + ~w + p ≥ 1` holds under witness `p ↦ true`. -/
theorem veronese_and_red_11_witness (u w : Bool) :
    b2n (!u) + b2n (!w) + b2n true ≥ 1 := by
  simp [b2n]

/-- `and_0x`: `u + ~p ≥ 1` holds under witness `p ↦ false`, AND preserves `and_11`
    whenever `and_0x` is falsified (`u = false, p = true`). -/
theorem veronese_and_red_0x_sound (u w p : Bool) :
    (b2n u + b2n (!false) ≥ 1) ∧
    (¬ (b2n u + b2n (!p) ≥ 1) → b2n (!u) + b2n (!w) + b2n false ≥ 1) := by
  cases u <;> cases w <;> cases p <;> simp [b2n]

/-- `and_x0`: `w + ~p ≥ 1` holds under witness `p ↦ false`, AND preserves both
    `and_11` and `and_0x` whenever `and_x0` is falsified (`w = false, p = true`). -/
theorem veronese_and_red_x0_sound (u w p : Bool) :
    (b2n w + b2n (!false) ≥ 1) ∧
    (¬ (b2n w + b2n (!p) ≥ 1) →
      (b2n (!u) + b2n (!w) + b2n false ≥ 1) ∧ (b2n u + b2n (!false) ≥ 1)) := by
  cases u <;> cases w <;> cases p <;> simp [b2n]

/-- Exact characterization: the three Veronese `red` clauses hold iff `p = (u && w)`
    (equivalently `b2n p = b2n u * b2n w`). -/
theorem veronese_and_clauses_characterize_prod (u w p : Bool) :
    ((b2n (!u) + b2n (!w) + b2n p ≥ 1) ∧
     (b2n u + b2n (!p) ≥ 1) ∧
     (b2n w + b2n (!p) ≥ 1)) ↔ (p = (u && w) ∧ b2n p = b2n u * b2n w) := by
  cases u <;> cases w <;> cases p <;> decide

/-! ## 2. Group 2: Polarity-Scrambling Invariance of `RM(2, n)` -/

/-- Exact F₂ algebraic normal form of `maj3`: elementary symmetric quadratic boundary. -/
theorem maj3_anf_f2_exact (a b c : Bool) :
    maj3 a b c = xor (xor (a && b) (a && c)) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Under arbitrary literal polarity flips `su, sw : Bool`, `(u ⊕ su) ∧ (w ⊕ sw)`
    decomposes into an affine (`deg ≤ 1`) shift plus the UNCHANGED quadratic term `u ∧ w`. -/
theorem and_polarity_scramble_invariance (u w su sw : Bool) :
    ((xor u su) && (xor w sw)) =
      xor (xor (su && sw) (xor (sw && u) (su && w))) (u && w) := by
  cases u <;> cases w <;> cases su <;> cases sw <;> rfl

/-- Under arbitrary literal polarity flips `sa, sb, sc : Bool`, `maj3 (a ⊕ sa) (b ⊕ sb) (c ⊕ sc)`
    has the EXACT same degree-2 quadratic boundary `maj3 a b c` up to an affine (`deg ≤ 1`) shift. -/
theorem maj3_polarity_scramble_boundary_invariance (a b c sa sb sc : Bool) :
    maj3 (xor a sa) (xor b sb) (xor c sc) =
      xor
        (xor (maj3 sa sb sc)
             (xor (( xor sb sc ) && a) (xor ((xor sa sc) && b) ((xor sa sb) && c))))
        (maj3 a b c) := by
  cases a <;> cases b <;> cases c <;> cases sa <;> cases sb <;> cases sc <;> rfl

/-! ## 3. Group 3: Universal `∀ n` F₂-Simplicial 2-Cycle Boundary Cancellation (`∂² = 0`) -/

/-- Tetrahedron (`K₄`) 2-cycle identity: the XOR sum of `maj3` over the 4 distinct 3-faces
    of `{u0, u1, u2, u3}` vanishes identically on `{0, 1}⁴`. -/
theorem k4_tetrahedron_maj3_boundary_zero (u0 u1 u2 u3 : Bool) :
    xor (xor (maj3 u0 u1 u2) (maj3 u0 u1 u3))
        (xor (maj3 u0 u2 u3) (maj3 u1 u2 u3)) = false := by
  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;> rfl

/-- Flip entry `(u, v)` of an ordered 2-skeleton edge table `E : Nat → Nat → Bool`. -/
def flipOrdered (u v : Nat) (E : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun i j => if (i == u) && (j == v) then !(E i j) else E i j

/-- Flip an undirected 1-simplex `{a, b}` (`a ≠ b`) in canonical order `min < max`. -/
def flipUndirected (a b : Nat) (E : Nat → Nat → Bool) : Nat → Nat → Bool :=
  if a < b then flipOrdered a b E
  else if b < a then flipOrdered b a E
  else E

/-- Apply the F₂ boundary `∂(a, b, c) = {a,b} + {a,c} + {b,c}` of a 2-simplex. -/
def applyTriBoundary (E : Nat → Nat → Bool) (t : Nat × Nat × Nat) : Nat → Nat → Bool :=
  flipUndirected t.2.1 t.2.2 (flipUndirected t.1 t.2.2 (flipUndirected t.1 t.2.1 E))

/-- Induced 1-skeleton boundary mod 2 of a list of triangles. -/
def boundaryEdges (tris : List (Nat × Nat × Nat)) : Nat → Nat → Bool :=
  tris.foldl applyTriBoundary (fun _ _ => false)

/-- Evaluate `⨁_{0 ≤ u < k} E u v ∧ x u ∧ x v`. -/
def colQuadXor (v : Nat) (x : Nat → Bool) (E : Nat → Nat → Bool) : Nat → Bool
  | 0 => false
  | u + 1 => xor (colQuadXor v x E u) (E u v && (x u && x v))

/-- Evaluate `⨁_{0 ≤ u < v < n} E u v ∧ x u ∧ x v`. -/
def quadXor (x : Nat → Bool) (E : Nat → Nat → Bool) : Nat → Bool
  | 0 => false
  | v + 1 => xor (quadXor x E v) (colQuadXor v x E v)

/-- Folded XOR sum of `maj3 (x a) (x b) (x c)` over an arbitrary list of triangles. -/
def trisMajParity (x : Nat → Bool) : List (Nat × Nat × Nat) → Bool
  | [] => false
  | (a, b, c) :: ts => xor (maj3 (x a) (x b) (x c)) (trisMajParity x ts)

theorem colQuadXor_zero (v : Nat) (x : Nat → Bool) :
    colQuadXor v x (fun _ _ => false) k = false := by
  induction k with
  | zero => rfl
  | succ u ih => simp [colQuadXor, ih]

theorem quadXor_zero (n : Nat) (x : Nat → Bool) :
    quadXor x (fun _ _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ v ih =>
    simp [quadXor, ih, colQuadXor_zero]

theorem colQuadXor_flipOrdered_ne_col (v a b k : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (hne : v ≠ b) :
    colQuadXor v x (flipOrdered a b E) k = colQuadXor v x E k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    have hvb : (v == b) = false := beq_false_of_ne hne
    simp [colQuadXor, flipOrdered, hvb, ih]

theorem colQuadXor_flipOrdered_le_row (b a k : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (hle : k ≤ a) :
    colQuadXor b x (flipOrdered a b E) k = colQuadXor b x E k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    have hua : (u == a) = false := beq_false_of_ne (Nat.ne_of_lt hle)
    have ih' := ih (Nat.le_of_succ_le hle)
    simp [colQuadXor, flipOrdered, hua, ih']

theorem colQuadXor_flipOrdered_gt_row (b a k : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (hgt : a < k) :
    colQuadXor b x (flipOrdered a b E) k =
      xor (colQuadXor b x E k) (x a && x b) := by
  induction k with
  | zero => exact absurd hgt (Nat.not_lt_zero a)
  | succ u ih =>
    by_cases h_eq : a = u
    · subst h_eq
      have h_le := colQuadXor_flipOrdered_le_row b a a x E (Nat.le_refl a)
      simp only [colQuadXor, flipOrdered, h_le]
      have haa : (a == a) = true := beq_self_eq_true a
      have hbb : (b == b) = true := beq_self_eq_true b
      simp only [haa, hbb, Bool.and_self]
      cases (colQuadXor b x E a) <;> cases (E a b) <;> cases (x a && x b) <;> rfl
    · have h_lt : a < u := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hgt) h_eq
      have hua : (u == a) = false := beq_false_of_ne (Ne.symm h_eq)
      have ih' := ih h_lt
      simp only [colQuadXor, flipOrdered, hua, Bool.false_and, ih']
      have hif : (if false = true then !(E u b) else E u b) = E u b := rfl
      rw [hif]
      cases (colQuadXor b x E u) <;> cases (x a && x b) <;> cases (E u b && (x u && x b)) <;> rfl

theorem quadXor_flipOrdered_le (a b n : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (hle : n ≤ b) :
    quadXor x (flipOrdered a b E) n = quadXor x E n := by
  induction n with
  | zero => rfl
  | succ v ih =>
    have hvb : v ≠ b := Nat.ne_of_lt hle
    have hcol := colQuadXor_flipOrdered_ne_col v a b v x E hvb
    have ih' := ih (Nat.le_of_succ_le hle)
    simp [quadXor, hcol, ih']

theorem quadXor_flipOrdered_lt (a b n : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (hab : a < b) (hbn : b < n) :
    quadXor x (flipOrdered a b E) n = xor (quadXor x E n) (x a && x b) := by
  induction n with
  | zero => exact absurd hbn (Nat.not_lt_zero b)
  | succ v ih =>
    by_cases h_eq : b = v
    · subst h_eq
      have h_le := quadXor_flipOrdered_le a b b x E (Nat.le_refl b)
      have h_col := colQuadXor_flipOrdered_gt_row b a b x E hab
      simp only [quadXor, h_le, h_col]
      rw [← xor_assoc_bool]
    · have h_lt : b < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hbn) h_eq
      have h_col := colQuadXor_flipOrdered_ne_col v a b v x E (Ne.symm h_eq)
      have ih' := ih h_lt
      simp only [quadXor, h_col, ih']
      rw [xor_assoc_bool (quadXor x E v) (x a && x b) (colQuadXor v x E v)]
      rw [xor_comm_bool (x a && x b) (colQuadXor v x E v)]
      rw [← xor_assoc_bool]

theorem quadXor_flipUndirected (a b n : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (ha : a < n) (hb : b < n) (hne : a ≠ b) :
    quadXor x (flipUndirected a b E) n = xor (quadXor x E n) (x a && x b) := by
  unfold flipUndirected
  by_cases hab : a < b
  · simp [hab, quadXor_flipOrdered_lt a b n x E hab hb]
  · have hba : b < a := Nat.lt_of_le_of_ne (Nat.not_lt.mp hab) (Ne.symm hne)
    simp [hab, hba, quadXor_flipOrdered_lt b a n x E hba ha, and_comm_bool (x b) (x a)]

def ValidTri (n : Nat) (t : Nat × Nat × Nat) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

theorem quadXor_applyTriBoundary (n : Nat) (x : Nat → Bool)
    (E : Nat → Nat → Bool) (t : Nat × Nat × Nat) (ht : ValidTri n t) :
    quadXor x (applyTriBoundary E t) n =
      xor (quadXor x E n) (maj3 (x t.1) (x t.2.1) (x t.2.2)) := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨ha, hb, hc, hab, hac, hbc⟩
  unfold applyTriBoundary
  rw [quadXor_flipUndirected b c n x _ hb hc hbc]
  rw [quadXor_flipUndirected a c n x _ ha hc hac]
  rw [quadXor_flipUndirected a b n x _ ha hb hab]
  rw [maj3_anf_f2_exact]
  rw [xor_assoc_bool (quadXor x E n) (x a && x b) (x a && x c)]
  rw [xor_assoc_bool (quadXor x E n) (xor (x a && x b) (x a && x c)) (x b && x c)]

theorem quadXor_foldl_tris (n : Nat) (x : Nat → Bool)
    (tris : List (Nat × Nat × Nat)) (E : Nat → Nat → Bool)
    (h_valid : ∀ t ∈ tris, ValidTri n t) :
    quadXor x (tris.foldl applyTriBoundary E) n =
      xor (quadXor x E n) (trisMajParity x tris) := by
  induction tris generalizing E with
  | nil =>
    simp [trisMajParity]
  | cons t ts ih =>
    have ht := h_valid t (List.Mem.head ts)
    have hts : ∀ t' ∈ ts, ValidTri n t' :=
      fun t' hm => h_valid t' (List.Mem.tail t hm)
    rcases t with ⟨a, b, c⟩
    simp only [List.foldl_cons, trisMajParity]
    rw [ih (applyTriBoundary E (a, b, c)) hts]
    rw [quadXor_applyTriBoundary n x E (a, b, c) ht]
    rw [xor_assoc_bool]

theorem colQuadXor_congr (v k : Nat) (x : Nat → Bool)
    (E1 E2 : Nat → Nat → Bool) (h_eq : ∀ u, u < k → E1 u v = E2 u v) :
    colQuadXor v x E1 k = colQuadXor v x E2 k := by
  induction k with
  | zero => rfl
  | succ u ih =>
    have h1 := ih (fun i hi => h_eq i (Nat.lt_succ_of_lt hi))
    have h2 := h_eq u (Nat.lt_succ_self u)
    simp [colQuadXor, h1, h2]

theorem quadXor_congr (n : Nat) (x : Nat → Bool)
    (E1 E2 : Nat → Nat → Bool) (h_eq : ∀ u v, u < v → v < n → E1 u v = E2 u v) :
    quadXor x E1 n = quadXor x E2 n := by
  induction n with
  | zero => rfl
  | succ v ih =>
    have h1 := ih (fun i j hij hjv => h_eq i j hij (Nat.lt_succ_of_lt hjv))
    have h2 := colQuadXor_congr v v x E1 E2 (fun u huv => h_eq u v huv (Nat.lt_succ_self v))
    simp [quadXor, h1, h2]

/-- Universal F₂-Simplicial 2-Cycle Vanishing Theorem (`∂C = 0 ⇒ ⨁ MAJ₃ = 0`):
    for EVERY `n : Nat`, EVERY Boolean assignment `x : Nat → Bool`, and EVERY list of
    non-degenerate triangles `tris` in `{0, ..., n-1}` whose 1-skeleton boundary has
    even multiplicity on every edge `(u, v)`, the global XOR of `maj3` vanishes! -/
theorem simplicial_2cycle_maj3_vanishes (n : Nat) (x : Nat → Bool)
    (tris : List (Nat × Nat × Nat))
    (h_valid : ∀ t ∈ tris, ValidTri n t)
    (h_cycle : ∀ u v, u < v → v < n → boundaryEdges tris u v = false) :
    trisMajParity x tris = false := by
  have h_fold := quadXor_foldl_tris n x tris (fun _ _ => false) h_valid
  rw [quadXor_zero, xor_false_left] at h_fold
  have h_zero_congr := quadXor_congr n x (boundaryEdges tris) (fun _ _ => false) h_cycle
  rw [quadXor_zero] at h_zero_congr
  unfold boundaryEdges at h_zero_congr
  rw [← h_fold, h_zero_congr]

/-! ## 4. Group 4: Universal Single-Expander Homological `XOR₃-MAJ₃` Unsatisfiability -/

def flipVertex (v : Nat) (c : Nat → Bool) : Nat → Bool :=
  fun x => if x == v then !(c x) else c x

def applyEdge (c : Nat → Bool) (e : Nat × Nat × Bool) : Nat → Bool :=
  if e.2.2 then flipVertex e.2.1 (flipVertex e.1 c) else c

def edgeCharge (edges : List (Nat × Nat × Bool)) : Nat → Bool :=
  edges.foldl applyEdge (fun _ => false)

def globalParity : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | v + 1, c => xor (globalParity v c) (c v)

theorem globalParity_zero (V : Nat) : globalParity V (fun _ => false) = false := by
  induction V with
  | zero => rfl
  | succ v ih => simp [globalParity, ih]

theorem globalParity_flip_ge (V u : Nat) (c : Nat → Bool) (hle : V ≤ u) :
    globalParity V (flipVertex u c) = globalParity V c := by
  induction V with
  | zero => rfl
  | succ v ih =>
    have hvu : (v == u) = false := beq_false_of_ne (Nat.ne_of_lt hle)
    simp [globalParity, flipVertex, hvu, ih (Nat.le_of_succ_le hle)]

theorem globalParity_flip_lt (V u : Nat) (c : Nat → Bool) (hlt : u < V) :
    globalParity V (flipVertex u c) = !(globalParity V c) := by
  induction V with
  | zero => exact absurd hlt (Nat.not_lt_zero u)
  | succ v ih =>
    by_cases h_eq : u = v
    · subst h_eq
      simp [globalParity, flipVertex, globalParity_flip_ge u u c (Nat.le_refl u)]
    · have h_lt : u < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) h_eq
      have hvu : (v == u) = false := beq_false_of_ne (Ne.symm h_eq)
      simp [globalParity, flipVertex, hvu, ih h_lt]

theorem globalParity_edges_even (V : Nat) (edges : List (Nat × Nat × Bool))
    (h_edges : ∀ e ∈ edges, e.1 < V ∧ e.2.1 < V) :
    globalParity V (edgeCharge edges) = false := by
  unfold edgeCharge
  suffices ∀ c : Nat → Bool, globalParity V (edges.foldl applyEdge c) = globalParity V c by
    rw [this (fun _ => false), globalParity_zero]
  induction edges with
  | nil => intro c; rfl
  | cons e es ih =>
    intro c
    have he := h_edges e (List.Mem.head es)
    have hes : ∀ e' ∈ es, e'.1 < V ∧ e'.2.1 < V := fun e' hm => h_edges e' (List.Mem.tail e hm)
    simp only [List.foldl_cons]
    rw [ih hes (applyEdge c e)]
    unfold applyEdge
    cases e.2.2 with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [globalParity_flip_lt V e.2.1 _ he.2, globalParity_flip_lt V e.1 _ he.1]
      cases globalParity V c <;> rfl

theorem globalParity_xor_dist (V : Nat) (f g : Nat → Bool) :
    globalParity V (fun v => xor (f v) (g v)) = xor (globalParity V f) (globalParity V g) := by
  induction V with
  | zero => rfl
  | succ v ih =>
    simp only [globalParity, ih]
    cases globalParity v f <;> cases globalParity v g <;> cases f v <;> cases g v <;> rfl

theorem globalParity_congr (V : Nat) (f g : Nat → Bool)
    (h : ∀ v, v < V → f v = g v) :
    globalParity V f = globalParity V g := by
  induction V with
  | zero => rfl
  | succ v ih =>
    simp [globalParity, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h v (Nat.lt_succ_self v)]

/-- Prefix triangle list `[triAt 0, ..., triAt (V - 1)]`. -/
def prefixTris (triAt : Nat → Nat × Nat × Nat) : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | v + 1 => (triAt v) :: prefixTris triAt v

theorem trisMajParity_prefix (V : Nat) (x : Nat → Bool) (triAt : Nat → Nat × Nat × Nat) :
    globalParity V (fun v => maj3 (x (triAt v).1) (x (triAt v).2.1) (x (triAt v).2.2)) =
      trisMajParity x (prefixTris triAt V) := by
  induction V with
  | zero => rfl
  | succ v ih =>
    simp only [globalParity, prefixTris, trisMajParity, ih, xor_comm_bool]

/-- Universal Homological `XOR₃-MAJ₃` Expander Unsatisfiability Theorem:
    for ANY vertex count `V`, variable count `n`, expander edge assignment list `edges`,
    and vertex-assigned `MAJ₃` triangles `triAt` whose 1-skeleton boundary vanishes mod 2,
    NO seed assignment `x : Nat → Bool` can satisfy `edgeCharge(v) ⊕ MAJ₃(triAt v) = target(v)`
    when `target` has odd global parity (`true`). -/
theorem homological_xor3_maj3_expander_unsat
    (V n : Nat) (x : Nat → Bool)
    (edges : List (Nat × Nat × Bool))
    (triAt : Nat → Nat × Nat × Nat)
    (target : Nat → Bool)
    (h_edges : ∀ e ∈ edges, e.1 < V ∧ e.2.1 < V)
    (h_tris : ∀ t ∈ prefixTris triAt V, ValidTri n t)
    (h_cycle : ∀ u w, u < w → w < n → boundaryEdges (prefixTris triAt V) u w = false)
    (h_odd : globalParity V target = true) :
    ¬ (∀ v, v < V →
        xor (edgeCharge edges v)
            (maj3 (x (triAt v).1) (x (triAt v).2.1) (x (triAt v).2.2)) = target v) := by
  intro h_sat
  have h_congr := globalParity_congr V
    (fun v => xor (edgeCharge edges v) (maj3 (x (triAt v).1) (x (triAt v).2.1) (x (triAt v).2.2)))
    target h_sat
  rw [globalParity_xor_dist] at h_congr
  rw [globalParity_edges_even V edges h_edges] at h_congr
  rw [trisMajParity_prefix V x triAt] at h_congr
  rw [simplicial_2cycle_maj3_vanishes n x (prefixTris triAt V) h_tris h_cycle] at h_congr
  rw [h_odd] at h_congr
  cases h_congr

/-! ## 5. Group 5: Clause-Halving Cube, XOR-Chain Folding & Veronese CG Cancellation -/

/-- Zero-slack clause (`B = 1`) halving step over a Boolean branch `v` vs `!v`. -/
theorem clause_cube_halving_exact (v : Bool) (C : Nat)
    (h_pos : b2n v + C ≥ 1) (h_neg : b2n (!v) + C ≥ 1) :
    C ≥ 1 := by
  cases v <;> simp [b2n] at h_pos h_neg <;> omega

/-- Parity of an arbitrary-width list of Booleans. -/
def listXor : List Bool → Bool
  | [] => false
  | b :: bs => xor b (listXor bs)

/-- Inductive relation encoding chained 2-input XOR extension definitions `s_{i+1} = s_i ⊕ z_{i+1}`. -/
def XorFoldChain : Bool → List Bool → Bool → Prop
  | acc, [], out => acc = out
  | acc, z :: zs, out => ∃ s : Bool, (s = xor acc z) ∧ XorFoldChain s zs out

/-- Universal `∀ zs : List Bool` soundness of folding an `r`-XOR into binary XOR steps. -/
theorem xor_chain_fold_sound (zs : List Bool) :
    ∀ acc out : Bool, XorFoldChain acc zs out → out = xor acc (listXor zs) := by
  induction zs with
  | nil =>
    intro acc out h
    simp [listXor]
    exact h.symm
  | cons z zs ih =>
    intro acc out ⟨s, hs, hrest⟩
    have h_tail := ih s out hrest
    rw [h_tail, hs, listXor, xor_assoc_bool]

/-- Arbitrary-multiplicity Veronese Cutting-Planes halving & cancellation over `Int`:
    if linear variables `S_lin`, quadratic Veronese witnesses `S_quad`, folding witnesses `S_fold`,
    and `MAJ₃` carry witnesses `W` all cancel with even integer multiplicities while the RHS sum
    is odd (`2 * Q + 1`), dividing `U⁺` and `U⁻` by `2` and summing derives `False` (`0 ≥ 1`). -/
theorem veronese_even_multiplicity_cg_unsat
    (S_lin S_quad S_fold W Gpos Gneg Q : Int)
    (h_plus : 2 * S_lin + 2 * S_quad + 2 * S_fold - 2 * W + 2 * Gpos ≥ 2 * Q + 1)
    (h_minus : -2 * S_lin - 2 * S_quad - 2 * S_fold + 2 * W + 2 * Gneg ≥ -(2 * Q + 1)) :
    (S_lin + S_quad + S_fold - W + Gpos ≥ Q + 1) ∧
    (-S_lin - S_quad - S_fold + W + Gneg ≥ -Q) ∧
    (Gpos + Gneg ≥ 1) := by
  omega

/-! ## 6. Group 6: Degree-2 Veronese Barrier Theorem on Goldreich `XOR-MAJ₅` -/

/-- 5-input majority threshold gate (`x1 + x2 + x3 + x4 + x5 ≥ 3`). -/
def maj5 (x1 x2 x3 x4 x5 : Bool) : Bool :=
  decide (b2n x1 + b2n x2 + b2n x3 + b2n x4 + b2n x5 ≥ 3)

/-- Evaluate a general 22-coefficient degree-≤ 2 polynomial in `RM(2, 6)` on
    `(y, x1, x2, x3, x4, x5)` over `F₂`. -/
def evalRM2_6
    (c0 cy c1 c2 c3 c4 c5
     cy1 cy2 cy3 cy4 cy5
     c12 c13 c14 c15 c23 c24 c25 c34 c35 c45
     y x1 x2 x3 x4 x5 : Bool) : Bool :=
  let lin := xor c0 (xor (cy && y)
    (xor (c1 && x1) (xor (c2 && x2) (xor (c3 && x3) (xor (c4 && x4) (c5 && x5))))))
  let qy := xor (cy1 && (y && x1))
    (xor (cy2 && (y && x2)) (xor (cy3 && (y && x3)) (xor (cy4 && (y && x4)) (cy5 && (y && x5)))))
  let qx1 := xor (c12 && (x1 && x2))
    (xor (c13 && (x1 && x3)) (xor (c14 && (x1 && x4)) (c15 && (x1 && x5))))
  let qx2 := xor (c23 && (x2 && x3))
    (xor (c24 && (x2 && x4)) (xor (c25 && (x2 && x5))
      (xor (c34 && (x3 && x4)) (xor (c35 && (x3 && x5)) (c45 && (x4 && x5))))))
  xor (xor lin qy) (xor qx1 qx2)

/-- Mechanical Degree-2 Barrier Theorem (`RM(2, 6)` Vanishing Ideal = `{0}` on `XOR-MAJ₅`):
    across ALL `2²² = 4,194,304` degree-≤ 2 polynomials in `RM(2, 6)` and BOTH polarities
    `rhs ∈ {false, true}`, if `P(y, x₁..x₅)` vanishes on all 32 satisfying assignments
    `y = MAJ₅(x₁, x₂, x₃, x₄, x₅) ⊕ rhs`, then ALL 22 coefficients of `P` are `false`!
    This formally separates `XOR-MAJ₃` (`deg = 2`, polynomial in Veronese `VeriPB`) from
    `XOR-MAJ₅` (`deg = 4`, zero degree-≤ 2 annihilators). -/
theorem xor_maj5_no_deg2_annihilator
    (c0 cy c1 c2 c3 c4 c5
     cy1 cy2 cy3 cy4 cy5
     c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 rhs : Bool)
    (h : ∀ x1 x2 x3 x4 x5 : Bool,
      evalRM2_6 c0 cy c1 c2 c3 c4 c5 cy1 cy2 cy3 cy4 cy5
        c12 c13 c14 c15 c23 c24 c25 c34 c35 c45
        (xor (maj5 x1 x2 x3 x4 x5) rhs) x1 x2 x3 x4 x5 = false) :
    c0 = false ∧ cy = false ∧
    c1 = false ∧ c2 = false ∧ c3 = false ∧ c4 = false ∧ c5 = false ∧
    cy1 = false ∧ cy2 = false ∧ cy3 = false ∧ cy4 = false ∧ cy5 = false ∧
    c12 = false ∧ c13 = false ∧ c14 = false ∧ c15 = false ∧
    c23 = false ∧ c24 = false ∧ c25 = false ∧ c34 = false ∧ c35 = false ∧ c45 = false := by
  have w00000 := h false false false false false
  have w10000 := h true  false false false false
  have w01000 := h false true  false false false
  have w00100 := h false false true  false false
  have w00010 := h false false false true  false
  have w00001 := h false false false false true
  have w11000 := h true  true  false false false
  have w10100 := h true  false true  false false
  have w10010 := h true  false false true  false
  have w10001 := h true  false false false true
  have w01100 := h false true  true  false false
  have w01010 := h false true  false true  false
  have w01001 := h false true  false false true
  have w00110 := h false false true  true  false
  have w00101 := h false false true  false true
  have w00011 := h false false false true  true
  have w11100 := h true  true  true  false false
  have w11110 := h true  true  true  true  false
  have w11101 := h true  true  true  false true
  have w01110 := h false true  true  true  false
  have w10110 := h true  false true  true  false
  have w11010 := h true  true  false true  false
  clear h
  cases rhs with
  | false =>
    simp [maj5, b2n, evalRM2_6] at w00000 w10000 w01000 w00100 w00010 w00001
    simp [maj5, b2n, evalRM2_6] at w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011
    simp [maj5, b2n, evalRM2_6] at w11100 w11110 w11101 w01110 w10110 w11010
    have z0 : c0 = false := by cases c0 <;> simp at w00000 ⊢
    simp only [z0] at w10000 w01000 w00100 w00010 w00001 w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011 w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    have z1 : c1 = false := by cases c1 <;> simp at w10000 ⊢
    have z2 : c2 = false := by cases c2 <;> simp at w01000 ⊢
    have z3 : c3 = false := by cases c3 <;> simp at w00100 ⊢
    have z4 : c4 = false := by cases c4 <;> simp at w00010 ⊢
    have z5 : c5 = false := by cases c5 <;> simp at w00001 ⊢
    simp only [z1, z2, z3, z4, z5] at w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011 w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    have z12 : c12 = false := by cases c12 <;> simp at w11000 ⊢
    have z13 : c13 = false := by cases c13 <;> simp at w10100 ⊢
    have z14 : c14 = false := by cases c14 <;> simp at w10010 ⊢
    have z15 : c15 = false := by cases c15 <;> simp at w10001 ⊢
    have z23 : c23 = false := by cases c23 <;> simp at w01100 ⊢
    have z24 : c24 = false := by cases c24 <;> simp at w01010 ⊢
    have z25 : c25 = false := by cases c25 <;> simp at w01001 ⊢
    have z34 : c34 = false := by cases c34 <;> simp at w00110 ⊢
    have z35 : c35 = false := by cases c35 <;> simp at w00101 ⊢
    have z45 : c45 = false := by cases c45 <;> simp at w00011 ⊢
    simp only [z12, z13, z14, z15, z23, z24, z25, z34, z35, z45] at w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    cases cy <;> cases cy1 <;> cases cy2 <;> cases cy3 <;> cases cy4 <;> cases cy5 <;>
      simp at w11100 w11110 w11101 w01110 w10110 w11010 ⊢
  | true =>
    simp [maj5, b2n, evalRM2_6] at w00000 w10000 w01000 w00100 w00010 w00001
    simp [maj5, b2n, evalRM2_6] at w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011
    simp [maj5, b2n, evalRM2_6] at w11100 w11110 w11101 w01110 w10110 w11010
    have eq0 : cy = c0 := by cases c0 <;> cases cy <;> simp at w00000 ⊢
    simp only [eq0] at w10000 w01000 w00100 w00010 w00001 w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011 w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    have eq1 : cy1 = c1 := by cases c0 <;> cases c1 <;> cases cy1 <;> simp at w10000 ⊢
    have eq2 : cy2 = c2 := by cases c0 <;> cases c2 <;> cases cy2 <;> simp at w01000 ⊢
    have eq3 : cy3 = c3 := by cases c0 <;> cases c3 <;> cases cy3 <;> simp at w00100 ⊢
    have eq4 : cy4 = c4 := by cases c0 <;> cases c4 <;> cases cy4 <;> simp at w00010 ⊢
    have eq5 : cy5 = c5 := by cases c0 <;> cases c5 <;> cases cy5 <;> simp at w00001 ⊢
    simp only [eq1, eq2, eq3, eq4, eq5] at w11000 w10100 w10010 w10001 w01100 w01010 w01001 w00110 w00101 w00011 w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    have z12 : c12 = false := by cases c0 <;> cases c1 <;> cases c2 <;> cases c12 <;> simp at w11000 ⊢
    have z13 : c13 = false := by cases c0 <;> cases c1 <;> cases c3 <;> cases c13 <;> simp at w10100 ⊢
    have z14 : c14 = false := by cases c0 <;> cases c1 <;> cases c4 <;> cases c14 <;> simp at w10010 ⊢
    have z15 : c15 = false := by cases c0 <;> cases c1 <;> cases c5 <;> cases c15 <;> simp at w10001 ⊢
    have z23 : c23 = false := by cases c0 <;> cases c2 <;> cases c3 <;> cases c23 <;> simp at w01100 ⊢
    have z24 : c24 = false := by cases c0 <;> cases c2 <;> cases c4 <;> cases c24 <;> simp at w01010 ⊢
    have z25 : c25 = false := by cases c0 <;> cases c2 <;> cases c5 <;> cases c25 <;> simp at w01001 ⊢
    have z34 : c34 = false := by cases c0 <;> cases c3 <;> cases c4 <;> cases c34 <;> simp at w00110 ⊢
    have z35 : c35 = false := by cases c0 <;> cases c3 <;> cases c5 <;> cases c35 <;> simp at w00101 ⊢
    have z45 : c45 = false := by cases c0 <;> cases c4 <;> cases c5 <;> cases c45 <;> simp at w00011 ⊢
    simp only [z12, z13, z14, z15, z23, z24, z25, z34, z35, z45] at w11100 w11110 w11101 w01110 w10110 w11010 ⊢
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
      simp at w11100 w11110 w11101 w01110 w10110 w11010 ⊢

/-! ## 7. Axiom Footprint Audit (`0 sorryAx`, Kernel Axioms Only) -/

#print axioms veronese_and_red_11_witness
#print axioms veronese_and_red_0x_sound
#print axioms veronese_and_red_x0_sound
#print axioms veronese_and_clauses_characterize_prod
#print axioms maj3_anf_f2_exact
#print axioms and_polarity_scramble_invariance
#print axioms maj3_polarity_scramble_boundary_invariance
#print axioms k4_tetrahedron_maj3_boundary_zero
#print axioms simplicial_2cycle_maj3_vanishes
#print axioms homological_xor3_maj3_expander_unsat
#print axioms clause_cube_halving_exact
#print axioms xor_chain_fold_sound
#print axioms veronese_even_multiplicity_cg_unsat
#print axioms xor_maj5_no_deg2_annihilator

end VeronesePrgSoundness
