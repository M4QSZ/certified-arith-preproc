/-
  Soundness of VeriPB 3.0 Blind Disjunctive Interpolant Calculus
  ================================================================
  Standalone Lean 4.36.0 formalization (zero Mathlib imports, zero external axioms,
  zero `sorry`) covering:
    1. Boolean-to-Nat embedding (`b2n`) and negation identities.
    2. Theorem 1: `(1,1)`-chain resolution unrolling in Cutting Planes
       (`chain11_pb_cancel_sound` and inductive `chain11_unroll_steps_sound`).
    3. Theorem 2: Guarded At-Most-One (AMO) Chvátal-Gomory step
       (`guarded_amo_cg_step_sound`, CG ceiling division identity, and `G = 0` / general consequence).
    4. Theorem 3: Universal `∀ p h` Pigeonhole guarded Cutting-Planes soundness
       (`guarded_php_unsat_derives_guard`).
    5. Theorem 4: `maj3` witness exactness (`maj3_witness_exact_xor_z`), `red` witness
       validity, and guarded 3-XOR parity Cutting-Planes derivation (`guarded_parity3_veripb_sound`).
    6. Theorem 5: Even-coefficient Chvátal-Gomory halving & cancellation over `Int`
       (`even_coeff_cg_halving_cancel_sound`).
    7. Theorem 6: Tseitin graph handshaking parity invariance over arbitrary edge lists
       (`tseitin_graph_handshaking_parity`).
    8. Theorem 7: Boolean cube halving unsatisfiability over `Fin k`
       (`boolean_cube_halving_unsat`).
-/

namespace DisjunctiveInterpolantSoundness

/-! ## 1. Boolean-to-Nat Embedding -/

/-- Embed `Bool` into `Nat` (`true ↦ 1`, `false ↦ 0`). -/
def b2n (b : Bool) : Nat :=
  if b then 1 else 0

@[simp]
theorem b2n_not (b : Bool) : b2n (!b) = 1 - b2n b := by
  cases b <;> rfl

@[simp]
theorem b2n_add_not (b : Bool) : b2n b + b2n (!b) = 1 := by
  cases b <;> rfl

theorem b2n_le_one (b : Bool) : b2n b ≤ 1 := by
  cases b <;> decide

/-! ## 2. Theorem 1: `(1,1)`-Chain Resolution Unrolling in Cutting Planes -/

/-- Single `(1,1)`-chain Cutting-Planes cancellation step. -/
theorem chain11_pb_cancel_sound (a b : Nat) (v : Bool)
    (h1 : a + b2n v ≥ 1) (h2 : b2n (!v) + b ≥ 1) :
    a + b ≥ 1 := by
  cases v <;> simp [b2n] at h1 h2 <;> omega

/-- Inductive predicate for a chain of `k` `(1,1)`-clauses linking `a` to `b`
    via pivot booleans `vs`. -/
def chain11_links : Nat → List Bool → Nat → Prop
  | a, [], b => a + b ≥ 1
  | a, v :: vs, b => (a + b2n v ≥ 1) ∧ chain11_links (b2n (!v)) vs b

/-- Inductive soundness of unrolling `k = vs.length` chained `(1,1)`-resolution steps. -/
theorem chain11_unroll_steps_sound (vs : List Bool) :
    ∀ a b : Nat, chain11_links a vs b → a + b ≥ 1 := by
  induction vs with
  | nil =>
    intro a b h
    exact h
  | cons v vs ih =>
    intro a b h
    have h_tail : b2n (!v) + b ≥ 1 := ih (b2n (!v)) b h.2
    exact chain11_pb_cancel_sound a b v h.1 h_tail

/-! ## 3. Theorem 2: Guarded AMO Chvátal-Gomory Step -/

/-- Exact Chvátal-Gomory combination of the inductive guarded AMO on `m` literals
    and the sum of `m` pairwise guarded clauses with `x_new`.
    Note: the tight lower bound is `(m - 1) * (m - 1) + m = m * m - m + 1`
    (witnessed e.g. at `m = 3, G = 1, s = 0, x_new = true` where LHS = 7). -/
theorem guarded_amo_cg_step_sound (m G s : Nat) (x_new : Bool)
    (_hm : m ≥ 1)
    (h_amo : (m - 1) * G + s ≥ m - 1)
    (_h_pair : m * G + s + m * b2n (!x_new) ≥ m) :
    (m - 1) * ((m - 1) * G + s) + (m * G + s + m * b2n (!x_new)) ≥
      (m - 1) * (m - 1) + m := by
  have h1 : (m - 1) * ((m - 1) * G + s) ≥ (m - 1) * (m - 1) :=
    Nat.mul_le_mul_left (m - 1) h_amo
  omega

/-- Exact Chvátal-Gomory ceiling division identity over `Nat`:
    `⌈(m^2 - m + 1) / m⌉ = m` for all `m ≥ 1`. -/
theorem cg_ceiling_div_id (m : Nat) (hm : m ≥ 1) :
    (m * m - m + 1 + m - 1) / m = m := by
  have h_le : m ≤ m * m := by
    calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * m := Nat.mul_le_mul_left m hm
  have h_eq : m * m - m + 1 + m - 1 = m * m := by omega
  rw [h_eq, Nat.mul_div_right m hm]

/-- When `G = 0` and `x_new = true`, the guarded AMO CG step forces `s ≥ m`. -/
theorem guarded_amo_cg_G0_xnew_true (m s : Nat)
    (_hm : m ≥ 1)
    (h_pair : m * 0 + s + m * b2n (!true) ≥ m) :
    s ≥ m := by
  simp [b2n] at h_pair
  exact h_pair

/-- Full guarded AMO step combining `h_amo` and `h_pair` to derive
    `m * G + (s + b2n (!x_new)) ≥ m` for all `m ≥ 1, G, s : Nat, x_new : Bool`. -/
theorem guarded_amo_step_full (m G s : Nat) (x_new : Bool)
    (_hm : m ≥ 1)
    (h_amo : (m - 1) * G + s ≥ m - 1)
    (h_pair : m * G + s + m * b2n (!x_new) ≥ m) :
    m * G + (s + b2n (!x_new)) ≥ m := by
  cases G with
  | zero =>
    simp at h_amo h_pair ⊢
    cases x_new <;> simp [b2n] at h_pair ⊢ <;> omega
  | succ G' =>
    have h_mG : m * (G' + 1) ≥ m := by
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ m * (G' + 1) := Nat.mul_le_mul_left m (Nat.succ_le_succ (Nat.zero_le G'))
    omega

/-! ## 4. Theorem 3: Universal Pigeonhole Guarded Cutting-Planes Soundness -/

/-- Universal `∀ p h` Pigeonhole Principle guarded Cutting-Planes soundness:
    combining `p` guarded pigeon ALO clauses and `h` guarded hole AMO inequalities
    derives `(p + h * (p - 1)) * G ≥ p - h` and hence `G ≥ 1`. -/
theorem guarded_php_unsat_derives_guard
    (p h G total_ones total_zeros : Nat)
    (hp_lt : h < p)
    (h_sum : total_ones + total_zeros = p * h)
    (h_alo : p * G + total_ones ≥ p)
    (h_amo : h * (p - 1) * G + total_zeros ≥ h * (p - 1)) :
    (p + h * (p - 1)) * G ≥ p - h ∧ G ≥ 1 := by
  have hp1 : 1 ≤ p := Nat.lt_of_le_of_lt (Nat.zero_le h) hp_lt
  have h_add :
      (p + h * (p - 1)) * G + (total_ones + total_zeros) ≥ p + h * (p - 1) := by
    have h_dist : (p + h * (p - 1)) * G = p * G + h * (p - 1) * G :=
      Nat.add_mul p (h * (p - 1)) G
    omega
  have h_ph : h * (p - 1) + h = p * h := by
    calc h * (p - 1) + h = h * (p - 1) + h * 1 := by rw [Nat.mul_one]
      _ = h * (p - 1 + 1) := (Nat.mul_add h (p - 1) 1).symm
      _ = h * p := by rw [Nat.sub_add_cancel hp1]
      _ = p * h := Nat.mul_comm h p
  have h_cancel : (p + h * (p - 1)) * G ≥ p - h := by
    omega
  have h_G : G ≥ 1 := by
    cases G with
    | zero =>
      rw [Nat.mul_zero] at h_cancel
      omega
    | succ G' =>
      exact Nat.succ_le_succ (Nat.zero_le G')
  exact ⟨h_cancel, h_G⟩

/-! ## 5. Theorem 4: `maj3` Witness & Guarded 3-XOR Parity VeriPB Soundness -/

/-- 3-input majority gate. -/
def maj3 (y1 y2 y3 : Bool) : Bool :=
  (y1 && y2) || (y1 && y3) || (y2 && y3)

/-- Exact arithmetic decomposition:
    `y1 + y2 + y3 = 2 * maj3(y1, y2, y3) + (y1 ⊕ y2 ⊕ y3)`. -/
theorem maj3_witness_exact_xor_z (y1 y2 y3 : Bool) :
    b2n y1 + b2n y2 + b2n y3 =
      2 * b2n (maj3 y1 y2 y3) + b2n (xor (xor y1 y2) y3) := by
  cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- Witness `red` validity for `w = false`. -/
theorem parity3_red_witness_false (y1 y2 y3 : Bool) :
    b2n y1 + b2n y2 + b2n y3 + 2 * b2n (!false) ≥ 2 := by
  simp [b2n]

/-- Witness `red` validity for `w = true`. -/
theorem parity3_red_witness_true (y1 y2 y3 : Bool) :
    b2n (!y1) + b2n (!y2) + b2n (!y3) + 2 * b2n true ≥ 2 := by
  simp [b2n]

/-- Guarded 3-XOR parity Cutting-Planes derivation:
    from `R2` and the 4 guarded parity clauses, derives each `L_i` and the
    combined guarded inequality `3 * G + !y1 + !y2 + !y3 + 2 * w ≥ 3`. -/
theorem guarded_parity3_veripb_sound (G : Nat) (y1 y2 y3 w : Bool)
    (hR2 : b2n (!y1) + b2n (!y2) + b2n (!y3) + 2 * b2n w ≥ 2)
    (hC1 : G + b2n (!y1) + b2n y2 + b2n y3 ≥ 1)
    (hC2 : G + b2n y1 + b2n (!y2) + b2n y3 ≥ 1)
    (hC3 : G + b2n y1 + b2n y2 + b2n (!y3) ≥ 1)
    (hC4 : G + b2n (!y1) + b2n (!y2) + b2n (!y3) ≥ 1) :
    (G + b2n (!y1) + b2n w ≥ 1) ∧
    (G + b2n (!y2) + b2n w ≥ 1) ∧
    (G + b2n (!y3) + b2n w ≥ 1) ∧
    (3 * G + b2n (!y1) + b2n (!y2) + b2n (!y3) + 2 * b2n w ≥ 3) := by
  cases y1 <;> cases y2 <;> cases y3 <;> cases w <;>
    simp [b2n] at hR2 hC1 hC2 hC3 hC4 ⊢ <;> omega

/-! ## 6. Theorem 5: Even-Coefficient CG Halving & Cancellation over `Int` -/

/-- Even-coefficient Chvátal-Gomory halving and cancellation over `Int`. -/
theorem even_coeff_cg_halving_cancel_sound (S W Gpos Gneg Q : Int)
    (h1 : 2 * S - 2 * W + 2 * Gpos ≥ 2 * Q + 1)
    (h2 : -2 * S + 2 * W + 2 * Gneg ≥ -(2 * Q + 1)) :
    (S - W + Gpos ≥ Q + 1) ∧
    (-S + W + Gneg ≥ -Q) ∧
    (Gpos + Gneg ≥ 1) := by
  omega

/-! ## 7. Theorem 6: Tseitin Graph Handshaking Parity Invariance -/

/-- Flip the charge of vertex `v` in a vertex-charge map `c`. -/
def flipVertex (v : Nat) (c : Nat → Bool) : Nat → Bool :=
  fun x => if x == v then !(c x) else c x

/-- Apply a Tseitin edge `(u, v, active)`: if `active = true`, flip both endpoints. -/
def applyEdge (c : Nat → Bool) (e : Nat × Nat × Bool) : Nat → Bool :=
  if e.2.2 then flipVertex e.2.1 (flipVertex e.1 c) else c

/-- Vertex charges induced by folding an arbitrary list of edge assignments. -/
def edgeCharge (edges : List (Nat × Nat × Bool)) : Nat → Bool :=
  edges.foldl applyEdge (fun _ => false)

/-- Global XOR parity of a charge map over vertices `0, 1, ..., n - 1`. -/
def globalParity : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, c => xor (globalParity n c) (c n)

theorem globalParity_zero (n : Nat) :
    globalParity n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [globalParity, ih]

theorem globalParity_flipVertex_of_ge (n v : Nat) (c : Nat → Bool) (hv : n ≤ v) :
    globalParity n (flipVertex v c) = globalParity n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : (n == v) = false := beq_false_of_ne (Nat.ne_of_lt hv)
    have ih' := ih (Nat.le_of_succ_le hv)
    simp [globalParity, flipVertex, hnv, ih']

theorem globalParity_flipVertex_of_lt (n v : Nat) (c : Nat → Bool) (hv : v < n) :
    globalParity n (flipVertex v c) = !(globalParity n c) := by
  induction n with
  | zero => exact absurd hv (Nat.not_lt_zero v)
  | succ n ih =>
    by_cases h_eq : v = n
    · subst h_eq
      have h_ge : globalParity v (flipVertex v c) = globalParity v c :=
        globalParity_flipVertex_of_ge v v c (Nat.le_refl v)
      simp [globalParity, flipVertex, h_ge]
    · have h_lt : v < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hv) h_eq
      have h_nv : (n == v) = false := beq_false_of_ne (Ne.symm h_eq)
      have ih' := ih h_lt
      simp [globalParity, flipVertex, h_nv, ih']

theorem globalParity_applyEdge (n : Nat) (c : Nat → Bool) (e : Nat × Nat × Bool)
    (he1 : e.1 < n) (he2 : e.2.1 < n) :
    globalParity n (applyEdge c e) = globalParity n c := by
  unfold applyEdge
  cases e.2.2 with
  | false => rfl
  | true =>
    simp
    rw [globalParity_flipVertex_of_lt n e.2.1 (flipVertex e.1 c) he2]
    rw [globalParity_flipVertex_of_lt n e.1 c he1]
    cases globalParity n c <;> rfl

theorem globalParity_foldl_applyEdge (n : Nat) (edges : List (Nat × Nat × Bool))
    (c : Nat → Bool)
    (h_edges : ∀ e ∈ edges, e.1 < n ∧ e.2.1 < n) :
    globalParity n (edges.foldl applyEdge c) = globalParity n c := by
  induction edges generalizing c with
  | nil => rfl
  | cons e es ih =>
    have he := h_edges e (List.Mem.head es)
    have hes : ∀ e' ∈ es, e'.1 < n ∧ e'.2.1 < n :=
      fun e' hm => h_edges e' (List.Mem.tail e hm)
    simp only [List.foldl_cons]
    rw [ih (applyEdge c e) hes]
    exact globalParity_applyEdge n c e he.1 he.2

theorem globalParity_congr (n : Nat) (c1 c2 : Nat → Bool)
    (h_eq : ∀ v, v < n → c1 v = c2 v) :
    globalParity n c1 = globalParity n c2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (fun v hv => h_eq v (Nat.lt_succ_of_lt hv))
    have h2 := h_eq n (Nat.lt_succ_self n)
    simp [globalParity, h1, h2]

/-- Tseitin graph handshaking parity theorem:
    (a) For any edge list whose endpoints lie in `{0, ..., n - 1}`, the induced
        global XOR parity is `false`.
    (b) Consequently, no target charge assignment with odd global parity (`true`)
        can agree with the induced edge-incident parities on `{0, ..., n - 1}`. -/
theorem tseitin_graph_handshaking_parity (n : Nat) (edges : List (Nat × Nat × Bool))
    (h_edges : ∀ e ∈ edges, e.1 < n ∧ e.2.1 < n) :
    globalParity n (edgeCharge edges) = false ∧
    ∀ target : Nat → Bool, globalParity n target = true →
      ¬ (∀ v, v < n → edgeCharge edges v = target v) := by
  have h_even : globalParity n (edgeCharge edges) = false := by
    unfold edgeCharge
    rw [globalParity_foldl_applyEdge n edges (fun _ => false) h_edges]
    exact globalParity_zero n
  refine ⟨h_even, ?_⟩
  intro target h_odd h_agree
  have h_congr := globalParity_congr n (edgeCharge edges) target h_agree
  rw [h_even, h_odd] at h_congr
  cases h_congr

/-! ## 8. Theorem 7: Boolean Cube Halving Unsatisfiability -/

/-- Single term in the cube-halving guard sum. -/
def cubeTerm (a p : Bool) : Nat :=
  if p then b2n (!a) else b2n a

theorem cubeTerm_self (a : Bool) : cubeTerm a a = 0 := by
  cases a <;> rfl

/-- Sum over `i : Fin k` of `if pat i then b2n (!(assign i)) else b2n (assign i)`. -/
def cubeGuardSat : (k : Nat) → (Fin k → Bool) → (Fin k → Bool) → Nat
  | 0, _, _ => 0
  | k + 1, assign, pat =>
    cubeTerm (assign ⟨k, Nat.lt_succ_self k⟩) (pat ⟨k, Nat.lt_succ_self k⟩) +
      cubeGuardSat k (fun i => assign ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                     (fun i => pat ⟨i.1, Nat.lt_succ_of_lt i.2⟩)

/-- Inductive lemma: choosing `pat = assign` yields `cubeGuardSat k assign assign = 0`. -/
theorem cubeGuardSat_self (k : Nat) :
    ∀ assign : Fin k → Bool, cubeGuardSat k assign assign = 0 := by
  induction k with
  | zero =>
    intro assign
    rfl
  | succ k ih =>
    intro assign
    simp only [cubeGuardSat]
    rw [cubeTerm_self (assign ⟨k, Nat.lt_succ_self k⟩)]
    rw [ih (fun i => assign ⟨i.1, Nat.lt_succ_of_lt i.2⟩)]

/-- Boolean cube halving unsatisfiability:
    for every `k : Nat` and `assign : Fin k → Bool`, there exists `pat : Fin k → Bool`
    such that `cubeGuardSat k assign pat = 0`, and hence
    `(∀ pat : Fin k → Bool, cubeGuardSat k assign pat ≥ 1) → False`. -/
theorem boolean_cube_halving_unsat (k : Nat) (assign : Fin k → Bool) :
    (∃ pat : Fin k → Bool, cubeGuardSat k assign pat = 0) ∧
    ((∀ pat : Fin k → Bool, cubeGuardSat k assign pat ≥ 1) → False) := by
  refine ⟨⟨assign, cubeGuardSat_self k assign⟩, ?_⟩
  intro h_all
  have h0 := cubeGuardSat_self k assign
  have h1 := h_all assign
  omega

/-! ## 9. Axiom Audit -/

#print axioms b2n_not
#print axioms b2n_add_not
#print axioms chain11_pb_cancel_sound
#print axioms chain11_unroll_steps_sound
#print axioms guarded_amo_cg_step_sound
#print axioms cg_ceiling_div_id
#print axioms guarded_amo_cg_G0_xnew_true
#print axioms guarded_amo_step_full
#print axioms guarded_php_unsat_derives_guard
#print axioms maj3_witness_exact_xor_z
#print axioms parity3_red_witness_false
#print axioms parity3_red_witness_true
#print axioms guarded_parity3_veripb_sound
#print axioms even_coeff_cg_halving_cancel_sound
#print axioms tseitin_graph_handshaking_parity
#print axioms cubeGuardSat_self
#print axioms boolean_cube_halving_unsat

end DisjunctiveInterpolantSoundness
