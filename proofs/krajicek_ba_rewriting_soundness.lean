/-!
# Formal Soundness & Modus Ponens Simulation for Krajíček's BA Rewrite Proof System

Formalization of Jan Krajíček, "Extended Frege proofs, circuits and rewriting"
(`arXiv:2606.13367v2`, version 11.X.2026):
- Section 1: DeMorgan language `{0, 1, ¬, ∨, ∧}` and Boolean evaluation.
- Section 2: The 12 Boolean Algebra equations `BA` (lines 274-288),
  local single-occurrence replacement `s ~_BA t` at a path `p : List Bool` (lines 388-406),
  and its reflexive-transitive closure `s ~_BA^* t`.
- Lemma 2.1 (`Lemma \ref{8.10.26b}`, lines 354-371): Constant-overhead Modus Ponens
  simulation in `~_BA^*` (and exact step-counted bound `k₁ + k₂ + 2` in `SimBAN`).

Zero imports, zero `sorry`, audited via `#print axioms`.
-/

namespace KrajicekBARewriting

/-- Terms in the DeMorgan language `{0, 1, ¬, ∨, ∧}` with variables indexed by `Nat`. -/
inductive DeMorganTerm : Type where
  | zero : DeMorganTerm
  | one  : DeMorganTerm
  | var  : Nat → DeMorganTerm
  | neg  : DeMorganTerm → DeMorganTerm
  | disj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  | conj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  deriving DecidableEq, Repr

/-- Standard Boolean evaluation of a DeMorgan term under an assignment `env`. -/
def evalTerm (env : Nat → Bool) : DeMorganTerm → Bool
  | .zero     => false
  | .one      => true
  | .var i    => env i
  | .neg a    => !(evalTerm env a)
  | .disj a b => (evalTerm env a) || (evalTerm env b)
  | .conj a b => (evalTerm env a) && (evalTerm env b)

/-- The 12 Boolean Algebra axiom schemes `BA` from Krajíček `rewrite.tex` Sec. 2 (lines 274-288). -/
inductive BAAxiom : DeMorganTerm → DeMorganTerm → Prop where
  | negZero       : BAAxiom (.neg .zero) .one
  | negOne        : BAAxiom (.neg .one) .zero
  | disjZeroLeft  (a : DeMorganTerm) : BAAxiom (.disj .zero a) a
  | conjOneLeft   (a : DeMorganTerm) : BAAxiom (.conj .one a) a
  | disjCompl     (a : DeMorganTerm) : BAAxiom (.disj a (.neg a)) .one
  | conjCompl     (a : DeMorganTerm) : BAAxiom (.conj a (.neg a)) .zero
  | disjComm      (a b : DeMorganTerm) : BAAxiom (.disj a b) (.disj b a)
  | conjComm      (a b : DeMorganTerm) : BAAxiom (.conj a b) (.conj b a)
  | disjAssoc     (a b c : DeMorganTerm) : BAAxiom (.disj a (.disj b c)) (.disj (.disj a b) c)
  | conjAssoc     (a b c : DeMorganTerm) : BAAxiom (.conj a (.conj b c)) (.conj (.conj a b) c)
  | disjDistrib   (a b c : DeMorganTerm) : BAAxiom (.disj a (.conj b c)) (.conj (.disj a b) (.disj a c))
  | conjDistrib   (a b c : DeMorganTerm) : BAAxiom (.conj a (.disj b c)) (.disj (.conj a b) (.conj a c))

/-- Bidirectional root BA step: `u = v` or `v = u` is an instance of one of the 12 BA axioms. -/
inductive BAStep : DeMorganTerm → DeMorganTerm → Prop where
  | fwd {s t : DeMorganTerm} : BAAxiom s t → BAStep s t
  | bwd {s t : DeMorganTerm} : BAAxiom t s → BAStep s t

theorem baStep_symm {s t : DeMorganTerm} (h : BAStep s t) : BAStep t s := by
  cases h with
  | fwd ha => exact .bwd ha
  | bwd ha => exact .fwd ha

/-- Single-occurrence context replacement `s ~_BA t` at an explicit path `p : List Bool`.
    - `[]`: apply `BAStep` at the root.
    - `false :: p`: descend into the sole child of `neg`, or the left child of `disj`/`conj`.
    - `true :: p`: descend into the right child of `disj`/`conj`. -/
inductive SimBAPath : List Bool → DeMorganTerm → DeMorganTerm → Prop where
  | root      {s t : DeMorganTerm} :
      BAStep s t → SimBAPath [] s t
  | neg       {p : List Bool} {s t : DeMorganTerm} :
      SimBAPath p s t → SimBAPath (false :: p) (.neg s) (.neg t)
  | disjLeft  {p : List Bool} {s₁ t₁ s₂ : DeMorganTerm} :
      SimBAPath p s₁ t₁ → SimBAPath (false :: p) (.disj s₁ s₂) (.disj t₁ s₂)
  | disjRight {p : List Bool} {s₁ s₂ t₂ : DeMorganTerm} :
      SimBAPath p s₂ t₂ → SimBAPath (true :: p) (.disj s₁ s₂) (.disj s₁ t₂)
  | conjLeft  {p : List Bool} {s₁ t₁ s₂ : DeMorganTerm} :
      SimBAPath p s₁ t₁ → SimBAPath (false :: p) (.conj s₁ s₂) (.conj t₁ s₂)
  | conjRight {p : List Bool} {s₁ s₂ t₂ : DeMorganTerm} :
      SimBAPath p s₂ t₂ → SimBAPath (true :: p) (.conj s₁ s₂) (.conj s₁ t₂)

theorem simBAPath_symm {p : List Bool} {s t : DeMorganTerm}
    (h : SimBAPath p s t) : SimBAPath p t s := by
  induction h with
  | root hb => exact .root (baStep_symm hb)
  | neg _ ih => exact .neg ih
  | disjLeft _ ih => exact .disjLeft ih
  | disjRight _ ih => exact .disjRight ih
  | conjLeft _ ih => exact .conjLeft ih
  | conjRight _ ih => exact .conjRight ih

/-- Local single-occurrence BA replacement `s ~_BA t` (existentially quantifying the path `p`). -/
def SimBA (s t : DeMorganTerm) : Prop :=
  ∃ p : List Bool, SimBAPath p s t

theorem simBA_symm {s t : DeMorganTerm} (h : SimBA s t) : SimBA t s :=
  let ⟨p, hp⟩ := h
  ⟨p, simBAPath_symm hp⟩

/-- Reflexive-transitive closure `s ~_BA^* t`. -/
inductive SimBAStar : DeMorganTerm → DeMorganTerm → Prop where
  | refl (s : DeMorganTerm) : SimBAStar s s
  | step {s u t : DeMorganTerm} : SimBA s u → SimBAStar u t → SimBAStar s t

/-- Step-counted reflexive-transitive closure: `SimBAN n s t` holds iff `s` rewrites to `t`
    in exactly `n` single-occurrence `SimBA` steps. -/
inductive SimBAN : Nat → DeMorganTerm → DeMorganTerm → Prop where
  | zero (s : DeMorganTerm) : SimBAN 0 s s
  | succ {n : Nat} {s u t : DeMorganTerm} :
      SimBA s u → SimBAN n u t → SimBAN (n + 1) s t

/-! ## Soundness of `BAAxiom`, `BAStep`, `SimBAPath`, `SimBA`, `SimBAStar`, and `SimBAN` -/

theorem baAxiom_sound (s t : DeMorganTerm) (env : Nat → Bool)
    (h : BAAxiom s t) : evalTerm env s = evalTerm env t := by
  cases h with
  | negZero => rfl
  | negOne => rfl
  | disjZeroLeft a =>
      rfl
  | conjOneLeft a =>
      rfl
  | disjCompl a =>
      dsimp [evalTerm]; cases evalTerm env a <;> rfl
  | conjCompl a =>
      dsimp [evalTerm]; cases evalTerm env a <;> rfl
  | disjComm a b =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> rfl
  | conjComm a b =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> rfl
  | disjAssoc a b c =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> cases evalTerm env c <;> rfl
  | conjAssoc a b c =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> cases evalTerm env c <;> rfl
  | disjDistrib a b c =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> cases evalTerm env c <;> rfl
  | conjDistrib a b c =>
      dsimp [evalTerm]; cases evalTerm env a <;> cases evalTerm env b <;> cases evalTerm env c <;> rfl

theorem baStep_sound (s t : DeMorganTerm) (env : Nat → Bool)
    (h : BAStep s t) : evalTerm env s = evalTerm env t := by
  cases h with
  | fwd ha => exact baAxiom_sound _ _ env ha
  | bwd ha => exact (baAxiom_sound _ _ env ha).symm

theorem simBAPath_sound (p : List Bool) (s t : DeMorganTerm) (env : Nat → Bool)
    (h : SimBAPath p s t) : evalTerm env s = evalTerm env t := by
  induction h with
  | root hb =>
      exact baStep_sound _ _ env hb
  | neg _ ih =>
      dsimp [evalTerm]; rw [ih]
  | disjLeft _ ih =>
      dsimp [evalTerm]; rw [ih]
  | disjRight _ ih =>
      dsimp [evalTerm]; rw [ih]
  | conjLeft _ ih =>
      dsimp [evalTerm]; rw [ih]
  | conjRight _ ih =>
      dsimp [evalTerm]; rw [ih]

theorem simBA_sound : ∀ s t env, SimBA s t → evalTerm env s = evalTerm env t := by
  intro s t env ⟨p, hp⟩
  exact simBAPath_sound p s t env hp

theorem simBAStar_sound : ∀ s t env, SimBAStar s t → evalTerm env s = evalTerm env t := by
  intro s t env h
  induction h with
  | refl _ => rfl
  | step hstep _ ih =>
      exact (simBA_sound _ _ env hstep).trans ih

theorem simBAN_to_simBAStar {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SimBAStar s t := by
  induction h with
  | zero s => exact .refl s
  | succ hstep _ ih => exact .step hstep ih

theorem simBAN_sound (n : Nat) (s t : DeMorganTerm) (env : Nat → Bool)
    (h : SimBAN n s t) : evalTerm env s = evalTerm env t :=
  simBAStar_sound s t env (simBAN_to_simBAStar h)

/-! ## Algebraic & Congruence Properties of `SimBAStar` and `SimBAN` -/

theorem simBAStar_single {s t : DeMorganTerm} (h : SimBA s t) : SimBAStar s t :=
  .step h (.refl t)

theorem simBAStar_trans {s u t : DeMorganTerm}
    (h₁ : SimBAStar s u) (h₂ : SimBAStar u t) : SimBAStar s t := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep _ ih => exact .step hstep (ih h₂)

theorem simBAStar_symm {s t : DeMorganTerm} (h : SimBAStar s t) : SimBAStar t s := by
  induction h with
  | refl s => exact .refl s
  | step hstep _ ih => exact simBAStar_trans ih (simBAStar_single (simBA_symm hstep))

theorem simBAStar_neg {s t : DeMorganTerm} (h : SimBAStar s t) :
    SimBAStar (.neg s) (.neg t) := by
  induction h with
  | refl s => exact .refl (.neg s)
  | step hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .step ⟨false :: p, .neg hp⟩ ih

theorem simBAStar_disj_left {s₁ t₁ s₂ : DeMorganTerm} (h : SimBAStar s₁ t₁) :
    SimBAStar (.disj s₁ s₂) (.disj t₁ s₂) := by
  induction h with
  | refl s₁ => exact .refl (.disj s₁ s₂)
  | step hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .step ⟨false :: p, .disjLeft hp⟩ ih

theorem simBAStar_disj_right {s₁ s₂ t₂ : DeMorganTerm} (h : SimBAStar s₂ t₂) :
    SimBAStar (.disj s₁ s₂) (.disj s₁ t₂) := by
  induction h with
  | refl s₂ => exact .refl (.disj s₁ s₂)
  | step hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .step ⟨true :: p, .disjRight hp⟩ ih

theorem simBAStar_conj_left {s₁ t₁ s₂ : DeMorganTerm} (h : SimBAStar s₁ t₁) :
    SimBAStar (.conj s₁ s₂) (.conj t₁ s₂) := by
  induction h with
  | refl s₁ => exact .refl (.conj s₁ s₂)
  | step hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .step ⟨false :: p, .conjLeft hp⟩ ih

theorem simBAStar_conj_right {s₁ s₂ t₂ : DeMorganTerm} (h : SimBAStar s₂ t₂) :
    SimBAStar (.conj s₁ s₂) (.conj s₁ t₂) := by
  induction h with
  | refl s₂ => exact .refl (.conj s₁ s₂)
  | step hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .step ⟨true :: p, .conjRight hp⟩ ih

/-! ### Step-counted combinators for `SimBAN` -/

theorem simBAN_trans {m n : Nat} {s u t : DeMorganTerm}
    (h₁ : SimBAN m s u) (h₂ : SimBAN n u t) : SimBAN (m + n) s t := by
  induction h₁ with
  | zero _ =>
      simpa [Nat.zero_add] using h₂
  | @succ k s' u' _ hstep _ ih =>
      have h' : SimBAN (k + n + 1) s' t := .succ hstep (ih h₂)
      simpa [Nat.succ_add] using h'

theorem simBAN_snoc {n : Nat} {s u t : DeMorganTerm}
    (h₁ : SimBAN n s u) (h₂ : SimBA u t) : SimBAN (n + 1) s t :=
  simBAN_trans h₁ (.succ h₂ (.zero t))

theorem simBAN_symm {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SimBAN n t s := by
  induction h with
  | zero s => exact .zero s
  | succ hstep _ ih => exact simBAN_snoc ih (simBA_symm hstep)

theorem simBAN_neg {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SimBAN n (.neg s) (.neg t) := by
  induction h with
  | zero s => exact .zero (.neg s)
  | succ hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .succ ⟨false :: p, .neg hp⟩ ih

theorem simBAN_disj_left {n : Nat} {s₁ t₁ s₂ : DeMorganTerm}
    (h : SimBAN n s₁ t₁) : SimBAN n (.disj s₁ s₂) (.disj t₁ s₂) := by
  induction h with
  | zero s₁ => exact .zero (.disj s₁ s₂)
  | succ hstep _ ih =>
      let ⟨p, hp⟩ := hstep
      exact .succ ⟨false :: p, .disjLeft hp⟩ ih

/-! ## Modus Ponens Constant-Step Simulation (Krajíček Lemma 2.1, lines 359-371)

From `a ~_BA^* 1` and `(¬a ∨ b) ~_BA^* 1`, derive `b ~_BA^* 1` using each hypothesis
exactly once (preserving tree-likeness) and adding exactly 2 explicit `SimBA` steps:
1. `a ~_BA^* 1`  ==>  `¬a ~_BA^* ¬1 ~_BA 0`  (1 explicit step: `BAAxiom.negOne`)
2. `¬a ∨ b ~_BA^* 0 ∨ b ~_BA b`             (1 explicit step: `BAAxiom.disjZeroLeft b`)
3. Reverse step (2) to get `b ~_BA^* ¬a ∨ b`, then compose with `(¬a ∨ b) ~_BA^* 1`.
-/

theorem modus_ponens_simBAStar (a b : DeMorganTerm)
    (ha : SimBAStar a .one)
    (himp : SimBAStar (.disj (.neg a) b) .one) :
    SimBAStar b .one := by
  -- Step 1: ¬a ~_BA^* ¬1 ~_BA 0
  have hNegOne : SimBA (.neg .one) .zero :=
    ⟨[], .root (.fwd .negOne)⟩
  have hNegA_zero : SimBAStar (.neg a) .zero :=
    simBAStar_trans (simBAStar_neg ha) (simBAStar_single hNegOne)
  -- Step 2: (¬a ∨ b) ~_BA^* (0 ∨ b) ~_BA b
  have hZeroOrB : SimBA (.disj .zero b) b :=
    ⟨[], .root (.fwd (.disjZeroLeft b))⟩
  have hImp_b : SimBAStar (.disj (.neg a) b) b :=
    simBAStar_trans (simBAStar_disj_left hNegA_zero) (simBAStar_single hZeroOrB)
  -- Step 3: b ~_BA^* (¬a ∨ b) ~_BA^* 1
  exact simBAStar_trans (simBAStar_symm hImp_b) himp

/-- Exact step-counted version of Lemma 2.1 Modus Ponens simulation:
    overhead is literally +2 `SimBA` steps (`negOne` and `disjZeroLeft`). -/
theorem modus_ponens_simBAN (a b : DeMorganTerm) (k₁ k₂ : Nat)
    (ha : SimBAN k₁ a .one)
    (himp : SimBAN k₂ (.disj (.neg a) b) .one) :
    SimBAN (k₁ + 2 + k₂) b .one := by
  have hNegOne : SimBA (.neg .one) .zero :=
    ⟨[], .root (.fwd .negOne)⟩
  have hNegA_zero : SimBAN (k₁ + 1) (.neg a) .zero :=
    simBAN_snoc (simBAN_neg ha) hNegOne
  have hZeroOrB : SimBA (.disj .zero b) b :=
    ⟨[], .root (.fwd (.disjZeroLeft b))⟩
  have hImp_b : SimBAN (k₁ + 1 + 1) (.disj (.neg a) b) b :=
    simBAN_snoc (simBAN_disj_left hNegA_zero) hZeroOrB
  have hb_imp : SimBAN (k₁ + 2) b (.disj (.neg a) b) :=
    simBAN_symm hImp_b
  exact simBAN_trans hb_imp himp

end KrajicekBARewriting

#print axioms KrajicekBARewriting.baAxiom_sound
#print axioms KrajicekBARewriting.baStep_sound
#print axioms KrajicekBARewriting.simBAPath_sound
#print axioms KrajicekBARewriting.simBA_sound
#print axioms KrajicekBARewriting.simBAStar_sound
#print axioms KrajicekBARewriting.modus_ponens_simBAStar
#print axioms KrajicekBARewriting.modus_ponens_simBAN
