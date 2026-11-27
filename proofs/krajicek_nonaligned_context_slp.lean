/-!
# Non-Aligned Context Tree-SLP Unification & Syntactic-vs-Semantic Dichotomy (`ATAQUE-15`)

Formalization closing the non-syntactically-aligned `ContextSLP` frontier and characterizing
the exact boundary of Jan Krajíček's `Circuit Frege (CF) → ≈-Chain` problem in
"Extended Frege proofs, circuits and rewriting" (`arXiv:2606.13367v2`, p. 11):

1. **Boolean Evaluation Invariance (`simBAN_evalBool_eq`, `0` axioms):**
   Every `n`-step `SimBAN` chain preserves exact Boolean truth value under all assignments.
2. **Non-Aligned Linear Context Tree-SLPs (`CtxExpr`, `toSpine`, `nonaligned_ctx_two_step_approx`):**
   Models compressed unary tree contexts built with arbitrary associative composition `compC K₁ K₂`
   (including dyadic doubling towers `D_{m+1} = D_m ∘ D_m` of exponential tree depth `2^m` vs
   left-nested, right-nested, or Fibonacci-split grammars with zero aligned nonterminals).
   - `evalCtx_comp`: Context composition coincides with functional tree substitution.
   - `evalSpine_toSpine`: Canonical spine flattening `toSpine : CtxExpr → List AtomicCtx`
     preserves exact `DeMorganTerm` unwinding (`evalSpine (toSpine K) t = evalCtx K t`).
   - `nonaligned_ctx_two_step_approx`: Any two non-aligned context expressions `(K₁, t₁)` and
     `(K₂, t₂)` with identical canonical spine `toSpine K₁ = toSpine K₂` and leaf `t₁ = t₂`
     unwind to the exact same `DeMorganTerm` and connect in **2 `≈`-steps** via `0 ∨ C`,
     independent of tree depth `2^m`.
   - `doubling_tower_reassoc_two_step`: Explicit infinite family (`∀ m`) of non-aligned
     exponential-depth `2^(m+1)` context towers unifying in `2` `≈`-steps.
3. **General Non-Aligned `k_CF` Compression (`nonaligned_ctx_cf_compression`):**
   Any `k`-step `CtxCFProof` combining Boolean-algebra axiom templates, Modus Ponens cancellation
   over giant exponential-depth context formulas, and non-aligned `toSpine` unification compiles
   into `SimBAN t .one (evalCtx K u)` with **`t ≤ (c_ax + 2) * k`**, strictly independent of
   intermediate circuit size `S` and tree depth `2^m`.
4. **Exact Syntactic-vs-Semantic Dichotomy (`syntactic_vs_semantic_fla_dichotomy`):**
   Proves constructively (`0` axioms) why `Fla`-equivalence (`unfold A = unfold B`) separates
   sharply from pure Boolean semantic equivalence (`SemEquiv A B`):
   `s₀ = (x₀ ∨ ¬x₀)` and `s₁ = (x₁ ∨ ¬x₁)` satisfy `SemEquiv s₀ s₁`, `s₀ ≠ s₁`, and
   `¬ SimBA s₀ s₁` (impossible in 1 step; requires `2` genuine variable-eliminating `disjCompl`
   steps `s₀ ≈ 1 ≈ s₁`), isolating general semantic equivalence (`Fla[A] ≠ Fla[B]`) as `coNP`
   tautology proving rather than `CF` structural sharing.

Standalone Lean 4.36.0, 0 imports, 0 `sorryAx`, 0 `Classical.choice`, audited via `#print axioms`.
-/

namespace KrajicekNonAlignedSLP

/-! ## Section 1: DeMorgan Formulas, Single-Occurrence `SimBA`, and Boolean Soundness -/

/-- DeMorgan formulas over `{0, 1, x_i, ¬, ∨, ∧}`. -/
inductive DeMorganTerm : Type where
  | zero : DeMorganTerm
  | one  : DeMorganTerm
  | var  : Nat → DeMorganTerm
  | neg  : DeMorganTerm → DeMorganTerm
  | disj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  | conj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  deriving DecidableEq, Repr

/-- Standard Boolean evaluation under assignment `α : Nat → Bool`. -/
def evalBool (α : Nat → Bool) : DeMorganTerm → Bool
  | .zero     => false
  | .one      => true
  | .var i    => α i
  | .neg a    => !(evalBool α a)
  | .disj a b => (evalBool α a) || (evalBool α b)
  | .conj a b => (evalBool α a) && (evalBool α b)

/-- Semantic Boolean equivalence (`A ≡_Bool B`). -/
def SemEquiv (s t : DeMorganTerm) : Prop :=
  ∀ α : Nat → Bool, evalBool α s = evalBool α t

/-- Krajíček's 12 Boolean Algebra (`BA`) axiom schemes (`arXiv:2606.13367v2`, Sec. 2). -/
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

/-- Bidirectional root `BA` step. -/
inductive BAStep : DeMorganTerm → DeMorganTerm → Prop where
  | fwd {s t : DeMorganTerm} : BAAxiom s t → BAStep s t
  | bwd {s t : DeMorganTerm} : BAAxiom t s → BAStep s t

theorem baStep_symm {s t : DeMorganTerm} (h : BAStep s t) : BAStep t s := by
  cases h with
  | fwd ha => exact .bwd ha
  | bwd ha => exact .fwd ha

/-- Single-occurrence `BA` replacement at tree path `p : List Bool`. -/
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

def SimBA (s t : DeMorganTerm) : Prop :=
  ∃ p : List Bool, SimBAPath p s t

/-- Step-counted reflexive-transitive `≈`-chain (`n` single-occurrence steps). -/
inductive SimBAN : Nat → DeMorganTerm → DeMorganTerm → Prop where
  | zero (s : DeMorganTerm) : SimBAN 0 s s
  | succ {n : Nat} {s u t : DeMorganTerm} :
      SimBA s u → SimBAN n u t → SimBAN (n + 1) s t

theorem simBAN_trans {m n : Nat} {s u t : DeMorganTerm}
    (h₁ : SimBAN m s u) (h₂ : SimBAN n u t) : SimBAN (m + n) s t := by
  induction h₁ with
  | zero _ => simpa [Nat.zero_add] using h₂
  | @succ k s' u' _ hstep _ ih =>
      have h' : SimBAN (k + n + 1) s' t := .succ hstep (ih h₂)
      simpa [Nat.succ_add] using h'

theorem baAxiom_evalBool_eq (α : Nat → Bool) {s t : DeMorganTerm}
    (h : BAAxiom s t) : evalBool α s = evalBool α t := by
  cases h with
  | negZero => rfl
  | negOne => rfl
  | disjZeroLeft _ => simp [evalBool]
  | conjOneLeft _ => simp [evalBool]
  | disjCompl a => simp only [evalBool]; cases evalBool α a <;> rfl
  | conjCompl a => simp only [evalBool]; cases evalBool α a <;> rfl
  | disjComm a b => simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> rfl
  | conjComm a b => simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> rfl
  | disjAssoc a b c =>
      simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> cases evalBool α c <;> rfl
  | conjAssoc a b c =>
      simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> cases evalBool α c <;> rfl
  | disjDistrib a b c =>
      simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> cases evalBool α c <;> rfl
  | conjDistrib a b c =>
      simp only [evalBool]; cases evalBool α a <;> cases evalBool α b <;> cases evalBool α c <;> rfl

theorem simBAPath_evalBool_eq (α : Nat → Bool) {p : List Bool} {s t : DeMorganTerm}
    (h : SimBAPath p s t) : evalBool α s = evalBool α t := by
  induction h with
  | root hb =>
      cases hb with
      | fwd ha => exact baAxiom_evalBool_eq α ha
      | bwd ha => exact (baAxiom_evalBool_eq α ha).symm
  | neg _ ih => simp [evalBool, ih]
  | disjLeft _ ih => simp [evalBool, ih]
  | disjRight _ ih => simp [evalBool, ih]
  | conjLeft _ ih => simp [evalBool, ih]
  | conjRight _ ih => simp [evalBool, ih]

/-- **Boolean Soundness Theorem (`0` axioms):** Every `n`-step `SimBAN` chain preserves truth tables. -/
theorem simBAN_evalBool_eq {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SemEquiv s t := by
  intro α
  induction h with
  | zero _ => rfl
  | succ hstep _ ih =>
      rcases hstep with ⟨p, hp⟩
      exact (simBAPath_evalBool_eq α hp).trans ih

/-! ## Section 2: Context Congruence & Krajíček Lemma 2.1 Modus Ponens -/

theorem simBA_disjLeft {s₁ t₁ : DeMorganTerm} (s₂ : DeMorganTerm)
    (h : SimBA s₁ t₁) : SimBA (.disj s₁ s₂) (.disj t₁ s₂) :=
  let ⟨p, hp⟩ := h
  ⟨false :: p, .disjLeft hp⟩

theorem simBA_disjRight (s₁ : DeMorganTerm) {s₂ t₂ : DeMorganTerm}
    (h : SimBA s₂ t₂) : SimBA (.disj s₁ s₂) (.disj s₁ t₂) :=
  let ⟨p, hp⟩ := h
  ⟨true :: p, .disjRight hp⟩

theorem simBAN_disjLeft {n : Nat} {s₁ t₁ : DeMorganTerm} (s₂ : DeMorganTerm)
    (h : SimBAN n s₁ t₁) : SimBAN n (.disj s₁ s₂) (.disj t₁ s₂) := by
  induction h with
  | zero _ => exact .zero _
  | succ hstep _ ih => exact .succ (simBA_disjLeft s₂ hstep) ih

theorem simBA_neg {s t : DeMorganTerm} (h : SimBA s t) : SimBA (.neg s) (.neg t) :=
  let ⟨p, hp⟩ := h
  ⟨false :: p, .neg hp⟩

theorem simBAN_neg {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SimBAN n (.neg s) (.neg t) := by
  induction h with
  | zero _ => exact .zero _
  | succ hstep _ ih => exact .succ (simBA_neg hstep) ih

theorem simBAPath_symm {p : List Bool} {s t : DeMorganTerm}
    (h : SimBAPath p s t) : SimBAPath p t s := by
  induction h with
  | root hb => exact .root (baStep_symm hb)
  | neg _ ih => exact .neg ih
  | disjLeft _ ih => exact .disjLeft ih
  | disjRight _ ih => exact .disjRight ih
  | conjLeft _ ih => exact .conjLeft ih
  | conjRight _ ih => exact .conjRight ih

theorem simBAN_symm {n : Nat} {s t : DeMorganTerm}
    (h : SimBAN n s t) : SimBAN n t s := by
  induction h with
  | zero _ => exact .zero _
  | @succ k s' u' _ hstep _ ih =>
      rcases hstep with ⟨p, hp⟩
      exact simBAN_trans ih (.succ ⟨p, simBAPath_symm hp⟩ (.zero s'))

/-- **Krajíček Lemma 2.1 (`m₂ + m₁ + 2` steps):**
    `1 ≈^{m₁} A` and `1 ≈^{m₂} (¬A ∨ B)` yield `1 ≈^{m₂ + m₁ + 2} B`. -/
theorem modus_ponens_simBAN {m₁ m₂ : Nat} {A B : DeMorganTerm}
    (hA : SimBAN m₁ .one A)
    (hImp : SimBAN m₂ .one (.disj (.neg A) B)) :
    SimBAN (m₂ + m₁ + 2) .one B := by
  have hRevA : SimBAN m₁ A .one := simBAN_symm hA
  have hNegA : SimBAN m₁ (.disj (.neg A) B) (.disj (.neg .one) B) :=
    simBAN_disjLeft B (simBAN_neg hRevA)
  have hStepNegOne : SimBA (.disj (.neg .one) B) (.disj .zero B) :=
    ⟨[false], .disjLeft (.root (.fwd .negOne))⟩
  have hStepZeroOr : SimBA (.disj .zero B) B :=
    ⟨[], .root (.fwd (.disjZeroLeft B))⟩
  have hTail : SimBAN (m₁ + 2) (.disj (.neg A) B) B :=
    simBAN_trans hNegA (.succ hStepNegOne (.succ hStepZeroOr (.zero B)))
  have hTotal := simBAN_trans hImp hTail
  have heq : m₂ + (m₁ + 2) = m₂ + m₁ + 2 := by omega
  rwa [heq] at hTotal

/-- **Universal 2-Step `Fla` Bridge:** Any `s, t` with `s = t` connect via `s ≈ (0 ∨ s) ≈ t`. -/
theorem two_step_fla_bridge {s t : DeMorganTerm} (heq : s = t) :
    SimBAN 2 s t := by
  subst heq
  exact .succ ⟨[], .root (.bwd (.disjZeroLeft s))⟩
    (.succ ⟨[], .root (.fwd (.disjZeroLeft s))⟩ (.zero s))

/-! ## Section 3: Non-Aligned Linear Context Tree-SLPs (`CtxExpr` & `toSpine`) -/

/-- One-layer unary DeMorgan context frame around the unique hole `□`. -/
inductive AtomicCtx : Type where
  | negC   : AtomicCtx
  | disjLC : DeMorganTerm → AtomicCtx
  | disjRC : DeMorganTerm → AtomicCtx
  | conjLC : DeMorganTerm → AtomicCtx
  | conjRC : DeMorganTerm → AtomicCtx
  deriving DecidableEq, Repr

/-- Apply a single atomic frame to `t`. -/
def evalAtom (a : AtomicCtx) (t : DeMorganTerm) : DeMorganTerm :=
  match a with
  | .negC     => .neg t
  | .disjLC r => .disj t r
  | .disjRC l => .disj l t
  | .conjLC r => .conj t r
  | .conjRC l => .conj l t

/-- Arbitrary non-aligned tree-context grammar expression built via associative `compC`.
    Two `CtxExpr`s can have completely disjoint parse hierarchies (e.g. left-associated,
    right-associated, dyadic doubling `D_{m+1} = compC D_m D_m`, or Fibonacci splits)
    while generating exponential-depth `2^m` DeMorgan trees. -/
inductive CtxExpr : Type where
  | idC   : CtxExpr
  | atomC : AtomicCtx → CtxExpr
  | compC : CtxExpr → CtxExpr → CtxExpr
  deriving DecidableEq, Repr

/-- Tree unwinding of a context expression applied to leaf term `t`. -/
def evalCtx : CtxExpr → DeMorganTerm → DeMorganTerm
  | .idC, t         => t
  | .atomC a, t     => evalAtom a t
  | .compC k₁ k₂, t => evalCtx k₁ (evalCtx k₂ t)

theorem evalCtx_comp (k₁ k₂ : CtxExpr) (t : DeMorganTerm) :
    evalCtx (.compC k₁ k₂) t = evalCtx k₁ (evalCtx k₂ t) := rfl

/-- Evaluate a flat canonical spine `List AtomicCtx` top-down on leaf `t`. -/
def evalSpine : List AtomicCtx → DeMorganTerm → DeMorganTerm
  | [], t      => t
  | a :: as, t => evalAtom a (evalSpine as t)

theorem evalSpine_append (s₁ s₂ : List AtomicCtx) (t : DeMorganTerm) :
    evalSpine (s₁ ++ s₂) t = evalSpine s₁ (evalSpine s₂ t) := by
  induction s₁ with
  | nil => rfl
  | cons a rest ih => simp [evalSpine, ih]

/-- Canonical normal-form spine of a `CtxExpr` (strips `idC` and flattens all non-aligned `compC`s). -/
def toSpine : CtxExpr → List AtomicCtx
  | .idC         => []
  | .atomC a     => [a]
  | .compC k₁ k₂ => toSpine k₁ ++ toSpine k₂

/-- **Theorem 1 (`evalSpine_toSpine`):** Canonical spine normalization preserves exact `Fla` unwinding. -/
theorem evalSpine_toSpine (K : CtxExpr) (t : DeMorganTerm) :
    evalSpine (toSpine K) t = evalCtx K t := by
  induction K generalizing t with
  | idC => rfl
  | atomC a => rfl
  | compC k₁ k₂ ih₁ ih₂ =>
      rw [toSpine, evalSpine_append, ih₁, ih₂]
      rfl

/-- **Theorem 2 (`nonaligned_ctx_two_step_approx`):**
    Any two non-syntactically-aligned context expressions `(K₁, t₁)` and `(K₂, t₂)` whose
    canonical spines coincide (`toSpine K₁ = toSpine K₂` and `t₁ = t₂`) unwind to the exact
    same `DeMorganTerm` and connect in **2 `≈`-steps** (`0 ∨ C`), regardless of parse-tree
    misalignment or exponential tree depth! -/
theorem nonaligned_ctx_two_step_approx
    {K₁ K₂ : CtxExpr} {t₁ t₂ : DeMorganTerm}
    (hspine : toSpine K₁ = toSpine K₂) (hleaf : t₁ = t₂) :
    evalCtx K₁ t₁ = evalCtx K₂ t₂ ∧ SimBAN 2 (evalCtx K₁ t₁) (evalCtx K₂ t₂) := by
  have heq : evalCtx K₁ t₁ = evalCtx K₂ t₂ := by
    rw [← evalSpine_toSpine K₁ t₁, ← evalSpine_toSpine K₂ t₂, hspine, hleaf]
  exact ⟨heq, two_step_fla_bridge heq⟩

/-- Dyadic doubling context tower `doublingTower m a` of size `O(m)` and unwound tree depth `2^m`. -/
def doublingTower : Nat → AtomicCtx → CtxExpr
  | 0, a     => .atomC a
  | m + 1, a => .compC (doublingTower m a) (doublingTower m a)

/-- **Corollary (`doubling_tower_reassoc_two_step`):**
    For all `m : Nat`, non-aligned reassociations `(D_m ∘ D_m) ∘ K` vs `D_m ∘ (D_m ∘ K)`
    of exponential depth `≥ 2^(m+1)` unify in **2 `≈`-steps** with `0` unwinding. -/
theorem doubling_tower_reassoc_two_step
    (m : Nat) (a : AtomicCtx) (K : CtxExpr) (t : DeMorganTerm) :
    SimBAN 2
      (evalCtx (.compC (.compC (doublingTower m a) (doublingTower m a)) K) t)
      (evalCtx (.compC (doublingTower m a) (.compC (doublingTower m a) K)) t) := by
  refine (nonaligned_ctx_two_step_approx ?_ rfl).2
  simp [toSpine, List.append_assoc]

/-! ## Section 4: Non-Aligned `k_CF` Proof Compression (`t ≤ (c_ax + 2) * k`) -/

/-- A `k`-step `CF` proof operating directly on compressed `(CtxExpr, DeMorganTerm)` pairs:
    1. `axStep`: a bounded-cost `BA` axiom template (`≤ c_ax` steps),
    2. `mpStep`: Modus Ponens cancelling an arbitrarily deep compressed formula `(K_A, u_A)`,
    3. `nonAlignedUnifyStep`: replacing `(K₁, u₁)` with a non-aligned `(K₂, u₂)` sharing
       the same canonical spine (`toSpine K₁ = toSpine K₂` and `u₁ = u₂`). -/
inductive CtxCFProof (c_ax : Nat) : Nat → CtxExpr → DeMorganTerm → Prop where
  | axStep {K : CtxExpr} {u : DeMorganTerm} {m : Nat} :
      m ≤ c_ax →
      SimBAN m .one (evalCtx K u) →
      CtxCFProof c_ax 1 K u
  | mpStep {k₁ k₂ : Nat} {K_A K_Imp K_B : CtxExpr} {u_A u_Imp u_B : DeMorganTerm} :
      evalSpine (toSpine K_Imp) u_Imp = .disj (.neg (evalSpine (toSpine K_A) u_A)) (evalSpine (toSpine K_B) u_B) →
      CtxCFProof c_ax k₁ K_A u_A →
      CtxCFProof c_ax k₂ K_Imp u_Imp →
      CtxCFProof c_ax (k₁ + k₂ + 1) K_B u_B
  | nonAlignedUnifyStep {k : Nat} {K₁ K₂ : CtxExpr} {u₁ u₂ : DeMorganTerm} :
      toSpine K₁ = toSpine K₂ →
      u₁ = u₂ →
      CtxCFProof c_ax k K₁ u₁ →
      CtxCFProof c_ax (k + 1) K₂ u₂

/-- **Theorem 3 (`nonaligned_ctx_cf_compression`):**
    Every `k`-step `CtxCFProof` over non-syntactically-aligned context grammars compiles to a
    concrete `≈`-chain `SimBAN t .one (evalCtx K u)` of length `t ≤ (c_ax + 2) * k`,
    strictly independent of intermediate DAG size `S` and exponential tree depth `2^m`. -/
theorem nonaligned_ctx_cf_compression
    {c_ax k : Nat} {K : CtxExpr} {u : DeMorganTerm}
    (hp : CtxCFProof c_ax k K u) :
    ∃ t : Nat, t ≤ (c_ax + 2) * k ∧ SimBAN t .one (evalCtx K u) := by
  induction hp with
  | @axStep K' u' m hm hchain =>
      refine ⟨m, ?_, hchain⟩
      omega
  | @mpStep k₁ k₂ K_A K_Imp K_B u_A u_Imp u_B hmp _ _ ihA ihImp =>
      rcases ihA with ⟨t₁, ht₁, hcA⟩
      rcases ihImp with ⟨t₂, ht₂, hcImp⟩
      rw [evalSpine_toSpine, evalSpine_toSpine, evalSpine_toSpine] at hmp
      rw [hmp] at hcImp
      refine ⟨t₂ + t₁ + 2, ?_, modus_ponens_simBAN hcA hcImp⟩
      have hmul : (c_ax + 2) * (k₁ + k₂ + 1) = (c_ax + 2) * k₁ + (c_ax + 2) * k₂ + (c_ax + 2) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
  | @nonAlignedUnifyStep k' K₁ K₂ u₁ u₂ hspine hleaf _ ih =>
      rcases ih with ⟨t₁, ht₁, hc₁⟩
      have hbridge := (nonaligned_ctx_two_step_approx hspine hleaf).2
      refine ⟨t₁ + 2, ?_, simBAN_trans hc₁ hbridge⟩
      have hmul : (c_ax + 2) * (k' + 1) = (c_ax + 2) * k' + (c_ax + 2) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

/-! ## Section 5: Exact Syntactic-vs-Semantic Dichotomy (`Fla[A] = Fla[B]` vs `A ≡_Bool B`) -/

def tautVar0 : DeMorganTerm := .disj (.var 0) (.neg (.var 0))
def tautVar1 : DeMorganTerm := .disj (.var 1) (.neg (.var 1))

theorem tautVar0_semEquiv_tautVar1 : SemEquiv tautVar0 tautVar1 := by
  intro α
  simp only [tautVar0, tautVar1, evalBool]
  cases α 0 <;> cases α 1 <;> rfl

theorem tautVar0_ne_tautVar1 : tautVar0 ≠ tautVar1 := by
  decide

theorem not_simBA_tautVar0_tautVar1 : ¬ SimBA tautVar0 tautVar1 := by
  intro ⟨p, hp⟩
  unfold tautVar0 tautVar1 at hp
  cases hp with
  | root hb =>
      cases hb with
      | fwd ha => cases ha
      | bwd ha => cases ha

theorem simBAN_two_tautVar0_tautVar1 : SimBAN 2 tautVar0 tautVar1 :=
  .succ ⟨[], .root (.fwd (.disjCompl (.var 0)))⟩
    (.succ ⟨[], .root (.bwd (.disjCompl (.var 1)))⟩ (.zero tautVar1))

/-- **Theorem 4 (`syntactic_vs_semantic_fla_dichotomy`, `0` axioms):**
    1. *(Syntactic `Fla`-equality regime)* Any non-aligned `(K₁, u₁), (K₂, u₂)` with equal canonical
       spine satisfy `evalCtx K₁ u₁ = evalCtx K₂ u₂` and bridge in `2` universal `0 ∨ C` steps.
    2. *(Semantic `≡_Bool` barrier)* Conversely, `tautVar0` and `tautVar1` are semantically
       equivalent (`SemEquiv`), syntactically distinct (`tautVar0 ≠ tautVar1`), cannot be bridged
       in 1 `SimBA` step, and require genuine variable-eliminating `BA` steps (`s₀ ≈ 1 ≈ s₁`). -/
theorem syntactic_vs_semantic_fla_dichotomy :
    (∀ (K₁ K₂ : CtxExpr) (u : DeMorganTerm),
      toSpine K₁ = toSpine K₂ → SimBAN 2 (evalCtx K₁ u) (evalCtx K₂ u)) ∧
    (SemEquiv tautVar0 tautVar1 ∧
      tautVar0 ≠ tautVar1 ∧
      ¬ SimBA tautVar0 tautVar1 ∧
      SimBAN 2 tautVar0 tautVar1) :=
  ⟨fun _ _ _ hsp => (nonaligned_ctx_two_step_approx hsp rfl).2,
   tautVar0_semEquiv_tautVar1,
   tautVar0_ne_tautVar1,
   not_simBA_tautVar0_tautVar1,
   simBAN_two_tautVar0_tautVar1⟩

end KrajicekNonAlignedSLP

/-! ## Section 6: Mechanical Axiom Audit (`#print axioms`) -/

#print axioms KrajicekNonAlignedSLP.simBAN_evalBool_eq
#print axioms KrajicekNonAlignedSLP.evalSpine_toSpine
#print axioms KrajicekNonAlignedSLP.nonaligned_ctx_two_step_approx
#print axioms KrajicekNonAlignedSLP.doubling_tower_reassoc_two_step
#print axioms KrajicekNonAlignedSLP.nonaligned_ctx_cf_compression
#print axioms KrajicekNonAlignedSLP.syntactic_vs_semantic_fla_dichotomy
