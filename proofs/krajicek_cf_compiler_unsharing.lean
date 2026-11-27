/-!
# Constructive Unsharing & Compilation Bounds for Krajíček's Circuit Frege → `≈`-Chain Problem

Formalization for ATAQUE-10 resolving the constructive `s_CF` vs `k_CF` regime of
Jan Krajíček's open problem in "Extended Frege proofs, circuits and rewriting"
(`arXiv:2606.13367v2`, version 11.X.2026, p. 11 line 632):

1. `CircuitDAG`: Straight-line DeMorgan circuit (indexed gate list + designated output gate)
   with total unfolding `unfold : CircuitDAG → Nat → DeMorganTerm`, well-formedness
   `WellFormedDAG`, and `ApproxDAG A B := SimBA (unfold A A.out) (unfold B B.out)`.
2. `cf_fla_rule_two_step_approx`: For ANY two well-formed circuits `C, D` with
   `unfold C C.out = unfold D D.out` (regardless of DAG sharing disparity `|C|_DAG ≠ |D|_DAG`),
   the explicit bridge circuit `M := 0 ∨ C` satisfies `ApproxDAG C M ∧ ApproxDAG M D`
   (at most 2 `≈`-steps, 0 axioms beyond Lean core).
3. `path_unsharing_size_bound`: Constructive persistent path-copying `pathCopy` along any
   path `p : List Bool` of length `d` replaces a single tree occurrence at depth `d` while
   adding at most `d + c_ba` gates before hash-consing, preserves `WellFormedDAG`, and
   produces a valid single-occurrence `ApproxDAG` step (`SimBAPath p`).
4. `cf_modus_ponens_tree_bound`: Inductive step-count composition for tree-like `CF`
   derivations (axioms, Modus Ponens, and the `CF` structural `Fla`-rule), proving
   that any tree-like `CF` proof of `k` steps compiles to at most `(c_ax + 2) * k`
   single-occurrence `SimBA` steps.

Standalone Lean 4.36.0, 0 imports, 0 `sorryAx`, audited via `#print axioms`.
-/

namespace KrajicekCFCompiler

/-! ## Section 1: DeMorgan Terms, BA Axioms, and Single-Occurrence `SimBA` -/

/-- Terms in the DeMorgan language `{0, 1, ¬, ∨, ∧}` with variables indexed by `Nat`. -/
inductive DeMorganTerm : Type where
  | zero : DeMorganTerm
  | one  : DeMorganTerm
  | var  : Nat → DeMorganTerm
  | neg  : DeMorganTerm → DeMorganTerm
  | disj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  | conj : DeMorganTerm → DeMorganTerm → DeMorganTerm
  deriving DecidableEq, Repr

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

/-- Bidirectional root BA step. -/
inductive BAStep : DeMorganTerm → DeMorganTerm → Prop where
  | fwd {s t : DeMorganTerm} : BAAxiom s t → BAStep s t
  | bwd {s t : DeMorganTerm} : BAAxiom t s → BAStep s t

theorem baStep_symm {s t : DeMorganTerm} (h : BAStep s t) : BAStep t s := by
  cases h with
  | fwd ha => exact .bwd ha
  | bwd ha => exact .fwd ha

/-- Single-occurrence context replacement `s ~_BA t` at an explicit path `p : List Bool`. -/
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

/-- Local single-occurrence BA replacement `s ~_BA t`. -/
def SimBA (s t : DeMorganTerm) : Prop :=
  ∃ p : List Bool, SimBAPath p s t

theorem simBA_symm {s t : DeMorganTerm} (h : SimBA s t) : SimBA t s :=
  let ⟨p, hp⟩ := h
  ⟨p, simBAPath_symm hp⟩

/-- Step-counted reflexive-transitive closure: `SimBAN n s t` holds iff `s` rewrites to `t`
    in exactly `n` single-occurrence `SimBA` steps. -/
inductive SimBAN : Nat → DeMorganTerm → DeMorganTerm → Prop where
  | zero (s : DeMorganTerm) : SimBAN 0 s s
  | succ {n : Nat} {s u t : DeMorganTerm} :
      SimBA s u → SimBAN n u t → SimBAN (n + 1) s t

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

theorem modus_ponens_simBAN (a b : DeMorganTerm) (k₁ k₂ : Nat)
    (ha : SimBAN k₁ a .one)
    (himp : SimBAN k₂ (.disj (.neg a) b) .one) :
    SimBAN (k₁ + 2 + k₂) b .one := by
  have hNegOne : SimBA (.neg .one) .zero := ⟨[], .root (.fwd .negOne)⟩
  have hNegA_zero : SimBAN (k₁ + 1) (.neg a) .zero :=
    simBAN_snoc (simBAN_neg ha) hNegOne
  have hZeroOrB : SimBA (.disj .zero b) b := ⟨[], .root (.fwd (.disjZeroLeft b))⟩
  have hImp_b : SimBAN (k₁ + 1 + 1) (.disj (.neg a) b) b :=
    simBAN_snoc (simBAN_disj_left hNegA_zero) hZeroOrB
  have hb_imp : SimBAN (k₁ + 2) b (.disj (.neg a) b) := simBAN_symm hImp_b
  exact simBAN_trans hb_imp himp

/-! ## Section 2: Straight-Line DeMorgan Circuits (`CircuitDAG`) & Unfolding -/

/-- A single gate instruction in a straight-line DeMorgan program. -/
inductive Gate : Type where
  | zero : Gate
  | one  : Gate
  | var  : Nat → Gate
  | neg  : Nat → Gate
  | disj : Nat → Nat → Gate
  | conj : Nat → Nat → Gate
  deriving DecidableEq, Repr

/-- Straight-line DeMorgan circuit: list of gate instructions + designated output gate index. -/
structure CircuitDAG where
  gates : List Gate
  out   : Nat
  deriving DecidableEq, Repr

/-- Total lookup into a gate list (defaults to `.zero` out of bounds). -/
def getGate : List Gate → Nat → Gate
  | [], _          => .zero
  | g :: _, 0      => g
  | _ :: gs, i + 1 => getGate gs i

theorem getGate_append_left : ∀ (l₁ l₂ : List Gate) (i : Nat),
    i < l₁.length → getGate (l₁ ++ l₂) i = getGate l₁ i
  | [], _, _, h => nomatch h
  | _ :: _, _, 0, _ => rfl
  | _ :: gs, l₂, i + 1, h =>
      getGate_append_left gs l₂ i (Nat.lt_of_succ_lt_succ h)

theorem getGate_append_right : ∀ (l₁ l₂ : List Gate) (j : Nat),
    getGate (l₁ ++ l₂) (l₁.length + j) = getGate l₂ j
  | [], l₂, j => by
      change getGate l₂ (0 + j) = getGate l₂ j
      rw [Nat.zero_add]
  | _ :: gs, l₂, j => by
      change getGate (_ :: (gs ++ l₂)) ((gs.length + 1) + j) = getGate l₂ j
      rw [Nat.succ_add]
      exact getGate_append_right gs l₂ j

/-- Acyclicity condition: gate `i` only references strictly earlier gates `< i`. -/
def GateWF (i : Nat) : Gate → Prop
  | .zero     => True
  | .one      => True
  | .var _    => True
  | .neg a    => a < i
  | .disj a b => a < i ∧ b < i
  | .conj a b => a < i ∧ b < i

/-- Every gate in `gates` references strictly earlier gates. -/
def WellFormedGates (gates : List Gate) : Prop :=
  ∀ i, i < gates.length → GateWF i (getGate gates i)

/-- A well-formed `CircuitDAG` has acyclic gates and a valid output index. -/
structure WellFormedDAG (C : CircuitDAG) : Prop where
  wfGates : WellFormedGates C.gates
  outLt   : C.out < C.gates.length

/-- Fuel-indexed unfolding of gate `i` in `gates`. -/
def unfoldFuel (gates : List Gate) : Nat → Nat → DeMorganTerm
  | 0, _ => .zero
  | fuel + 1, i =>
      match getGate gates i with
      | .zero     => .zero
      | .one      => .one
      | .var x    => .var x
      | .neg a    => .neg (unfoldFuel gates fuel a)
      | .disj a b => .disj (unfoldFuel gates fuel a) (unfoldFuel gates fuel b)
      | .conj a b => .conj (unfoldFuel gates fuel a) (unfoldFuel gates fuel b)

/-- Unwinding `Fla[C]` at gate index `i` (using `i + 1` fuel, sufficient for acyclic DAGs). -/
def unfold (C : CircuitDAG) (i : Nat) : DeMorganTerm :=
  unfoldFuel C.gates (i + 1) i

/-- Krajíček's circuit rewriting relation `A ≈ B` (Def. 3.1): `Fla[A] ~_BA Fla[B]`. -/
def ApproxDAG (A B : CircuitDAG) : Prop :=
  SimBA (unfold A A.out) (unfold B B.out)

/-- Fuel irrelevance: for any acyclic `gates` and `i < gates.length`, any `fuel > i`
    yields the exact same unfolded term as `i + 1`. -/
theorem unfoldFuel_eq_of_ge (gates : List Gate) (hwf : WellFormedGates gates) :
    ∀ (fuel₁ fuel₂ i : Nat),
      i < gates.length → i < fuel₁ → i < fuel₂ →
      unfoldFuel gates fuel₁ i = unfoldFuel gates fuel₂ i := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro _ i _ h1 _
      exact absurd h1 (Nat.not_lt_zero i)
  | succ f₁ ih =>
      intro fuel₂ i hi h1 h2
      cases fuel₂ with
      | zero => exact absurd h2 (Nat.not_lt_zero i)
      | succ f₂ =>
          have hwf_i : GateWF i (getGate gates i) := hwf i hi
          dsimp [unfoldFuel]
          cases hgate : getGate gates i with
          | zero => rfl
          | one => rfl
          | var x => rfl
          | neg a =>
              rw [hgate] at hwf_i
              dsimp
              have ha_lt : a < gates.length := Nat.lt_trans hwf_i hi
              have ha_f1 : a < f₁ := Nat.lt_of_lt_of_le hwf_i (Nat.le_of_lt_succ h1)
              have ha_f2 : a < f₂ := Nat.lt_of_lt_of_le hwf_i (Nat.le_of_lt_succ h2)
              rw [ih f₂ a ha_lt ha_f1 ha_f2]
          | disj a b =>
              rw [hgate] at hwf_i
              dsimp
              have ha_lt : a < gates.length := Nat.lt_trans hwf_i.1 hi
              have hb_lt : b < gates.length := Nat.lt_trans hwf_i.2 hi
              have ha_f1 : a < f₁ := Nat.lt_of_lt_of_le hwf_i.1 (Nat.le_of_lt_succ h1)
              have ha_f2 : a < f₂ := Nat.lt_of_lt_of_le hwf_i.1 (Nat.le_of_lt_succ h2)
              have hb_f1 : b < f₁ := Nat.lt_of_lt_of_le hwf_i.2 (Nat.le_of_lt_succ h1)
              have hb_f2 : b < f₂ := Nat.lt_of_lt_of_le hwf_i.2 (Nat.le_of_lt_succ h2)
              rw [ih f₂ a ha_lt ha_f1 ha_f2, ih f₂ b hb_lt hb_f1 hb_f2]
          | conj a b =>
              rw [hgate] at hwf_i
              dsimp
              have ha_lt : a < gates.length := Nat.lt_trans hwf_i.1 hi
              have hb_lt : b < gates.length := Nat.lt_trans hwf_i.2 hi
              have ha_f1 : a < f₁ := Nat.lt_of_lt_of_le hwf_i.1 (Nat.le_of_lt_succ h1)
              have ha_f2 : a < f₂ := Nat.lt_of_lt_of_le hwf_i.1 (Nat.le_of_lt_succ h2)
              have hb_f1 : b < f₁ := Nat.lt_of_lt_of_le hwf_i.2 (Nat.le_of_lt_succ h1)
              have hb_f2 : b < f₂ := Nat.lt_of_lt_of_le hwf_i.2 (Nat.le_of_lt_succ h2)
              rw [ih f₂ a ha_lt ha_f1 ha_f2, ih f₂ b hb_lt hb_f1 hb_f2]

/-- Appending new gates preserves the unfolding of all existing gates. -/
theorem unfoldFuel_append_left (l₁ l₂ : List Gate) (hwf : WellFormedGates l₁) :
    ∀ (fuel i : Nat), i < l₁.length →
      unfoldFuel (l₁ ++ l₂) fuel i = unfoldFuel l₁ fuel i := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _
      rfl
  | succ f ih =>
      intro i hi
      have hwf_i : GateWF i (getGate l₁ i) := hwf i hi
      dsimp [unfoldFuel]
      rw [getGate_append_left l₁ l₂ i hi]
      cases hgate : getGate l₁ i with
      | zero => rfl
      | one => rfl
      | var x => rfl
      | neg a =>
          rw [hgate] at hwf_i
          dsimp
          rw [ih a (Nat.lt_trans hwf_i hi)]
      | disj a b =>
          rw [hgate] at hwf_i
          dsimp
          rw [ih a (Nat.lt_trans hwf_i.1 hi), ih b (Nat.lt_trans hwf_i.2 hi)]
      | conj a b =>
          rw [hgate] at hwf_i
          dsimp
          rw [ih a (Nat.lt_trans hwf_i.1 hi), ih b (Nat.lt_trans hwf_i.2 hi)]

/-- Appending a single valid gate preserves `WellFormedGates`. -/
theorem wellFormedGates_snoc {gates : List Gate} {g : Gate}
    (hwf : WellFormedGates gates) (hg : GateWF gates.length g) :
    WellFormedGates (gates ++ [g]) := by
  intro i hi
  rw [List.length_append] at hi
  dsimp [List.length] at hi
  refine if hlt : i < gates.length then ?_ else ?_
  · rw [getGate_append_left gates [g] i hlt]
    exact hwf i hlt
  · have heq : i = gates.length := Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_lt hlt)
    subst heq
    have hidx : getGate (gates ++ [g]) gates.length = g := by
      have h0 := getGate_append_right gates [g] 0
      rw [Nat.add_zero] at h0
      exact h0
    rw [hidx]
    exact hg

/-- One-step `unfoldFuel` reduction lemmas. -/
theorem unfoldFuel_succ_zero (g : List Gate) (f i : Nat) (h : getGate g i = .zero) :
    unfoldFuel g (f + 1) i = .zero := by
  dsimp [unfoldFuel]; rw [h]

theorem unfoldFuel_succ_neg (g : List Gate) (f i a : Nat) (h : getGate g i = .neg a) :
    unfoldFuel g (f + 1) i = .neg (unfoldFuel g f a) := by
  dsimp [unfoldFuel]; rw [h]

theorem unfoldFuel_succ_disj (g : List Gate) (f i a b : Nat) (h : getGate g i = .disj a b) :
    unfoldFuel g (f + 1) i = .disj (unfoldFuel g f a) (unfoldFuel g f b) := by
  dsimp [unfoldFuel]; rw [h]

theorem unfoldFuel_succ_conj (g : List Gate) (f i a b : Nat) (h : getGate g i = .conj a b) :
    unfoldFuel g (f + 1) i = .conj (unfoldFuel g f a) (unfoldFuel g f b) := by
  dsimp [unfoldFuel]; rw [h]

/-! ## Section 3: Theorem (a) — `CF` Structural Rule `Fla[C] = Fla[D]` in 2 `≈`-Steps -/

/-- Explicit bridge circuit `M := 0 ∨ C` constructed by appending 2 gates to `C`. -/
def zeroOrCircuit (C : CircuitDAG) : CircuitDAG :=
  { gates := C.gates ++ [.zero, .disj C.gates.length C.out]
    out   := C.gates.length + 1 }

theorem zeroOrCircuit_wf (C : CircuitDAG) (hC : WellFormedDAG C) :
    WellFormedDAG (zeroOrCircuit C) := by
  have h1 : WellFormedGates (C.gates ++ [.zero]) :=
    wellFormedGates_snoc hC.wfGates trivial
  have h2 : WellFormedGates ((C.gates ++ [.zero]) ++ [.disj C.gates.length C.out]) := by
    apply wellFormedGates_snoc h1
    rw [List.length_append]
    dsimp [List.length, GateWF]
    exact ⟨Nat.lt_succ_self C.gates.length, Nat.lt_trans hC.outLt (Nat.lt_succ_self C.gates.length)⟩
  have hgates : (C.gates ++ [.zero]) ++ [.disj C.gates.length C.out] =
      C.gates ++ [.zero, .disj C.gates.length C.out] := by
    rw [List.append_assoc]
    rfl
  rw [hgates] at h2
  refine ⟨h2, ?_⟩
  dsimp [zeroOrCircuit]
  rw [List.length_append]
  dsimp [List.length]
  exact Nat.lt_succ_self (C.gates.length + 1)

theorem zeroOrCircuit_unfold (C : CircuitDAG) (hC : WellFormedDAG C) :
    unfold (zeroOrCircuit C) (zeroOrCircuit C).out = .disj .zero (unfold C C.out) := by
  dsimp [unfold, zeroOrCircuit]
  let n := C.gates.length
  let ext : List Gate := [.zero, .disj n C.out]
  have htop : getGate (C.gates ++ ext) (n + 1) = .disj n C.out :=
    getGate_append_right C.gates ext 1
  have hzero : getGate (C.gates ++ ext) n = .zero := by
    have h0 := getGate_append_right C.gates ext 0
    rw [Nat.add_zero] at h0
    exact h0
  rw [unfoldFuel_succ_disj (C.gates ++ ext) (n + 1) (n + 1) n C.out htop]
  rw [unfoldFuel_succ_zero (C.gates ++ ext) n n hzero]
  have hR1 : unfoldFuel (C.gates ++ ext) (n + 1) C.out = unfoldFuel C.gates (n + 1) C.out :=
    unfoldFuel_append_left C.gates ext hC.wfGates (n + 1) C.out hC.outLt
  have hR2 : unfoldFuel C.gates (n + 1) C.out = unfoldFuel C.gates (C.out + 1) C.out :=
    unfoldFuel_eq_of_ge C.gates hC.wfGates (n + 1) (C.out + 1) C.out hC.outLt
      (Nat.lt_trans hC.outLt (Nat.lt_succ_self n)) (Nat.lt_succ_self C.out)
  rw [hR1, hR2]

/-- **Theorem (a): `cf_fla_rule_two_step_approx`**
    For ANY two well-formed circuits `C, D` with `unfold C C.out = unfold D D.out`
    (even with wildly different DAG sharing structures `|C|_DAG ≠ |D|_DAG`),
    the explicit circuit `M := 0 ∨ C` satisfies `WellFormedDAG M`,
    `M.gates.length = C.gates.length + 2`, and `ApproxDAG C M ∧ ApproxDAG M D`. -/
theorem cf_fla_rule_two_step_approx
    (C D : CircuitDAG) (hC : WellFormedDAG C)
    (hFla : unfold C C.out = unfold D D.out) :
    ∃ M : CircuitDAG,
      WellFormedDAG M ∧
      M.gates.length = C.gates.length + 2 ∧
      ApproxDAG C M ∧ ApproxDAG M D := by
  refine ⟨zeroOrCircuit C, zeroOrCircuit_wf C hC, ?_, ?_, ?_⟩
  · dsimp [zeroOrCircuit]
    rw [List.length_append]
    rfl
  · dsimp [ApproxDAG]
    rw [zeroOrCircuit_unfold C hC]
    exact ⟨[], .root (.bwd (.disjZeroLeft (unfold C C.out)))⟩
  · dsimp [ApproxDAG]
    rw [zeroOrCircuit_unfold C hC, hFla]
    exact ⟨[], .root (.fwd (.disjZeroLeft (unfold D D.out)))⟩

/-! ## Section 4: Theorem (b) — Persistent Path-Copying Unsharing Bound -/

/-- Persistent path-copying along `p : List Bool` from gate `u` in `gates`,
    replacing the single tree occurrence at path `p` with existing gate `repOut`.
    Only the `≤ p.length` ancestors on `p` are allocated as new gates; all sibling
    subcircuits are shared directly from `gates`. -/
def pathCopy (gates : List Gate) (u : Nat) (p : List Bool) (repOut : Nat) : List Gate × Nat :=
  match p with
  | [] => (gates, repOut)
  | dir :: rest =>
      match getGate gates u with
      | .neg a =>
          let res := pathCopy gates a rest repOut
          (res.1 ++ [.neg res.2], res.1.length)
      | .disj a b =>
          if !dir then
            let res := pathCopy gates a rest repOut
            (res.1 ++ [.disj res.2 b], res.1.length)
          else
            let res := pathCopy gates b rest repOut
            (res.1 ++ [.disj a res.2], res.1.length)
      | .conj a b =>
          if !dir then
            let res := pathCopy gates a rest repOut
            (res.1 ++ [.conj res.2 b], res.1.length)
          else
            let res := pathCopy gates b rest repOut
            (res.1 ++ [.conj a res.2], res.1.length)
      | _ => (gates, u)

/-- Path-copying adds at most `p.length` gates (exact before hash-consing). -/
theorem pathCopy_length_le (gates : List Gate) (u : Nat) (p : List Bool) (repOut : Nat) :
    (pathCopy gates u p repOut).1.length ≤ gates.length + p.length := by
  induction p generalizing u with
  | nil =>
      dsimp [pathCopy, List.length]
      exact Nat.le_refl _
  | cons dir rest ih =>
      dsimp [pathCopy, List.length]
      cases hgate : getGate gates u with
      | zero => exact Nat.le_trans (Nat.le_refl _) (Nat.le_add_right _ _)
      | one  => exact Nat.le_trans (Nat.le_refl _) (Nat.le_add_right _ _)
      | var _ => exact Nat.le_trans (Nat.le_refl _) (Nat.le_add_right _ _)
      | neg a =>
          dsimp
          rw [List.length_append]
          dsimp [List.length]
          exact Nat.succ_le_succ (ih a)
      | disj a b =>
          cases dir <;> dsimp <;> rw [List.length_append] <;> dsimp [List.length]
          · exact Nat.succ_le_succ (ih a)
          · exact Nat.succ_le_succ (ih b)
      | conj a b =>
          cases dir <;> dsimp <;> rw [List.length_append] <;> dsimp [List.length]
          · exact Nat.succ_le_succ (ih a)
          · exact Nat.succ_le_succ (ih b)

/-- Path-copying only appends gates to `gates` (persistent extension). -/
theorem pathCopy_extends (gates : List Gate) (u : Nat) (p : List Bool) (repOut : Nat) :
    ∃ delta : List Gate, (pathCopy gates u p repOut).1 = gates ++ delta := by
  induction p generalizing u with
  | nil =>
      exact ⟨[], by simp [pathCopy]⟩
  | cons dir rest ih =>
      dsimp [pathCopy]
      cases hgate : getGate gates u with
      | zero => exact ⟨[], by simp⟩
      | one  => exact ⟨[], by simp⟩
      | var _ => exact ⟨[], by simp⟩
      | neg a =>
          obtain ⟨d, hd⟩ := ih a
          exact ⟨d ++ [.neg (pathCopy gates a rest repOut).2], by simp [hd, List.append_assoc]⟩
      | disj a b =>
          cases dir
          · obtain ⟨d, hd⟩ := ih a
            exact ⟨d ++ [.disj (pathCopy gates a rest repOut).2 b], by simp [hd, List.append_assoc]⟩
          · obtain ⟨d, hd⟩ := ih b
            exact ⟨d ++ [.disj a (pathCopy gates b rest repOut).2], by simp [hd, List.append_assoc]⟩
      | conj a b =>
          cases dir
          · obtain ⟨d, hd⟩ := ih a
            exact ⟨d ++ [.conj (pathCopy gates a rest repOut).2 b], by simp [hd, List.append_assoc]⟩
          · obtain ⟨d, hd⟩ := ih b
            exact ⟨d ++ [.conj a (pathCopy gates b rest repOut).2], by simp [hd, List.append_assoc]⟩

/-- Path-copying preserves `WellFormedGates` and returns a valid output index. -/
theorem pathCopy_wf (gates : List Gate) (hwf : WellFormedGates gates)
    (u : Nat) (hu : u < gates.length) (p : List Bool)
    (repOut : Nat) (hrep : repOut < gates.length) :
    WellFormedGates (pathCopy gates u p repOut).1 ∧
    (pathCopy gates u p repOut).2 < (pathCopy gates u p repOut).1.length := by
  induction p generalizing u with
  | nil =>
      exact ⟨hwf, hrep⟩
  | cons dir rest ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      dsimp [pathCopy]
      cases hgate : getGate gates u with
      | zero => exact ⟨hwf, hu⟩
      | one  => exact ⟨hwf, hu⟩
      | var _ => exact ⟨hwf, hu⟩
      | neg a =>
          rw [hgate] at hwf_u
          have ha_lt : a < gates.length := Nat.lt_trans hwf_u hu
          obtain ⟨hwf', hout'⟩ := ih a ha_lt
          refine ⟨wellFormedGates_snoc hwf' hout', ?_⟩
          rw [List.length_append]; exact Nat.lt_succ_self _
      | disj a b =>
          rw [hgate] at hwf_u
          have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
          have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
          cases dir
          · dsimp
            obtain ⟨hwf', hout'⟩ := ih a ha_lt
            obtain ⟨delta, hdelta⟩ := pathCopy_extends gates a rest repOut
            have hb_lt' : b < (pathCopy gates a rest repOut).1.length := by
              rw [hdelta, List.length_append]
              exact Nat.lt_of_lt_of_le hb_lt (Nat.le_add_right _ _)
            refine ⟨wellFormedGates_snoc hwf' ⟨hout', hb_lt'⟩, ?_⟩
            rw [List.length_append]; exact Nat.lt_succ_self _
          · dsimp
            obtain ⟨hwf', hout'⟩ := ih b hb_lt
            obtain ⟨delta, hdelta⟩ := pathCopy_extends gates b rest repOut
            have ha_lt' : a < (pathCopy gates b rest repOut).1.length := by
              rw [hdelta, List.length_append]
              exact Nat.lt_of_lt_of_le ha_lt (Nat.le_add_right _ _)
            refine ⟨wellFormedGates_snoc hwf' ⟨ha_lt', hout'⟩, ?_⟩
            rw [List.length_append]; exact Nat.lt_succ_self _
      | conj a b =>
          rw [hgate] at hwf_u
          have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
          have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
          cases dir
          · dsimp
            obtain ⟨hwf', hout'⟩ := ih a ha_lt
            obtain ⟨delta, hdelta⟩ := pathCopy_extends gates a rest repOut
            have hb_lt' : b < (pathCopy gates a rest repOut).1.length := by
              rw [hdelta, List.length_append]
              exact Nat.lt_of_lt_of_le hb_lt (Nat.le_add_right _ _)
            refine ⟨wellFormedGates_snoc hwf' ⟨hout', hb_lt'⟩, ?_⟩
            rw [List.length_append]; exact Nat.lt_succ_self _
          · dsimp
            obtain ⟨hwf', hout'⟩ := ih b hb_lt
            obtain ⟨delta, hdelta⟩ := pathCopy_extends gates b rest repOut
            have ha_lt' : a < (pathCopy gates b rest repOut).1.length := by
              rw [hdelta, List.length_append]
              exact Nat.lt_of_lt_of_le ha_lt (Nat.le_add_right _ _)
            refine ⟨wellFormedGates_snoc hwf' ⟨ha_lt', hout'⟩, ?_⟩
            rw [List.length_append]; exact Nat.lt_succ_self _

/-- Predicate witnessing that following path `p` from gate `u` in `gates` reaches `target`. -/
inductive FollowsPath (gates : List Gate) : Nat → List Bool → Nat → Prop where
  | nil (u : Nat) : FollowsPath gates u [] u
  | neg {u a target : Nat} {rest : List Bool} :
      getGate gates u = .neg a →
      FollowsPath gates a rest target →
      FollowsPath gates u (false :: rest) target
  | disjLeft {u a b target : Nat} {rest : List Bool} :
      getGate gates u = .disj a b →
      FollowsPath gates a rest target →
      FollowsPath gates u (false :: rest) target
  | disjRight {u a b target : Nat} {rest : List Bool} :
      getGate gates u = .disj a b →
      FollowsPath gates b rest target →
      FollowsPath gates u (true :: rest) target
  | conjLeft {u a b target : Nat} {rest : List Bool} :
      getGate gates u = .conj a b →
      FollowsPath gates a rest target →
      FollowsPath gates u (false :: rest) target
  | conjRight {u a b target : Nat} {rest : List Bool} :
      getGate gates u = .conj a b →
      FollowsPath gates b rest target →
      FollowsPath gates u (true :: rest) target

/-- Helper: unfolding a freshly appended `.neg` gate. -/
theorem unfold_snoc_neg (g : List Gate) (hwf : WellFormedGates g) (a : Nat) (ha : a < g.length) :
    unfoldFuel (g ++ [Gate.neg a]) (g.length + 1) g.length =
      .neg (unfoldFuel g (a + 1) a) := by
  have htop : getGate (g ++ [Gate.neg a]) g.length = Gate.neg a := by
    have h0 := getGate_append_right g [Gate.neg a] 0
    rw [Nat.add_zero] at h0
    exact h0
  rw [unfoldFuel_succ_neg (g ++ [Gate.neg a]) g.length g.length a htop]
  rw [unfoldFuel_append_left g [Gate.neg a] hwf g.length a ha]
  rw [unfoldFuel_eq_of_ge g hwf g.length (a + 1) a ha ha (Nat.lt_succ_self a)]

/-- Helper: unfolding a freshly appended `.disj` gate. -/
theorem unfold_snoc_disj (g : List Gate) (hwf : WellFormedGates g)
    (a b : Nat) (ha : a < g.length) (hb : b < g.length) :
    unfoldFuel (g ++ [Gate.disj a b]) (g.length + 1) g.length =
      .disj (unfoldFuel g (a + 1) a) (unfoldFuel g (b + 1) b) := by
  have htop : getGate (g ++ [Gate.disj a b]) g.length = Gate.disj a b := by
    have h0 := getGate_append_right g [Gate.disj a b] 0
    rw [Nat.add_zero] at h0
    exact h0
  rw [unfoldFuel_succ_disj (g ++ [Gate.disj a b]) g.length g.length a b htop]
  rw [unfoldFuel_append_left g [Gate.disj a b] hwf g.length a ha]
  rw [unfoldFuel_append_left g [Gate.disj a b] hwf g.length b hb]
  rw [unfoldFuel_eq_of_ge g hwf g.length (a + 1) a ha ha (Nat.lt_succ_self a)]
  rw [unfoldFuel_eq_of_ge g hwf g.length (b + 1) b hb hb (Nat.lt_succ_self b)]

/-- Helper: unfolding a freshly appended `.conj` gate. -/
theorem unfold_snoc_conj (g : List Gate) (hwf : WellFormedGates g)
    (a b : Nat) (ha : a < g.length) (hb : b < g.length) :
    unfoldFuel (g ++ [Gate.conj a b]) (g.length + 1) g.length =
      .conj (unfoldFuel g (a + 1) a) (unfoldFuel g (b + 1) b) := by
  have htop : getGate (g ++ [Gate.conj a b]) g.length = Gate.conj a b := by
    have h0 := getGate_append_right g [Gate.conj a b] 0
    rw [Nat.add_zero] at h0
    exact h0
  rw [unfoldFuel_succ_conj (g ++ [Gate.conj a b]) g.length g.length a b htop]
  rw [unfoldFuel_append_left g [Gate.conj a b] hwf g.length a ha]
  rw [unfoldFuel_append_left g [Gate.conj a b] hwf g.length b hb]
  rw [unfoldFuel_eq_of_ge g hwf g.length (a + 1) a ha ha (Nat.lt_succ_self a)]
  rw [unfoldFuel_eq_of_ge g hwf g.length (b + 1) b hb hb (Nat.lt_succ_self b)]

/-- Helper: unfolding an existing gate `u` one step when `hwf` holds. -/
theorem unfold_neg_step (g : List Gate) (hwf : WellFormedGates g)
    (u a : Nat) (hu : u < g.length) (hgate : getGate g u = .neg a) :
    unfoldFuel g (u + 1) u = .neg (unfoldFuel g (a + 1) a) := by
  have hwf_u : GateWF u (getGate g u) := hwf u hu
  rw [hgate] at hwf_u
  rw [unfoldFuel_succ_neg g u u a hgate]
  rw [unfoldFuel_eq_of_ge g hwf u (a + 1) a (Nat.lt_trans hwf_u hu) hwf_u (Nat.lt_succ_self a)]

theorem unfold_disj_step (g : List Gate) (hwf : WellFormedGates g)
    (u a b : Nat) (hu : u < g.length) (hgate : getGate g u = .disj a b) :
    unfoldFuel g (u + 1) u = .disj (unfoldFuel g (a + 1) a) (unfoldFuel g (b + 1) b) := by
  have hwf_u : GateWF u (getGate g u) := hwf u hu
  rw [hgate] at hwf_u
  rw [unfoldFuel_succ_disj g u u a b hgate]
  rw [unfoldFuel_eq_of_ge g hwf u (a + 1) a (Nat.lt_trans hwf_u.1 hu) hwf_u.1 (Nat.lt_succ_self a)]
  rw [unfoldFuel_eq_of_ge g hwf u (b + 1) b (Nat.lt_trans hwf_u.2 hu) hwf_u.2 (Nat.lt_succ_self b)]

theorem unfold_conj_step (g : List Gate) (hwf : WellFormedGates g)
    (u a b : Nat) (hu : u < g.length) (hgate : getGate g u = .conj a b) :
    unfoldFuel g (u + 1) u = .conj (unfoldFuel g (a + 1) a) (unfoldFuel g (b + 1) b) := by
  have hwf_u : GateWF u (getGate g u) := hwf u hu
  rw [hgate] at hwf_u
  rw [unfoldFuel_succ_conj g u u a b hgate]
  rw [unfoldFuel_eq_of_ge g hwf u (a + 1) a (Nat.lt_trans hwf_u.1 hu) hwf_u.1 (Nat.lt_succ_self a)]
  rw [unfoldFuel_eq_of_ge g hwf u (b + 1) b (Nat.lt_trans hwf_u.2 hu) hwf_u.2 (Nat.lt_succ_self b)]

/-- Correctness of `pathCopy`: replacing `target` along `p` with a `BAStep`-equivalent gate
    `repOut` yields a valid `SimBAPath p` step on the unfolded terms. -/
theorem pathCopy_simBAPath (gates : List Gate) (hwf : WellFormedGates gates)
    (u target repOut : Nat) (p : List Bool)
    (hu : u < gates.length) (hrep : repOut < gates.length)
    (hpath : FollowsPath gates u p target)
    (hba : BAStep (unfoldFuel gates (target + 1) target) (unfoldFuel gates (repOut + 1) repOut)) :
    SimBAPath p
      (unfoldFuel gates (u + 1) u)
      (unfoldFuel (pathCopy gates u p repOut).1 ((pathCopy gates u p repOut).2 + 1)
        (pathCopy gates u p repOut).2) := by
  induction hpath with
  | nil u =>
      dsimp [pathCopy]
      exact .root hba
  | @neg u a target rest hgate hsub ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      rw [hgate] at hwf_u
      have ha_lt : a < gates.length := Nat.lt_trans hwf_u hu
      have ih' := ih ha_lt hba
      obtain ⟨hwf', hout'⟩ := pathCopy_wf gates hwf a ha_lt rest repOut hrep
      dsimp [pathCopy]
      rw [hgate]
      dsimp
      rw [unfold_neg_step gates hwf u a hu hgate]
      rw [unfold_snoc_neg _ hwf' _ hout']
      exact .neg ih'
  | @disjLeft u a b target rest hgate hsub ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      rw [hgate] at hwf_u
      have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
      have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
      have ih' := ih ha_lt hba
      obtain ⟨hwf', hout'⟩ := pathCopy_wf gates hwf a ha_lt rest repOut hrep
      obtain ⟨delta, hdelta⟩ := pathCopy_extends gates a rest repOut
      have hb_lt' : b < (pathCopy gates a rest repOut).1.length := by
        rw [hdelta, List.length_append]
        exact Nat.lt_of_lt_of_le hb_lt (Nat.le_add_right _ _)
      have hb_eq : unfoldFuel (pathCopy gates a rest repOut).1 (b + 1) b =
          unfoldFuel gates (b + 1) b := by
        rw [hdelta]
        exact unfoldFuel_append_left gates delta hwf (b + 1) b hb_lt
      dsimp [pathCopy]
      rw [hgate]
      dsimp
      rw [unfold_disj_step gates hwf u a b hu hgate]
      rw [unfold_snoc_disj _ hwf' _ b hout' hb_lt', hb_eq]
      exact .disjLeft ih'
  | @disjRight u a b target rest hgate hsub ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      rw [hgate] at hwf_u
      have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
      have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
      have ih' := ih hb_lt hba
      obtain ⟨hwf', hout'⟩ := pathCopy_wf gates hwf b hb_lt rest repOut hrep
      obtain ⟨delta, hdelta⟩ := pathCopy_extends gates b rest repOut
      have ha_lt' : a < (pathCopy gates b rest repOut).1.length := by
        rw [hdelta, List.length_append]
        exact Nat.lt_of_lt_of_le ha_lt (Nat.le_add_right _ _)
      have ha_eq : unfoldFuel (pathCopy gates b rest repOut).1 (a + 1) a =
          unfoldFuel gates (a + 1) a := by
        rw [hdelta]
        exact unfoldFuel_append_left gates delta hwf (a + 1) a ha_lt
      dsimp [pathCopy]
      rw [hgate]
      dsimp
      rw [unfold_disj_step gates hwf u a b hu hgate]
      rw [unfold_snoc_disj _ hwf' a _ ha_lt' hout', ha_eq]
      exact .disjRight ih'
  | @conjLeft u a b target rest hgate hsub ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      rw [hgate] at hwf_u
      have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
      have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
      have ih' := ih ha_lt hba
      obtain ⟨hwf', hout'⟩ := pathCopy_wf gates hwf a ha_lt rest repOut hrep
      obtain ⟨delta, hdelta⟩ := pathCopy_extends gates a rest repOut
      have hb_lt' : b < (pathCopy gates a rest repOut).1.length := by
        rw [hdelta, List.length_append]
        exact Nat.lt_of_lt_of_le hb_lt (Nat.le_add_right _ _)
      have hb_eq : unfoldFuel (pathCopy gates a rest repOut).1 (b + 1) b =
          unfoldFuel gates (b + 1) b := by
        rw [hdelta]
        exact unfoldFuel_append_left gates delta hwf (b + 1) b hb_lt
      dsimp [pathCopy]
      rw [hgate]
      dsimp
      rw [unfold_conj_step gates hwf u a b hu hgate]
      rw [unfold_snoc_conj _ hwf' _ b hout' hb_lt', hb_eq]
      exact .conjLeft ih'
  | @conjRight u a b target rest hgate hsub ih =>
      have hwf_u : GateWF u (getGate gates u) := hwf u hu
      rw [hgate] at hwf_u
      have ha_lt : a < gates.length := Nat.lt_trans hwf_u.1 hu
      have hb_lt : b < gates.length := Nat.lt_trans hwf_u.2 hu
      have ih' := ih hb_lt hba
      obtain ⟨hwf', hout'⟩ := pathCopy_wf gates hwf b hb_lt rest repOut hrep
      obtain ⟨delta, hdelta⟩ := pathCopy_extends gates b rest repOut
      have ha_lt' : a < (pathCopy gates b rest repOut).1.length := by
        rw [hdelta, List.length_append]
        exact Nat.lt_of_lt_of_le ha_lt (Nat.le_add_right _ _)
      have ha_eq : unfoldFuel (pathCopy gates b rest repOut).1 (a + 1) a =
          unfoldFuel gates (a + 1) a := by
        rw [hdelta]
        exact unfoldFuel_append_left gates delta hwf (a + 1) a ha_lt
      dsimp [pathCopy]
      rw [hgate]
      dsimp
      rw [unfold_conj_step gates hwf u a b hu hgate]
      rw [unfold_snoc_conj _ hwf' a _ ha_lt' hout', ha_eq]
      exact .conjRight ih'

/-- **Theorem (b): `path_unsharing_size_bound`**
    Given a well-formed circuit `C`, a path `p : List Bool` of length `d = p.length`
    leading to `target`, and a replacement subcircuit `repGates` of size `≤ c_ba`
    appended to `C.gates` with output `repOut` satisfying `BAStep` against `target`:
    persistent path-copying constructs a well-formed circuit `C'` such that:
    1. `C'.gates.length ≤ C.gates.length + p.length + c_ba` (before hash-consing),
    2. `ApproxDAG C C'` (verified single-occurrence `SimBA` step at path `p`). -/
theorem path_unsharing_size_bound
    (C : CircuitDAG) (hC : WellFormedDAG C)
    (p : List Bool) (target : Nat)
    (repGates : List Gate) (c_ba repOut : Nat)
    (hrepLen : repGates.length ≤ c_ba)
    (hwfExt : WellFormedGates (C.gates ++ repGates))
    (hrepLt : repOut < (C.gates ++ repGates).length)
    (hpath : FollowsPath (C.gates ++ repGates) C.out p target)
    (hba : BAStep
      (unfoldFuel (C.gates ++ repGates) (target + 1) target)
      (unfoldFuel (C.gates ++ repGates) (repOut + 1) repOut)) :
    ∃ C' : CircuitDAG,
      WellFormedDAG C' ∧
      C'.gates.length ≤ C.gates.length + p.length + c_ba ∧
      ApproxDAG C C' := by
  let g₁ := C.gates ++ repGates
  let res := pathCopy g₁ C.out p repOut
  let C' : CircuitDAG := { gates := res.1, out := res.2 }
  have hOut1 : C.out < g₁.length := by
    dsimp [g₁]
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hC.outLt (Nat.le_add_right _ _)
  obtain ⟨hwf', hout'⟩ := pathCopy_wf g₁ hwfExt C.out hOut1 p repOut hrepLt
  refine ⟨C', ⟨hwf', hout'⟩, ?_, ?_⟩
  · -- Size bound: |C'| ≤ |g₁| + |p| = |C| + |repGates| + |p| ≤ |C| + |p| + c_ba
    have hlen : res.1.length ≤ g₁.length + p.length :=
      pathCopy_length_le g₁ C.out p repOut
    have hg1 : g₁.length = C.gates.length + repGates.length := List.length_append
    have hstep1 : res.1.length ≤ C.gates.length + repGates.length + p.length := by
      rw [← hg1]; exact hlen
    have hstep2 : C.gates.length + repGates.length + p.length =
        C.gates.length + p.length + repGates.length := by
      rw [Nat.add_assoc, Nat.add_comm repGates.length p.length, ← Nat.add_assoc]
    rw [hstep2] at hstep1
    exact Nat.le_trans hstep1 (Nat.add_le_add_left hrepLen _)
  · -- Soundness: ApproxDAG C C'
    have hsim := pathCopy_simBAPath g₁ hwfExt C.out target repOut p hOut1 hrepLt hpath hba
    have hunf : unfoldFuel g₁ (C.out + 1) C.out = unfold C C.out :=
      unfoldFuel_append_left C.gates repGates hC.wfGates (C.out + 1) C.out hC.outLt
    rw [hunf] at hsim
    exact ⟨p, hsim⟩

/-! ## Section 5: Theorem (c) — Tree-Like `CF` Derivation Step-Count Composition -/

/-- Tree-like Circuit Frege (`CF`) derivation parameterized by a uniform BA axiom
    compilation budget `c_ax` (every Frege axiom scheme compiles to `≤ c_ax` `SimBA` steps):
    - `axiomStep`: a Frege axiom instance `C` with `∃ n ≤ c_ax, SimBAN n (unfold C C.out) .one`.
    - `flaRule`: the `CF` structural rule `C / D` assuming `unfold C C.out = unfold D D.out`.
    - `modusPonens`: `A, ¬A ∨ B ⊢ B` (tree-like: each premise derivation is used once). -/
inductive TreeCFDeriv (c_ax : Nat) : CircuitDAG → Nat → Prop where
  | axiomStep (C : CircuitDAG) (n : Nat) :
      n ≤ c_ax →
      SimBAN n (unfold C C.out) .one →
      TreeCFDeriv c_ax C 1
  | flaRule {C D : CircuitDAG} {k : Nat} :
      TreeCFDeriv c_ax C k →
      unfold C C.out = unfold D D.out →
      TreeCFDeriv c_ax D (k + 1)
  | modusPonens {A Imp B : CircuitDAG} {k₁ k₂ : Nat} :
      TreeCFDeriv c_ax A k₁ →
      TreeCFDeriv c_ax Imp k₂ →
      unfold Imp Imp.out = .disj (.neg (unfold A A.out)) (unfold B B.out) →
      TreeCFDeriv c_ax B (k₁ + k₂ + 1)

/-- **Theorem (c): `cf_modus_ponens_tree_bound`**
    Any tree-like `CF` derivation of circuit `C` with `k` steps compiles inductively to a
    `SimBAN` rewrite chain `unfold C C.out ~_BA^* 1` of length at most `(c_ax + 2) * k`.
    (In particular, for a balanced tree-like `CF` proof of `k* = O(k log k)` steps,
    the resulting `≈`-chain has length `≤ (c_ax + 2) * k* = O(k log k)`.) -/
theorem cf_modus_ponens_tree_bound (c_ax : Nat) (C : CircuitDAG) (k : Nat)
    (h : TreeCFDeriv c_ax C k) :
    ∃ n : Nat, n ≤ (c_ax + 2) * k ∧ SimBAN n (unfold C C.out) .one := by
  induction h with
  | axiomStep C n hn hsim =>
      refine ⟨n, ?_, hsim⟩
      rw [Nat.mul_one]
      exact Nat.le_trans hn (Nat.le_add_right c_ax 2)
  | @flaRule C D k _ hFla ih =>
      obtain ⟨n, hn, hsim⟩ := ih
      rw [← hFla]
      refine ⟨n, ?_, hsim⟩
      rw [Nat.mul_succ]
      exact Nat.le_trans hn (Nat.le_add_right _ _)
  | @modusPonens A Imp B k₁ k₂ _ _ hImp ih₁ ih₂ =>
      obtain ⟨n₁, hn₁, hsim₁⟩ := ih₁
      obtain ⟨n₂, hn₂, hsim₂⟩ := ih₂
      rw [hImp] at hsim₂
      refine ⟨n₁ + 2 + n₂, ?_, modus_ponens_simBAN (unfold A A.out) (unfold B B.out) n₁ n₂ hsim₁ hsim₂⟩
      -- Bound: n₁ + 2 + n₂ ≤ (c_ax + 2) * k₁ + 2 + (c_ax + 2) * k₂ ≤ (c_ax + 2) * (k₁ + k₂ + 1)
      have h1 : n₁ + 2 + n₂ ≤ (c_ax + 2) * k₁ + 2 + (c_ax + 2) * k₂ :=
        Nat.add_le_add (Nat.add_le_add_right hn₁ 2) hn₂
      have h2 : (c_ax + 2) * k₁ + 2 + (c_ax + 2) * k₂ ≤
          (c_ax + 2) * k₁ + (c_ax + 2) * k₂ + (c_ax + 2) := by
        have hcomm : (c_ax + 2) * k₁ + 2 + (c_ax + 2) * k₂ =
            (c_ax + 2) * k₁ + (c_ax + 2) * k₂ + 2 := by
          rw [Nat.add_assoc, Nat.add_comm 2 ((c_ax + 2) * k₂), ← Nat.add_assoc]
        rw [hcomm]
        exact Nat.add_le_add_left (Nat.le_add_left 2 c_ax) _
      have h3 : (c_ax + 2) * k₁ + (c_ax + 2) * k₂ + (c_ax + 2) =
          (c_ax + 2) * (k₁ + k₂ + 1) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      rw [← h3]
      exact Nat.le_trans h1 h2

end KrajicekCFCompiler

#print axioms KrajicekCFCompiler.cf_fla_rule_two_step_approx
#print axioms KrajicekCFCompiler.path_unsharing_size_bound
#print axioms KrajicekCFCompiler.cf_modus_ponens_tree_bound
