/-!
# Constructive Bug-Extraction & Proof Analysis Soundness (ATAQUE-08)

Formalization of:
1. Binary-Search Bug Localization on Alleged `≈`-Chains (`findBrokenStep`, `locateBug`,
   `binary_search_bug_step_correct`), with both `O(log₂ t)` fuel sufficiency (`2^fuel ≥ t`)
   and linear-fuel (`fuel = t`) correctness.
2. Soundness Dichotomy (`bug_or_tautology_dichotomy`): for any alleged chain
   `E₀, E₁, ..., Eₜ` ending at `1`, either every step `i < t` is semantically equivalent
   (so `E₀` is a tautology), or there exists a step `i < t` and a falsifying assignment
   `x*` witnessing `Eᵢ(x*) ≠ Eᵢ₊₁(x*)`.
3. Constructive Witness-to-Broken-Step Extraction (`constructive_bug_extraction`):
   given any falsifying assignment `x*` for `E₀` and a valid endpoint `Eₜ ≡ 1`,
   `locateBug (fun i => eval (E i) x*) t` constructively returns `idx < t` with
   `eval (E idx) x* = false` and `eval (E (idx + 1)) x* = true`.

Standalone Lean 4.36.0, 0 imports, 0 `sorry`, audited with `#print axioms`.
-/

namespace ProofAnalysisBugExtractor

/-- Binary-search midpoint bisection over `chain : Nat → Bool` on `[lo, hi]` with `fuel` steps. -/
def findBrokenStep (chain : Nat → Bool) (lo hi : Nat) : Nat → Nat
  | 0 => lo
  | fuel + 1 =>
    if hi ≤ lo + 1 then
      lo
    else
      let mid := (lo + hi) / 2
      if chain mid then
        findBrokenStep chain lo mid fuel
      else
        findBrokenStep chain mid hi fuel

/-- Locate a broken step `i < t` using `t` fuel (also sufficient with `Nat.log2 t + 1`). -/
def locateBug (chain : Nat → Bool) (t : Nat) : Nat :=
  findBrokenStep chain 0 t t

/-- Logarithmic-fuel bug locator: uses `log2Bound t` steps (`O(log t)` evaluations). -/
def locateBugLog (chain : Nat → Bool) (t fuel : Nat) : Nat :=
  findBrokenStep chain 0 t fuel

private theorem two_pow_ge_self : ∀ n : Nat, n ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := two_pow_ge_self n
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
    omega

private theorem mid_sub_lo_le {lo hi k : Nat} (hlo : lo < hi) (hle : hi - lo ≤ 2 * k) :
    (lo + hi) / 2 - lo ≤ k := by
  omega

private theorem hi_sub_mid_le {lo hi k : Nat} (hlo : lo < hi) (hle : hi - lo ≤ 2 * k) :
    hi - (lo + hi) / 2 ≤ k := by
  omega

/-- Core invariant for `findBrokenStep`:
    Whenever `lo < hi`, `hi - lo ≤ 2 ^ fuel`, `chain lo = false`, and `chain hi = true`,
    `findBrokenStep chain lo hi fuel` returns `idx` with
    `lo ≤ idx ∧ idx < hi ∧ chain idx = false ∧ chain (idx + 1) = true`. -/
theorem findBrokenStep_spec :
    ∀ (fuel : Nat) (chain : Nat → Bool) (lo hi : Nat),
      lo < hi →
      hi - lo ≤ 2 ^ fuel →
      chain lo = false →
      chain hi = true →
      let idx := findBrokenStep chain lo hi fuel
      lo ≤ idx ∧ idx < hi ∧ chain idx = false ∧ chain (idx + 1) = true
  | 0, chain, lo, hi, hlt, hbound, hlo, hhi => by
    have hpow : 2 ^ 0 = 1 := rfl
    have heq : hi = lo + 1 := by omega
    simp only [findBrokenStep]
    refine ⟨Nat.le_refl lo, hlt, hlo, ?_⟩
    rw [← heq]
    exact hhi
  | fuel + 1, chain, lo, hi, hlt, hbound, hlo, hhi => by
    simp only [findBrokenStep]
    by_cases hbase : hi ≤ lo + 1
    · simp only [hbase, ↓reduceIte]
      have heq : hi = lo + 1 := by omega
      refine ⟨Nat.le_refl lo, hlt, hlo, ?_⟩
      rw [← heq]
      exact hhi
    · simp only [hbase, ↓reduceIte]
      have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hbound2 : hi - lo ≤ 2 * 2 ^ fuel := by omega
      have hlo_mid : lo < (lo + hi) / 2 := by omega
      have hmid_hi : (lo + hi) / 2 < hi := by omega
      have hleft_len : (lo + hi) / 2 - lo ≤ 2 ^ fuel :=
        mid_sub_lo_le hlt hbound2
      have hright_len : hi - (lo + hi) / 2 ≤ 2 ^ fuel :=
        hi_sub_mid_le hlt hbound2
      cases hmid : chain ((lo + hi) / 2)
      · -- chain mid = false: recurse on [mid, hi]
        have ih := findBrokenStep_spec fuel chain ((lo + hi) / 2) hi hmid_hi hright_len hmid hhi
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases ih with ⟨h1, h2, h3, h4⟩
        exact ⟨Nat.le_trans (Nat.le_of_lt hlo_mid) h1, h2, h3, h4⟩
      · -- chain mid = true: recurse on [lo, mid]
        have ih := findBrokenStep_spec fuel chain lo ((lo + hi) / 2) hlo_mid hleft_len hlo hmid
        simp only [↓reduceIte]
        rcases ih with ⟨h1, h2, h3, h4⟩
        exact ⟨h1, Nat.lt_trans h2 hmid_hi, h3, h4⟩

/-- **Binary-Search Bug Localization on Alleged `≈`-Chains**:
    For any `t ≥ 1` and `chain : Nat → Bool` with `chain 0 = false` and `chain t = true`,
    `locateBug chain t` returns an index `idx < t` with `chain idx = false` and `chain (idx + 1) = true`. -/
theorem binary_search_bug_step_correct :
    ∀ (t : Nat) (chain : Nat → Bool),
      t ≥ 1 →
      chain 0 = false →
      chain t = true →
      let idx := locateBug chain t
      idx < t ∧ chain idx = false ∧ chain (idx + 1) = true := by
  intro t chain ht h0 h1
  have hbound : t - 0 ≤ 2 ^ t := by
    rw [Nat.sub_zero]
    exact two_pow_ge_self t
  have hspec := findBrokenStep_spec t chain 0 t ht hbound h0 h1
  rcases hspec with ⟨_, hlt, hfalse, htrue⟩
  exact ⟨hlt, hfalse, htrue⟩

/-- **Logarithmic-Fuel Variant**:
    For any `fuel` with `t ≤ 2 ^ fuel` (i.e. `fuel = O(log₂ t)`),
    `locateBugLog chain t fuel` finds `idx < t` with `chain idx = false` and `chain (idx + 1) = true`. -/
theorem binary_search_bug_step_log_correct :
    ∀ (t fuel : Nat) (chain : Nat → Bool),
      t ≥ 1 →
      t ≤ 2 ^ fuel →
      chain 0 = false →
      chain t = true →
      let idx := locateBugLog chain t fuel
      idx < t ∧ chain idx = false ∧ chain (idx + 1) = true := by
  intro t fuel chain ht hpow h0 h1
  have hbound : t - 0 ≤ 2 ^ fuel := by omega
  have hspec := findBrokenStep_spec fuel chain 0 t ht hbound h0 h1
  rcases hspec with ⟨_, hlt, hfalse, htrue⟩
  exact ⟨hlt, hfalse, htrue⟩

/-- Helper: if every step `i < t` preserves evaluation at `x` and `eval t x = true`,
    then `eval 0 x = true`. -/
theorem chain_sound_at_env (eval : Nat → α → Bool) (t : Nat) (x : α)
    (hsteps : ∀ i, i < t → eval i x = eval (i + 1) x)
    (ht : eval t x = true) : eval 0 x = true := by
  have hreach : ∀ k, k ≤ t → eval (t - k) x = true := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero]
      exact ht
    | succ k ih =>
      have hk_le : k ≤ t := Nat.le_of_succ_le hk
      have hlt : t - (k + 1) < t := by omega
      have heq : t - (k + 1) + 1 = t - k := by omega
      have hstep := hsteps (t - (k + 1)) hlt
      rw [heq] at hstep
      rw [hstep]
      exact ih hk_le
  have h0 := hreach t (Nat.le_refl t)
  rw [Nat.sub_self] at h0
  exact h0

/-- **Soundness Dichotomy (Bug-Extractor vs Tautology)**:
    For any chain of Boolean formulas/circuits `E₀, ..., Eₜ` (abstracted by `eval : Nat → Env → Bool`)
    whose endpoint `Eₜ` is a tautology (`∀ x, eval t x = true`),
    EITHER every step `i < t` is semantically equivalent (`∀ i < t, ∀ x, eval i x = eval (i + 1) x`),
      which implies `E₀` is a tautology (`∀ x, eval 0 x = true`),
    OR there exists a step `i < t` and a local witness `x*` falsifying `Eᵢ ≡ Eᵢ₊₁`
      (`eval i x* ≠ eval (i + 1) x*`). -/
theorem bug_or_tautology_dichotomy {Env : Type} (eval : Nat → Env → Bool) (t : Nat)
    (ht : ∀ x, eval t x = true) :
    ((∀ i, i < t → ∀ x, eval i x = eval (i + 1) x) ∧ (∀ x, eval 0 x = true)) ∨
    (∃ i, i < t ∧ ∃ x, eval i x ≠ eval (i + 1) x) := by
  by_cases h : ∀ i, i < t → ∀ x, eval i x = eval (i + 1) x
  · left
    refine ⟨h, ?_⟩
    intro x
    exact chain_sound_at_env eval t x (fun i hi => h i hi x) (ht x)
  · right
    have hnot : ¬ ∀ i, i < t → ∀ x, eval i x = eval (i + 1) x := h
    -- Classical witness extraction from negated universal quantifier
    exact Classical.byContradiction fun hno =>
      hnot fun i hi x =>
        Classical.byContradiction fun hne =>
          hno ⟨i, hi, x, hne⟩

/-- **Constructive Bug Extraction from a Falsifying Assignment**:
    Given `t ≥ 1`, an endpoint tautology `∀ x, eval t x = true`, and a falsifying
    assignment `x*` for `E₀` (`eval 0 x* = false`), `locateBug (fun i => eval i x*) t`
    constructively yields a broken step `idx < t` with `eval idx x* = false` and
    `eval (idx + 1) x* = true`. -/
theorem constructive_bug_extraction {Env : Type} (eval : Nat → Env → Bool) (t : Nat)
    (ht_ge : t ≥ 1)
    (ht : ∀ x, eval t x = true)
    (x_star : Env)
    (hfals : eval 0 x_star = false) :
    let idx := locateBug (fun i => eval i x_star) t
    idx < t ∧ eval idx x_star = false ∧ eval (idx + 1) x_star = true :=
  binary_search_bug_step_correct t (fun i => eval i x_star) ht_ge hfals (ht x_star)

#print axioms binary_search_bug_step_correct
#print axioms binary_search_bug_step_log_correct
#print axioms bug_or_tautology_dichotomy
#print axioms constructive_bug_extraction

end ProofAnalysisBugExtractor
