/-
  ATAQUE-09: Universal `∀ n` 2-Adic Torsion Law in Nisan Matrices for Witt Carries
  ================================================================================
  Standalone Lean 4.36.0 formalization (zero imports, zero `sorryAx`,
  `#print axioms` audited).

  Main results:
    1. Exact unimodular Smith Normal Form reduction over `Int` for the `n × n`
       derangement/complement matrix `D_n = J_n - I_n` (`derangementEntry i j`),
       which is the exact Nisan bimodal matrix `M_1(e_2^sym)` of the symmetrized
       Witt carry `e_2^sym(x_1..x_n) = ∑_{i ≠ j} x_i x_j`:
       - Explicit closed-form integer matrices `P_n`, `P_n_inv`, `Q_n`, `Q_n_inv`
       - Proven two-sided unimodular inverses for all `n ≥ 2`:
           `P_n * P_n_inv = I_n`, `P_n_inv * P_n = I_n`,
           `Q_n * Q_n_inv = I_n`, `Q_n_inv * Q_n = I_n`
       - Universal Smith Normal Form theorem (`snf_derangement_forall_n`):
           `∀ n ≥ 2, P_n * D_n * Q_n = diag(1, ..., 1, n - 1)`
    2. Exact 2-adic Witt depth visibility threshold (`witt_depth_visibility_threshold`):
       - For `n = 2^r + 1`, the top invariant factor `n - 1 = 2^r` satisfies:
           * `∀ j ≤ r, (n - 1) % 2^j = 0` (vanishes identically in `W_j(F_2) ≅ Z/2^j Z`)
           * `(n - 1) % 2^(r + 1) = 2^r ≠ 0` (emerges first as `2^r`-torsion in `W_{r+1}(F_2)`)
    3. Combined universal theorem (`witt_snf_torsion_emergence`) connecting the
       unimodular SNF reduction to the exact Witt ring depth threshold `k = r + 1`.
-/

namespace WittSnfUniversalTorsion

/-! ## 1. Finite Integer Sums (`sumRange`) and Matrix Algebra -/

/-- Sum of `f 0 + f 1 + ... + f (m - 1)` over `Int`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | m + 1, f => sumRange m f + f m

theorem sumRange_zero (f : Nat → Int) : sumRange 0 f = 0 := rfl

theorem sumRange_succ (m : Nat) (f : Nat → Int) :
    sumRange (m + 1) f = sumRange m f + f m := rfl

theorem sumRange_split_last (n : Nat) (hn : 1 ≤ n) (f : Nat → Int) :
    sumRange n f = sumRange (n - 1) f + f (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    simp [sumRange_succ]

theorem sumRange_congr {m : Nat} {f g : Nat → Int}
    (h : ∀ k, k < m → f k = g k) :
    sumRange m f = sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ]
    rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumRange_const (m : Nat) (c : Int) :
    sumRange m (fun _ => c) = (m : Int) * c := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, ih]
    have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
    rw [hcast, Int.add_mul, Int.one_mul]

theorem sumRange_ite_eq (m a : Nat) (c : Int) :
    sumRange m (fun k => if k = a then c else 0) = if a < m then c else 0 := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, ih]
    by_cases h1 : m = a
    · subst h1
      have hnot : ¬ (m < m) := by omega
      have hlt : m < m + 1 := by omega
      simp [hnot, hlt]
    · by_cases h2 : a < m
      · have hlt : a < m + 1 := by omega
        simp [h1, h2, hlt]
      · have hnot : ¬ (a < m + 1) := by omega
        simp [h1, h2, hnot]

theorem sumRange_ite_eq_symm (m a : Nat) (c : Int) :
    sumRange m (fun k => if a = k then c else 0) = if a < m then c else 0 := by
  rw [← sumRange_ite_eq m a c]
  apply sumRange_congr
  intro k _
  by_cases h : a = k
  · subst h; simp
  · have h' : k ≠ a := fun hk => h hk.symm
    simp [h, h']

theorem sumRange_ite_ne_one (m a : Nat) :
    sumRange m (fun k => if k = a then (0 : Int) else 1) =
      if a < m then (m : Int) - 1 else (m : Int) := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, ih]
    by_cases h1 : m = a
    · subst h1
      have hnot : ¬ (m < m) := by omega
      have hlt : m < m + 1 := by omega
      simp [hnot, hlt]
    · by_cases h2 : a < m
      · have hlt : a < m + 1 := by omega
        simp [h1, h2, hlt]
      · have hnot : ¬ (a < m + 1) := by omega
        simp [h1, h2, hnot]

theorem sumRange_ite_ne_one_symm (m a : Nat) :
    sumRange m (fun k => if a = k then (0 : Int) else 1) =
      if a < m then (m : Int) - 1 else (m : Int) := by
  rw [← sumRange_ite_ne_one m a]
  apply sumRange_congr
  intro k _
  by_cases h : a = k
  · subst h; simp
  · have h' : k ≠ a := fun hk => h hk.symm
    simp [h, h']

/-- Matrix multiplication of `n × n` integer matrices represented as `Nat → Nat → Int`. -/
def matMul (n : Nat) (A B : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange n (fun k => A i k * B k j)

/-- Identity matrix `I_n`. -/
def idMat (i j : Nat) : Int :=
  if i = j then 1 else 0

/-- Derangement / complement matrix `D_n = J_n - I_n` (`0` on diagonal, `1` off-diagonal),
    which is the exact Nisan bimodal matrix `M_1(e_2^sym)`. -/
def derangementEntry (i j : Nat) : Int :=
  if i = j then 0 else 1

/-- Smith Normal Form diagonal matrix `diag(1, 1, ..., 1, n - 1)`. -/
def snfDiag (n i j : Nat) : Int :=
  if i = j then (if i = n - 1 then (n : Int) - 1 else 1) else 0

/-! ## 2. Explicit Unimodular Left and Right Factors `P_n, P_n_inv, Q_n, Q_n_inv` -/

/-- Explicit unimodular left factor `P_n` (`n × n`, `n ≥ 2`):
    - For `i < n - 1`: `-1` at `j = i`, `+1` at `j = n - 1`, `0` elsewhere.
    - For `i = n - 1`: `1` at `j < n - 1`, `2 - n` at `j = n - 1`. -/
def P_mat (n i j : Nat) : Int :=
  if i < n - 1 then
    if i = j then -1 else if j = n - 1 then 1 else 0
  else
    if j = n - 1 then 2 - (n : Int) else 1

/-- Explicit integer inverse `P_n_inv` of `P_n`:
    - For `i < n - 1`: `0` at `j = i`, `1` elsewhere.
    - For `i = n - 1`: `1` everywhere. -/
def P_inv (n i j : Nat) : Int :=
  if i < n - 1 then
    if i = j then 0 else 1
  else
    1

/-- Explicit unimodular right factor `Q_n` (`n × n`, `n ≥ 2`):
    `1` on the diagonal and last column, `0` elsewhere. -/
def Q_mat (n i j : Nat) : Int :=
  if i = j ∨ j = n - 1 then 1 else 0

/-- Explicit integer inverse `Q_n_inv` of `Q_n`:
    `1` on the diagonal, `-1` in the last column above the diagonal, `0` elsewhere. -/
def Q_inv (n i j : Nat) : Int :=
  if i = j then 1 else if j = n - 1 then -1 else 0

/-! ## 3. Universal Two-Sided Unimodularity Proofs (`∀ n ≥ 2`) -/

/-- Left-right inverse: `P_n * P_n_inv = I_n` for all `n ≥ 2`. -/
theorem P_mul_P_inv (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (P_mat n) (P_inv n) i j = idMat i j := by
  unfold matMul idMat
  rw [sumRange_split_last n (by omega)]
  by_cases hil : i < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => P_mat n i k * P_inv n k j) =
          sumRange (n - 1) (fun k => if i = k then -(P_inv n i j) else 0) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp only [P_mat, hil, hkne, ↓reduceIte]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    rw [hsum, sumRange_ite_eq_symm]
    have hlast : P_mat n i (n - 1) * P_inv n (n - 1) j = 1 := by
      have hine : i ≠ n - 1 := by omega
      have hnotlt : ¬ (n - 1 < n - 1) := by omega
      simp [P_mat, P_inv, hil, hine, hnotlt]
    rw [hlast]
    simp only [hil, ↓reduceIte, P_inv]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  · have hieq : i = n - 1 := by omega
    have hsum :
        sumRange (n - 1) (fun k => P_mat n i k * P_inv n k j) =
          sumRange (n - 1) (fun k => if k = j then (0 : Int) else 1) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp [P_mat, P_inv, hil, hk, hkne]
    rw [hsum, sumRange_ite_ne_one]
    have hlast : P_mat n i (n - 1) * P_inv n (n - 1) j = 2 - (n : Int) := by
      have hnotlt : ¬ (n - 1 < n - 1) := by omega
      simp [P_mat, P_inv, hil, hnotlt]
    rw [hlast]
    by_cases hjl : j < n - 1
    · have hij : i ≠ j := by omega
      simp [hjl, hij]
      omega
    · have hij : i = j := by omega
      simp [hjl, hij]
      omega

/-- Right-left inverse: `P_n_inv * P_n = I_n` for all `n ≥ 2`. -/
theorem P_inv_mul_P (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (P_inv n) (P_mat n) i j = idMat i j := by
  unfold matMul idMat
  rw [sumRange_split_last n (by omega)]
  by_cases hjl : j < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => P_inv n i k * P_mat n k j) =
          sumRange (n - 1) (fun k => if k = j then -(P_inv n i j) else 0) := by
      apply sumRange_congr
      intro k hk
      have hjne : j ≠ n - 1 := by omega
      simp only [P_mat, hk, hjne, ↓reduceIte]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]
    rw [hsum, sumRange_ite_eq]
    have hlast : P_inv n i (n - 1) * P_mat n (n - 1) j = 1 := by
      have hnotlt : ¬ (n - 1 < n - 1) := by omega
      have hjne : j ≠ n - 1 := by omega
      by_cases hil : i < n - 1
      · have hine : i ≠ n - 1 := by omega
        simp [P_inv, P_mat, hil, hine, hnotlt, hjne]
      · simp [P_inv, P_mat, hil, hnotlt, hjne]
    rw [hlast]
    simp only [hjl, ↓reduceIte, P_inv]
    by_cases hil : i < n - 1
    · by_cases hij : i = j
      · simp [hij, hjl]
      · simp [hil, hij]
    · have hij : i ≠ j := by omega
      simp [hil, hij]
  · have hjeq : j = n - 1 := by omega
    by_cases hil : i < n - 1
    · have hsum :
          sumRange (n - 1) (fun k => P_inv n i k * P_mat n k j) =
            sumRange (n - 1) (fun k => if i = k then (0 : Int) else 1) := by
        apply sumRange_congr
        intro k hk
        have hkne : k ≠ n - 1 := by omega
        simp [P_inv, P_mat, hil, hk, hkne, hjeq]
      rw [hsum, sumRange_ite_ne_one_symm]
      have hlast : P_inv n i (n - 1) * P_mat n (n - 1) j = 2 - (n : Int) := by
        have hine : i ≠ n - 1 := by omega
        have hnotlt : ¬ (n - 1 < n - 1) := by omega
        simp [P_inv, P_mat, hil, hine, hnotlt, hjeq]
      rw [hlast]
      have hij : i ≠ j := by omega
      simp [hil, hij]
      omega
    · have hsum :
          sumRange (n - 1) (fun k => P_inv n i k * P_mat n k j) =
            sumRange (n - 1) (fun _ => (1 : Int)) := by
        apply sumRange_congr
        intro k hk
        have hkne : k ≠ n - 1 := by omega
        simp [P_inv, P_mat, hil, hk, hkne, hjeq]
      rw [hsum, sumRange_const]
      have hlast : P_inv n i (n - 1) * P_mat n (n - 1) j = 2 - (n : Int) := by
        have hnotlt : ¬ (n - 1 < n - 1) := by omega
        simp [P_inv, P_mat, hil, hnotlt, hjeq]
      rw [hlast]
      have hij : i = j := by omega
      simp [hij]
      omega

/-- Left-right inverse: `Q_n * Q_n_inv = I_n` for all `n ≥ 2`. -/
theorem Q_mul_Q_inv (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (Q_mat n) (Q_inv n) i j = idMat i j := by
  unfold matMul idMat
  rw [sumRange_split_last n (by omega)]
  by_cases hil : i < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => Q_mat n i k * Q_inv n k j) =
          sumRange (n - 1) (fun k => if i = k then Q_inv n i j else 0) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      by_cases hik : i = k
      · subst hik; simp [Q_mat]
      · simp [Q_mat, hik, hkne]
    rw [hsum, sumRange_ite_eq_symm]
    have hlast : Q_mat n i (n - 1) * Q_inv n (n - 1) j =
        if j = n - 1 then 1 else 0 := by
      by_cases hjeq : j = n - 1
      · subst hjeq; simp [Q_mat, Q_inv]
      · have hne : n - 1 ≠ j := fun h => hjeq h.symm
        simp [Q_mat, Q_inv, hjeq, hne]
    rw [hlast]
    simp only [hil, ↓reduceIte, Q_inv]
    by_cases hij : i = j
    · have hjne : j ≠ n - 1 := by omega
      simp [hij, hjne]
    · by_cases hjeq : j = n - 1
      · have hine : i ≠ n - 1 := by omega
        simp [hjeq, hine]
      · simp [hij, hjeq]
  · have hieq : i = n - 1 := by omega
    have hsum :
        sumRange (n - 1) (fun k => Q_mat n i k * Q_inv n k j) =
          sumRange (n - 1) (fun _ => (0 : Int)) := by
      apply sumRange_congr
      intro k hk
      have hik : i ≠ k := by omega
      have hkne : k ≠ n - 1 := by omega
      simp [Q_mat, hik, hkne]
    rw [hsum, sumRange_const]
    by_cases hjeq : j = n - 1
    · simp [Q_mat, Q_inv, hieq, hjeq]
    · have hne : n - 1 ≠ j := fun h => hjeq h.symm
      simp [Q_mat, Q_inv, hieq, hjeq, hne]

/-- Right-left inverse: `Q_n_inv * Q_n = I_n` for all `n ≥ 2`. -/
theorem Q_inv_mul_Q (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (Q_inv n) (Q_mat n) i j = idMat i j := by
  unfold matMul idMat
  rw [sumRange_split_last n (by omega)]
  by_cases hil : i < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => Q_inv n i k * Q_mat n k j) =
          sumRange (n - 1) (fun k => if i = k then Q_mat n i j else 0) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      by_cases hik : i = k
      · subst hik; simp [Q_inv]
      · simp [Q_inv, hik, hkne]
    rw [hsum, sumRange_ite_eq_symm]
    have hlast : Q_inv n i (n - 1) * Q_mat n (n - 1) j =
        if j = n - 1 then -1 else 0 := by
      have hine : i ≠ n - 1 := by omega
      by_cases hjeq : j = n - 1
      · subst hjeq; simp [Q_inv, Q_mat, hine]
      · have hne : n - 1 ≠ j := fun h => hjeq h.symm
        simp [Q_inv, Q_mat, hine, hjeq, hne]
    rw [hlast]
    simp only [hil, ↓reduceIte, Q_mat]
    by_cases hij : i = j
    · have hjne : j ≠ n - 1 := by omega
      simp [hij, hjne]
    · by_cases hjeq : j = n - 1
      · have hine : i ≠ n - 1 := by omega
        simp [hjeq, hine]
      · simp [hij, hjeq]
  · have hieq : i = n - 1 := by omega
    have hsum :
        sumRange (n - 1) (fun k => Q_inv n i k * Q_mat n k j) =
          sumRange (n - 1) (fun _ => (0 : Int)) := by
      apply sumRange_congr
      intro k hk
      have hik : i ≠ k := by omega
      have hkne : k ≠ n - 1 := by omega
      simp [Q_inv, hik, hkne]
    rw [hsum, sumRange_const]
    by_cases hjeq : j = n - 1
    · simp [Q_inv, Q_mat, hieq, hjeq]
    · have hne : n - 1 ≠ j := fun h => hjeq h.symm
      simp [Q_inv, Q_mat, hieq, hjeq, hne]

/-! ## 4. Universal Smith Normal Form Reduction `P_n * D_n * Q_n = diag(1, ..., 1, n - 1)` -/

/-- Closed-form intermediate product `P_n * D_n`. -/
def PD_mat (n i j : Nat) : Int :=
  if i < n - 1 then
    if i = j then 1 else if j = n - 1 then -1 else 0
  else
    if j = n - 1 then (n : Int) - 1 else 0

theorem P_mul_D (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (P_mat n) derangementEntry i j = PD_mat n i j := by
  unfold matMul PD_mat
  rw [sumRange_split_last n (by omega)]
  by_cases hil : i < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => P_mat n i k * derangementEntry k j) =
          sumRange (n - 1) (fun k => if i = k then -(derangementEntry i j) else 0) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp only [P_mat, hil, hkne, ↓reduceIte]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    rw [hsum, sumRange_ite_eq_symm]
    have hlast : P_mat n i (n - 1) * derangementEntry (n - 1) j =
        derangementEntry (n - 1) j := by
      have hine : i ≠ n - 1 := by omega
      simp [P_mat, hil, hine]
    rw [hlast]
    simp only [hil, ↓reduceIte, derangementEntry]
    by_cases hij : i = j
    · have hne : n - 1 ≠ j := by omega
      simp [hij, hne]
    · by_cases hjeq : j = n - 1
      · subst hjeq; simp [hij]
      · have hne : n - 1 ≠ j := fun h => hjeq h.symm
        simp [hij, hjeq, hne]
  · have hsum :
        sumRange (n - 1) (fun k => P_mat n i k * derangementEntry k j) =
          sumRange (n - 1) (fun k => if k = j then (0 : Int) else 1) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp [P_mat, derangementEntry, hil, hkne]
    rw [hsum, sumRange_ite_ne_one]
    have hlast : P_mat n i (n - 1) * derangementEntry (n - 1) j =
        (2 - (n : Int)) * derangementEntry (n - 1) j := by
      simp [P_mat, hil]
    rw [hlast]
    simp only [hil, ↓reduceIte, derangementEntry]
    by_cases hjeq : j = n - 1
    · have hnotlt : ¬ (j < n - 1) := by omega
      subst hjeq
      simp [hnotlt]
      omega
    · have hjl : j < n - 1 := by omega
      have hne : n - 1 ≠ j := fun h => hjeq h.symm
      simp [hjl, hjeq, hne]
      omega

/-- Universal Smith Normal Form theorem for `D_n = J_n - I_n` (`M_1(e_2^sym)`):
    For every `n ≥ 2`, `P_n * D_n * Q_n = diag(1, ..., 1, n - 1)` where `P_n, Q_n`
    are unimodular over `Int` (with explicit two-sided inverses `P_inv, Q_inv`). -/
theorem snf_derangement_forall_n (n : Nat) (hn : 2 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (matMul n (P_mat n) derangementEntry) (Q_mat n) i j = snfDiag n i j := by
  have hPD :
      matMul n (matMul n (P_mat n) derangementEntry) (Q_mat n) i j =
        matMul n (PD_mat n) (Q_mat n) i j := by
    change sumRange n (fun k => matMul n (P_mat n) derangementEntry i k * Q_mat n k j) =
      sumRange n (fun k => PD_mat n i k * Q_mat n k j)
    apply sumRange_congr
    intro k hk
    rw [P_mul_D n hn i k hi hk]
  rw [hPD]
  unfold matMul snfDiag
  rw [sumRange_split_last n (by omega)]
  by_cases hil : i < n - 1
  · have hsum :
        sumRange (n - 1) (fun k => PD_mat n i k * Q_mat n k j) =
          sumRange (n - 1) (fun k => if i = k then Q_mat n i j else 0) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp only [PD_mat, hil, hkne, ↓reduceIte]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    rw [hsum, sumRange_ite_eq_symm]
    have hlast : PD_mat n i (n - 1) * Q_mat n (n - 1) j =
        if j = n - 1 then -1 else 0 := by
      have hine : i ≠ n - 1 := by omega
      by_cases hjeq : j = n - 1
      · subst hjeq; simp [PD_mat, Q_mat, hil, hine]
      · have hne : n - 1 ≠ j := fun h => hjeq h.symm
        simp [PD_mat, Q_mat, hil, hine, hjeq, hne]
    rw [hlast]
    have hine : i ≠ n - 1 := by omega
    simp only [hil, hine, ↓reduceIte, Q_mat]
    by_cases hij : i = j
    · have hjne : j ≠ n - 1 := by omega
      simp [hij, hjne]
    · by_cases hjeq : j = n - 1
      · simp [hjeq, hine]
      · simp [hij, hjeq]
  · have hieq : i = n - 1 := by omega
    have hsum :
        sumRange (n - 1) (fun k => PD_mat n i k * Q_mat n k j) =
          sumRange (n - 1) (fun _ => (0 : Int)) := by
      apply sumRange_congr
      intro k hk
      have hkne : k ≠ n - 1 := by omega
      simp [PD_mat, hil, hkne]
    rw [hsum, sumRange_const]
    by_cases hjeq : j = n - 1
    · simp [PD_mat, Q_mat, hieq, hjeq]
    · have hne : n - 1 ≠ j := fun h => hjeq h.symm
      simp [PD_mat, Q_mat, hieq, hjeq, hne]

/-! ## 5. Exact 2-Adic Witt Depth Visibility Threshold (`n = 2^r + 1`) -/

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem pow2_dvd_pow2 {j r : Nat} (hjr : j ≤ r) : 2 ^ j ∣ 2 ^ r := by
  refine ⟨2 ^ (r - j), ?_⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le hjr]

/-- Exact 2-adic Witt depth visibility threshold:
    At `n = 2^r + 1`, the top SNF invariant factor `n - 1 = 2^r` vanishes identically
    modulo `2^j` for all shallower Witt depths `j ≤ r` (`W_j(F_2) ≅ Z/2^j Z`),
    and emerges first as strictly nonzero `2^r`-torsion at Witt depth `k = r + 1`
    (`W_{r+1}(F_2) ≅ Z/2^{r+1} Z`). -/
theorem witt_depth_visibility_threshold (r : Nat) :
    let n := 2 ^ r + 1
    2 ≤ n ∧
    (∀ j : Nat, j ≤ r → (n - 1) % (2 ^ j) = 0) ∧
    (n - 1) % (2 ^ (r + 1)) = 2 ^ r ∧
    (n - 1) % (2 ^ (r + 1)) ≠ 0 := by
  dsimp only
  have hpos : 0 < 2 ^ r := pow2_pos r
  have hsub : 2 ^ r + 1 - 1 = 2 ^ r := by omega
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hjr
    rw [hsub]
    exact Nat.mod_eq_zero_of_dvd (pow2_dvd_pow2 hjr)
  · rw [hsub]
    have hlt : 2 ^ r < 2 ^ (r + 1) := by
      rw [Nat.pow_succ]
      omega
    exact Nat.mod_eq_of_lt hlt
  · rw [hsub]
    have hlt : 2 ^ r < 2 ^ (r + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- Combined universal Witt torsion emergence theorem:
    For every `r : Nat` and `n = 2^r + 1`, `P_n * D_n * Q_n = diag(1, ..., 1, 2^r)`
    with unimodular `P_n, Q_n`, whose top invariant factor `(n - 1 : Int) = (2^r : Int)`
    vanishes mod `2^j` for all `j ≤ r` and is strictly nonzero mod `2^(r+1)`. -/
theorem witt_snf_torsion_emergence (r : Nat) :
    let n := 2 ^ r + 1
    (∀ i j, i < n → j < n →
      matMul n (matMul n (P_mat n) derangementEntry) (Q_mat n) i j = snfDiag n i j) ∧
    snfDiag n (n - 1) (n - 1) = (2 ^ r : Int) ∧
    (∀ j : Nat, j ≤ r → (n - 1) % (2 ^ j) = 0) ∧
    (n - 1) % (2 ^ (r + 1)) = 2 ^ r ∧
    (n - 1) % (2 ^ (r + 1)) ≠ 0 := by
  dsimp only
  have hvis := witt_depth_visibility_threshold r
  rcases hvis with ⟨hn, hvanish, hmod, hne⟩
  refine ⟨fun i j hi hj => snf_derangement_forall_n (2 ^ r + 1) hn i j hi hj, ?_, hvanish, hmod, hne⟩
  unfold snfDiag
  simp

/-! ## 6. Axiom Audit -/

#print axioms P_mul_P_inv
#print axioms P_inv_mul_P
#print axioms Q_mul_Q_inv
#print axioms Q_inv_mul_Q
#print axioms snf_derangement_forall_n
#print axioms witt_depth_visibility_threshold
#print axioms witt_snf_torsion_emergence

end WittSnfUniversalTorsion
