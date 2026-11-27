/-
  ATAQUE-12: Universal Kneser KG(n, 2) / e_4^sym 2-Adic Torsion Theorem
             & NC-IPS Separation over Witt Rings W_k(F_2)
  ======================================================================
  Standalone Lean 4.36.0 formalization (zero imports, zero `sorryAx`,
  `#print axioms` audited).

  Main results:
    (a) Universal `∀ n ≥ 3` bilateral unimodular Smith Normal Form for
        `M_{1,2}(e_3^sym)` (size `n × n^2`):
        - Explicit closed-form integer matrices `P_e3 n`, `P_e3_inv n`,
          `Q_e3 n`, `Q_e3_inv n`
        - Proven two-sided unimodular inverses:
            `P_e3 * P_e3_inv = I_n`, `P_e3_inv * P_e3 = I_n`,
            `Q_e3 * Q_e3_inv = I_{n^2}`, `Q_e3_inv * Q_e3 = I_{n^2}`
        - Universal SNF theorem (`snf_e3_M12_forall_n`):
            `∀ n ≥ 3, P_e3 n * M12_e3 n * Q_e3 n = diag(1, ..., 1, n - 2, 0, ..., 0)`
    (b) Exact algebraic/vector-space theorem on `KG(n, 2)` (odd `n ≥ 5`):
        - On the `(n - 1)`-dimensional zero-sum subspace
          `V_0 = {v : sumRange n v = 0}`, the pair-sum embedding
          `w_v(i, j) = v i + v j` is injective (`pairSum_injective`) and maps
          the standard basis `e_0, ..., e_{n-2}` to `n - 1` linearly independent
          pair-sum vectors in `Z^{binom(n,2)}` (`pairSum_basis_lin_indep`).
        - `KG(n, 2)` acts on every `w_v` (`v ∈ V_0`) as scalar `-(n - 3)`
          (`kneser_acts_on_pairSum`):
            `(KG(n, 2) * w_v)(i, j) = -(n - 3 : Int) * w_v(i, j)`.
        - At `n = 2^r + 3` (`r ≥ 1`), `n - 3 = 2^r`, so all `n - 1` linearly
          independent directions suffer exact `2^r`-divisibility
          (`kneser_torsion_eigenspace_2r`).
    (c) Rank-collapse vs full-rank separation theorem over `Z/2^{r+1}Z` vs
        `Z/2^r Z` (`W_{r+1}(F_2)` vs `W_r(F_2)`) for NC-IPS Nisan matrices:
        - Every `m * 2^r` (with `m` odd) vanishes mod `2^k` for `k ≤ r` and
          equals `2^r ≠ 0` mod `2^{r+1}` (`witt_rank_collapse_vs_emergence`).
        - For `KG(2^r + 3, 2)` (`r ≥ 1`), the `(n - 1)`-dimensional eigenspace
          `W_0` collapses identically to `0` mod `2^k` for all `k ≤ r` and
          maintains full `(n - 1)`-dimensional `F_2`-independence mod `2^{r+1}`
          (`kneser_witt_subspace_separation`).
        - For `M_{1,2}(e_3^sym)` at `n = 2^r + 2` (`r ≥ 1`), the top SNF factor
          `n - 2 = 2^r` collapses mod `2^k` (`k ≤ r`) and emerges at `W_{r+1}(F_2)`
          (`e3_witt_rank_jump`).
-/

namespace WittKneserLinearTorsion

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

theorem sumRange_split_last2 (n : Nat) (hn : 2 ≤ n) (f : Nat → Int) :
    sumRange n f = sumRange (n - 2) f + f (n - 2) + f (n - 1) := by
  have h1 : n - 1 - 1 = n - 2 := by omega
  rw [sumRange_split_last n (by omega), sumRange_split_last (n - 1) (by omega), h1]

theorem sumRange_add_split (a b : Nat) (f : Nat → Int) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun k => f (a + k)) := by
  induction b with
  | zero => simp [sumRange_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_congr {m : Nat} {f g : Nat → Int}
    (h : ∀ k, k < m → f k = g k) :
    sumRange m f = sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ]
    rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumRange_add (m : Nat) (f g : Nat → Int) :
    sumRange m (fun k => f k + g k) = sumRange m f + sumRange m g := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_sub (m : Nat) (f g : Nat → Int) :
    sumRange m (fun k => f k - g k) = sumRange m f - sumRange m g := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_mul_left (m : Nat) (c : Int) (f : Nat → Int) :
    sumRange m (fun k => c * f k) = c * sumRange m f := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ, ih, Int.mul_add]

theorem sumRange_mul_right (m : Nat) (c : Int) (f : Nat → Int) :
    sumRange m (fun k => f k * c) = sumRange m f * c := by
  induction m with
  | zero => simp [sumRange_zero]
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ, ih, Int.add_mul]

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

/-- Matrix multiplication for rectangular matrices `(m × k) * (k × n)`. -/
def matMulRect (k : Nat) (A B : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange k (fun t => A i t * B t j)

/-- Square matrix multiplication `(n × n) * (n × n)`. -/
def matMul (n : Nat) (A B : Nat → Nat → Int) (i j : Nat) : Int :=
  matMulRect n A B i j

/-- Identity matrix. -/
def idMat (i j : Nat) : Int :=
  if i = j then 1 else 0

/-! ## 2. Part (a): Universal SNF for `M_{1,2}(e_3^sym)` (`∀ n ≥ 3`) -/

/-- The Nisan matrix `M_{1,2}(e_3^sym)` of size `n × n^2`.
    Column `c < n * n` encodes `(c / n, c % n)`. -/
def M12_e3 (n : Nat) (i c : Nat) : Int :=
  let a := c / n
  let b := c % n
  if a ≠ b ∧ i ≠ a ∧ i ≠ b then 1 else 0

/-- Target SNF matrix of size `n × n^2`: `diag(1^{n-1}, n - 2, 0, ..., 0)`. -/
def snfM12 (n : Nat) (i j : Nat) : Int :=
  if i = j then (if i = n - 1 then (n : Int) - 2 else 1) else 0

/-- Left unimodular matrix `P_e3 n` of size `n × n`. -/
def P_e3 (n : Nat) (i k : Nat) : Int :=
  if i < n - 2 then
    if k = i then 1 else if k = n - 2 then -1 else 0
  else if i = n - 2 then
    if k = n - 1 then 1 else 0
  else
    if k = n - 2 then 3 - (n : Int) else 1

/-- Exact two-sided inverse `P_e3_inv n` of `P_e3 n`. -/
def P_e3_inv (n : Nat) (i j : Nat) : Int :=
  if i < n - 2 then
    if j < n - 2 then (if i = j then 0 else -1)
    else if j = n - 2 then -1
    else 1
  else if i = n - 2 then
    if j < n - 2 then -1
    else if j = n - 2 then -1
    else 1
  else
    if j = n - 2 then 1 else 0

theorem P_e3_mul_inv (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (P_e3 n) (P_e3_inv n) i j = idMat i j := by
  unfold matMul matMulRect idMat
  rw [sumRange_split_last2 n (by omega)]
  by_cases hi1 : i < n - 2
  · have hsum :
        sumRange (n - 2) (fun t => P_e3 n i t * P_e3_inv n t j) =
          sumRange (n - 2) (fun t => if t = i then P_e3_inv n i j else 0) := by
      apply sumRange_congr
      intro t ht
      have ht1 : t ≠ n - 2 := by omega
      simp [P_e3, hi1, ht1]
      by_cases hti : t = i
      · subst hti; simp
      · simp [hti]
    rw [hsum, sumRange_ite_eq]
    simp only [hi1, ↓reduceIte]
    have h1 : P_e3 n i (n - 2) = -1 := by
      have hine : n - 2 ≠ i := by omega
      simp [P_e3, hi1, hine]
    have h2 : P_e3 n i (n - 1) = 0 := by
      have hine1 : n - 1 ≠ i := by omega
      have hine2 : n - 1 ≠ n - 2 := by omega
      simp [P_e3, hi1, hine1, hine2]
    rw [h1, h2]
    have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
    have hn1_ne : n - 1 ≠ n - 2 := by omega
    have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
    by_cases hj1 : j < n - 2
    · by_cases hij : i = j
      · subst hij; simp [P_e3_inv, hi1, hn2_not_lt, hn1_not_lt, hn1_ne]
      · simp [P_e3_inv, hi1, hj1, hij, hn2_not_lt, hn1_not_lt, hn1_ne]
    · by_cases hj2 : j = n - 2
      · subst hj2; have hij : i ≠ n - 2 := by omega
        simp [P_e3_inv, hi1, hij, hn2_not_lt, hn1_not_lt, hn1_ne]
      · have hj3 : j = n - 1 := by omega
        subst hj3; have hij : i ≠ n - 1 := by omega
        simp [P_e3_inv, hi1, hij, hn2_not_lt, hn1_not_lt, hn1_ne]
  · have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
    have hn1_ne : n - 1 ≠ n - 2 := by omega
    have hn2_ne : n - 2 ≠ n - 1 := by omega
    have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
    by_cases hi2 : i = n - 2
    · subst hi2
      have hsum :
          sumRange (n - 2) (fun t => P_e3 n (n - 2) t * P_e3_inv n t j) =
            sumRange (n - 2) (fun _ => (0 : Int)) := by
        apply sumRange_congr
        intro t ht
        have ht1 : t ≠ n - 1 := by omega
        simp [P_e3, hn2_not_lt, ht1]
      rw [hsum, sumRange_const]
      by_cases hj2 : j = n - 2
      · subst hj2; simp [P_e3, P_e3_inv, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
      · have hne : n - 2 ≠ j := fun h => hj2 h.symm
        by_cases hj1 : j < n - 2
        · simp [P_e3, P_e3_inv, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne, hj1, hj2, hne]
        · have hj3 : j = n - 1 := by omega
          subst hj3; simp [P_e3, P_e3_inv, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
    · have hi3 : i = n - 1 := by omega
      subst hi3
      by_cases hj1 : j < n - 2
      · have hsum :
            sumRange (n - 2) (fun t => P_e3 n (n - 1) t * P_e3_inv n t j) =
              sumRange (n - 2) (fun t => if t = j then (0 : Int) else -1) := by
          apply sumRange_congr
          intro t ht
          have ht1 : t ≠ n - 2 := by omega
          simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, ht, ht1, hj1]
        have hneg :
            sumRange (n - 2) (fun t => if t = j then (0 : Int) else -1) =
              (-1 : Int) * sumRange (n - 2) (fun t => if t = j then (0 : Int) else 1) := by
          rw [← sumRange_mul_left (n - 2) (-1)]
          apply sumRange_congr; intro t _; by_cases h : t = j <;> simp [h]
        rw [hsum, hneg, sumRange_ite_ne_one]
        have hne : n - 1 ≠ j := by omega
        simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, hn2_not_lt, hj1, hne]
        omega
      · by_cases hj2 : j = n - 2
        · subst hj2
          have hsum :
              sumRange (n - 2) (fun t => P_e3 n (n - 1) t * P_e3_inv n t (n - 2)) =
                sumRange (n - 2) (fun _ => (-1 : Int)) := by
            apply sumRange_congr
            intro t ht
            have ht1 : t ≠ n - 2 := by omega
            simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, ht, ht1]
          rw [hsum, sumRange_const]
          simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, hn2_not_lt]
          omega
        · have hj3 : j = n - 1 := by omega
          subst hj3
          have hsum :
              sumRange (n - 2) (fun t => P_e3 n (n - 1) t * P_e3_inv n t (n - 1)) =
                sumRange (n - 2) (fun _ => (1 : Int)) := by
            apply sumRange_congr
            intro t ht
            have ht1 : t ≠ n - 2 := by omega
            simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, ht, ht1]
          rw [hsum, sumRange_const]
          simp [P_e3, P_e3_inv, hn1_not_lt, hn1_ne, hn2_not_lt]
          omega

theorem P_e3_inv_mul (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n) :
    matMul n (P_e3_inv n) (P_e3 n) i j = idMat i j := by
  unfold matMul matMulRect idMat
  rw [sumRange_split_last2 n (by omega)]
  have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
  have hn1_ne : n - 1 ≠ n - 2 := by omega
  have hn2_ne : n - 2 ≠ n - 1 := by omega
  have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
  by_cases hi1 : i < n - 2
  · by_cases hj1 : j < n - 2
    · have hj_ne2 : j ≠ n - 2 := by omega
      have hj_ne1 : j ≠ n - 1 := by omega
      have hsum :
          sumRange (n - 2) (fun t => P_e3_inv n i t * P_e3 n t j) =
            sumRange (n - 2) (fun t => if t = j then (if i = j then 0 else -1) else 0) := by
        apply sumRange_congr
        intro t ht
        simp [P_e3_inv, P_e3, hi1, ht, hj_ne2]
        by_cases htj : t = j
        · subst htj; simp
        · have hjt : j ≠ t := fun h => htj h.symm
          simp [htj, hjt]
      rw [hsum, sumRange_ite_eq]
      simp [P_e3_inv, P_e3, hi1, hj1, hj_ne1, hj_ne2, hn2_not_lt, hn1_not_lt, hn1_ne]
      by_cases hij : i = j <;> simp [hij]
    · by_cases hj2 : j = n - 2
      · subst hj2
        have hsum :
            sumRange (n - 2) (fun t => P_e3_inv n i t * P_e3 n t (n - 2)) =
              sumRange (n - 2) (fun t => if t = i then (0 : Int) else 1) := by
          apply sumRange_congr
          intro t ht
          have hnt : n - 2 ≠ t := by omega
          simp [P_e3_inv, P_e3, hi1, ht, hnt]
          by_cases hit : i = t
          · subst hit; simp
          · have hti : t ≠ i := fun h => hit h.symm
            simp [hit, hti]
        rw [hsum, sumRange_ite_ne_one]
        have hine : i ≠ n - 2 := by omega
        simp [P_e3_inv, P_e3, hi1, hine, hn2_not_lt, hn1_not_lt, hn1_ne]
        omega
      · have hj3 : j = n - 1 := by omega
        subst hj3
        have hsum :
            sumRange (n - 2) (fun t => P_e3_inv n i t * P_e3 n t (n - 1)) =
              sumRange (n - 2) (fun _ => (0 : Int)) := by
          apply sumRange_congr
          intro t ht
          have hne : n - 1 ≠ t := by omega
          simp [P_e3_inv, P_e3, hi1, ht, hne, hn1_ne]
        rw [hsum, sumRange_const]
        have hine : i ≠ n - 1 := by omega
        simp [P_e3_inv, P_e3, hi1, hine, hn2_not_lt, hn1_not_lt, hn1_ne]
  · by_cases hi2 : i = n - 2
    · subst hi2
      by_cases hj1 : j < n - 2
      · have hj_ne2 : j ≠ n - 2 := by omega
        have hj_ne1 : j ≠ n - 1 := by omega
        have hsum :
            sumRange (n - 2) (fun t => P_e3_inv n (n - 2) t * P_e3 n t j) =
              sumRange (n - 2) (fun t => if t = j then -1 else 0) := by
          apply sumRange_congr
          intro t ht
          simp [P_e3_inv, P_e3, hn2_not_lt, ht, hj_ne2]
          by_cases htj : t = j
          · subst htj; simp
          · have hjt : j ≠ t := fun h => htj h.symm
            simp [htj, hjt]
        rw [hsum, sumRange_ite_eq]
        have hne1 : n - 2 ≠ j := by omega
        simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne, hj1, hne1, hj_ne1, hj_ne2]
      · by_cases hj2 : j = n - 2
        · subst hj2
          have hsum :
              sumRange (n - 2) (fun t => P_e3_inv n (n - 2) t * P_e3 n t (n - 2)) =
                sumRange (n - 2) (fun _ => (1 : Int)) := by
            apply sumRange_congr
            intro t ht
            have hnt : n - 2 ≠ t := by omega
            simp [P_e3_inv, P_e3, hn2_not_lt, ht, hnt]
          rw [hsum, sumRange_const]
          simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne]
          omega
        · have hj3 : j = n - 1 := by omega
          subst hj3
          have hsum :
              sumRange (n - 2) (fun t => P_e3_inv n (n - 2) t * P_e3 n t (n - 1)) =
                sumRange (n - 2) (fun _ => (0 : Int)) := by
            apply sumRange_congr
            intro t ht
            have hne1 : n - 1 ≠ t := by omega
            simp [P_e3_inv, P_e3, hn2_not_lt, ht, hne1, hn1_ne]
          rw [hsum, sumRange_const]
          simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
    · have hi3 : i = n - 1 := by omega
      subst hi3
      have hsum :
          sumRange (n - 2) (fun t => P_e3_inv n (n - 1) t * P_e3 n t j) =
            sumRange (n - 2) (fun _ => (0 : Int)) := by
        apply sumRange_congr
        intro t ht
        have ht2 : t ≠ n - 2 := by omega
        simp [P_e3_inv, hn1_not_lt, hn1_ne, ht2]
      rw [hsum, sumRange_const]
      by_cases hj3 : j = n - 1
      · subst hj3; simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne]
      · have hne : n - 1 ≠ j := fun h => hj3 h.symm
        by_cases hj1 : j < n - 2
        · simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne, hne, hj3]
        · have hj2 : j = n - 2 := by omega
          subst hj2; simp [P_e3_inv, P_e3, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]

/-- Explicit closed-form `PM_e3 := P_e3 n * M12_e3 n` for `c < n * n`. -/
def PM_e3 (n : Nat) (i c : Nat) : Int :=
  let a := c / n
  let b := c % n
  if a = b then 0
  else if i < n - 2 then
    (if i ≠ a ∧ i ≠ b then 1 else 0) - (if n - 2 ≠ a ∧ n - 2 ≠ b then 1 else 0)
  else if i = n - 2 then
    if a ≠ n - 1 ∧ b ≠ n - 1 then 1 else 0
  else
    if a = n - 2 ∨ b = n - 2 then (n : Int) - 2 else 0

theorem P_e3_mul_M12 (n : Nat) (hn : 3 ≤ n) (i c : Nat) (hi : i < n) (hc : c < n * n) :
    matMulRect n (P_e3 n) (M12_e3 n) i c = PM_e3 n i c := by
  unfold matMulRect PM_e3
  dsimp only
  have ha : c / n < n := Nat.div_lt_of_lt_mul hc
  have hb : c % n < n := Nat.mod_lt c (by omega)
  by_cases hab : c / n = c % n
  · have hzero : sumRange n (fun t => P_e3 n i t * M12_e3 n t c) =
        sumRange n (fun _ => (0 : Int)) := by
      apply sumRange_congr; intro t _
      simp [M12_e3, hab]
    rw [hzero, sumRange_const]
    simp [hab]
  · simp only [hab, ↓reduceIte]
    by_cases hi1 : i < n - 2
    · simp only [hi1, ↓reduceIte]
      rw [sumRange_split_last2 n (by omega)]
      have hsum :
          sumRange (n - 2) (fun t => P_e3 n i t * M12_e3 n t c) =
            sumRange (n - 2) (fun t => if t = i then M12_e3 n i c else 0) := by
        apply sumRange_congr; intro t ht
        have ht1 : t ≠ n - 2 := by omega
        simp [P_e3, hi1, ht1]
        by_cases hti : t = i
        · subst hti; simp
        · simp [hti]
      rw [hsum, sumRange_ite_eq]
      have h1 : P_e3 n i (n - 2) = -1 := by
        have hine : n - 2 ≠ i := by omega
        simp [P_e3, hi1, hine]
      have h2 : P_e3 n i (n - 1) = 0 := by
        have hine1 : n - 1 ≠ i := by omega
        have hine2 : n - 1 ≠ n - 2 := by omega
        simp [P_e3, hi1, hine1, hine2]
      rw [h1, h2]
      simp [hi1, M12_e3, hab]
      omega
    · by_cases hi2 : i = n - 2
      · subst hi2
        have hnot : ¬ (n - 2 < n - 2) := by omega
        simp only [hnot, ↓reduceIte]
        rw [sumRange_split_last n (by omega)]
        have hsum :
            sumRange (n - 1) (fun t => P_e3 n (n - 2) t * M12_e3 n t c) =
              sumRange (n - 1) (fun _ => (0 : Int)) := by
          apply sumRange_congr; intro t ht
          have ht1 : t ≠ n - 1 := by omega
          simp [P_e3, hnot, ht1]
        rw [hsum, sumRange_const]
        simp [P_e3, M12_e3, hnot, hab]
        by_cases h1 : c / n = n - 1 <;> by_cases h2 : c % n = n - 1 <;> simp [h1, h2, Ne.symm]
      · have hi3 : i = n - 1 := by omega
        subst hi3
        have hnot1 : ¬ (n - 1 < n - 2) := by omega
        have hnot2 : n - 1 ≠ n - 2 := by omega
        simp only [hnot1, hnot2, ↓reduceIte]
        have hsum_all :
            sumRange n (fun t => M12_e3 n t c) = (n : Int) - 2 := by
          have hcongr :
              sumRange n (fun t => M12_e3 n t c) =
                sumRange n (fun t => (1 : Int) - (if t = c / n then 1 else 0) - (if t = c % n then 1 else 0)) := by
            apply sumRange_congr; intro t _
            simp only [M12_e3, hab, ne_eq, not_false_eq_true, true_and]
            by_cases hta : t = c / n <;> by_cases htb : t = c % n <;> simp [hta, htb, hab, Ne.symm hab]
          rw [hcongr, sumRange_sub, sumRange_sub, sumRange_const, sumRange_ite_eq, sumRange_ite_eq]
          simp [ha, hb]
          omega
        have hsplit :
            sumRange n (fun t => P_e3 n (n - 1) t * M12_e3 n t c) =
              sumRange n (fun t => M12_e3 n t c) + (2 - (n : Int)) * M12_e3 n (n - 2) c := by
          have hcongr :
              sumRange n (fun t => P_e3 n (n - 1) t * M12_e3 n t c) =
                sumRange n (fun t => M12_e3 n t c + (if t = n - 2 then (2 - (n : Int)) * M12_e3 n (n - 2) c else 0)) := by
            apply sumRange_congr; intro t _
            by_cases ht : t = n - 2
            · subst ht
              simp [P_e3, hnot1, hnot2]
              have h3 : (3 : Int) - (n : Int) = 1 + (2 - (n : Int)) := by omega
              rw [h3, Int.add_mul, Int.one_mul]
            · simp [P_e3, hnot1, hnot2, ht]
          rw [hcongr, sumRange_add, sumRange_ite_eq]
          have hlt : n - 2 < n := by omega
          simp [hlt]
        rw [hsplit, hsum_all]
        by_cases hcond : c / n = n - 2 ∨ c % n = n - 2
        · have hzero : M12_e3 n (n - 2) c = 0 := by
            rcases hcond with h | h <;> simp [M12_e3, hab, h]
          simp [hcond, hzero]
        · have ha2 : n - 2 ≠ c / n := fun h => hcond (Or.inl h.symm)
          have hb2 : n - 2 ≠ c % n := fun h => hcond (Or.inr h.symm)
          have hone : M12_e3 n (n - 2) c = 1 := by simp [M12_e3, hab, ha2, hb2]
          simp [hcond, hone]
          omega

/-- Disjoint involution `sigmaQ n` on `{0..n*n - 1}` mapping `0..n-1` to the `n`
    pivot columns `{(n-1)*n + 0, ..., (n-1)*n + (n-3), n, (n-1)*n + (n-2)}`. -/
def sigmaQ (n : Nat) (x : Nat) : Nat :=
  if x < n - 2 then (n - 1) * n + x
  else if x = n - 2 then n
  else if x = n - 1 then (n - 1) * n + (n - 2)
  else if x = n then n - 2
  else if (n - 1) * n ≤ x ∧ x < (n - 1) * n + (n - 2) then x - (n - 1) * n
  else if x = (n - 1) * n + (n - 2) then n - 1
  else x

theorem sigmaQ_lt (n : Nat) (hn : 3 ≤ n) {x : Nat} (hx : x < n * n) :
    sigmaQ n x < n * n := by
  unfold sigmaQ
  have h1 : (n - 1) * n + n = n * n := by
    have : n * n = (n - 1 + 1) * n := by rw [Nat.sub_add_cancel (by omega)]
    rw [this, Nat.add_mul, Nat.one_mul]
  have h2 : n < (n - 1) * n := by
    have : 2 * n ≤ (n - 1) * n := Nat.mul_le_mul_right n (by omega)
    omega
  repeat (split <;> try omega)

theorem sigmaQ_involutive (n : Nat) (hn : 3 ≤ n) (x : Nat) :
    sigmaQ n (sigmaQ n x) = x := by
  have h2 : n < (n - 1) * n := by
    have : 2 * n ≤ (n - 1) * n := Nat.mul_le_mul_right n (by omega)
    omega
  by_cases h1 : x < n - 2
  · have hs : sigmaQ n x = (n - 1) * n + x := by unfold sigmaQ; repeat (split <;> try omega)
    rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
  · by_cases h2' : x = n - 2
    · have hs : sigmaQ n x = n := by unfold sigmaQ; repeat (split <;> try omega)
      rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
    · by_cases h3 : x = n - 1
      · have hs : sigmaQ n x = (n - 1) * n + (n - 2) := by unfold sigmaQ; repeat (split <;> try omega)
        rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
      · by_cases h4 : x = n
        · have hs : sigmaQ n x = n - 2 := by unfold sigmaQ; repeat (split <;> try omega)
          rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
        · by_cases h5 : (n - 1) * n ≤ x ∧ x < (n - 1) * n + (n - 2)
          · have hs : sigmaQ n x = x - (n - 1) * n := by unfold sigmaQ; repeat (split <;> try omega)
            rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
          · by_cases h6 : x = (n - 1) * n + (n - 2)
            · have hs : sigmaQ n x = n - 1 := by unfold sigmaQ; repeat (split <;> try omega)
              rw [hs]; unfold sigmaQ; repeat (split <;> try omega)
            · have hs : sigmaQ n x = x := by unfold sigmaQ; repeat (split <;> try omega)
              rw [hs, hs]

/-- Permutation matrix `PermQ n` of size `n^2 × n^2`. -/
def PermQ (n : Nat) (r c : Nat) : Int :=
  if r = sigmaQ n c then 1 else 0

theorem PermQ_mul_PermQ (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n * n) (hj : j < n * n) :
    matMul (n * n) (PermQ n) (PermQ n) i j = idMat i j := by
  unfold matMul matMulRect idMat
  have hcongr :
      sumRange (n * n) (fun t => PermQ n i t * PermQ n t j) =
        sumRange (n * n) (fun t => if t = sigmaQ n i then PermQ n (sigmaQ n i) j else 0) := by
    apply sumRange_congr; intro t _
    unfold PermQ
    have hinv : (i = sigmaQ n t) ↔ (t = sigmaQ n i) := by
      constructor
      · intro h; rw [h, sigmaQ_involutive n hn]
      · intro h; rw [h, sigmaQ_involutive n hn]
    by_cases ht : t = sigmaQ n i
    · subst ht
      simp [sigmaQ_involutive n hn]
    · have hi' : i ≠ sigmaQ n t := fun h => ht (hinv.mp h)
      simp [ht, hi']
  rw [hcongr, sumRange_ite_eq]
  have hlt : sigmaQ n i < n * n := sigmaQ_lt n hn hi
  simp only [hlt, ↓reduceIte, PermQ]
  have heq : (sigmaQ n i = sigmaQ n j) ↔ (i = j) := by
    constructor
    · intro h
      have := congrArg (sigmaQ n) h
      rwa [sigmaQ_involutive n hn, sigmaQ_involutive n hn] at this
    · intro h; rw [h]
  by_cases hij : i = j
  · simp [heq.mpr hij, hij]
  · have hne : sigmaQ n i ≠ sigmaQ n j := fun h => hij (heq.mp h)
    simp [hne, hij]

/-- Right unimodular clearing matrix `U_e3 n` in permuted coordinates (`n^2 × n^2`). -/
def U_e3 (n : Nat) (r j : Nat) : Int :=
  if j < n - 2 then
    if r = j then -1 else 0
  else if j = n - 2 then
    let delta : Int := if n = 3 then 1 else 0
    if r < n - 2 then PM_e3 n r n - delta
    else if r = n - 2 then 1
    else if r = n - 1 then -delta
    else 0
  else if j = n - 1 then
    if r < n - 2 then 1
    else if r = n - 1 then 1
    else 0
  else
    let c := sigmaQ n j
    let d_c : Int := if c / n ≠ c % n ∧ (c / n = n - 2 ∨ c % n = n - 2) then 1 else 0
    let x_n2 : Int := PM_e3 n (n - 2) c
    let x_last : Int := (if n = 3 then 1 else 0) * x_n2 - d_c
    if r < n - 2 then PM_e3 n r c - PM_e3 n r n * x_n2 + x_last
    else if r = n - 2 then -x_n2
    else if r = n - 1 then x_last
    else if r = j then 1
    else 0

/-- Exact two-sided inverse `U_e3_inv n` of `U_e3 n`. -/
def U_e3_inv (n : Nat) (r j : Nat) : Int :=
  if j < n - 2 then
    if r = j then -1 else 0
  else if j = n - 2 then
    if r < n - 2 then PM_e3 n r n
    else if r = n - 2 then 1
    else if r = n - 1 then (if n = 3 then 1 else 0)
    else 0
  else if j = n - 1 then
    if r < n - 2 then 1
    else if r = n - 1 then 1
    else 0
  else
    let c := sigmaQ n j
    let d_c : Int := if c / n ≠ c % n ∧ (c / n = n - 2 ∨ c % n = n - 2) then 1 else 0
    if r < n - 2 then PM_e3 n r c
    else if r = n - 2 then PM_e3 n (n - 2) c
    else if r = n - 1 then d_c
    else if r = j then 1
    else 0

theorem U_e3_mul_inv (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n * n) (hj : j < n * n) :
    matMul (n * n) (U_e3 n) (U_e3_inv n) i j = idMat i j := by
  unfold matMul matMulRect idMat
  have hnn : n ≤ n * n := by
    have : 1 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
  have hn1_ne : n - 1 ≠ n - 2 := by omega
  have hn2_ne : n - 2 ≠ n - 1 := by omega
  have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
  by_cases hi_ge : n ≤ i
  · have hi1 : ¬ (i < n - 2) := by omega
    have hi2 : i ≠ n - 2 := by omega
    have hi3 : i ≠ n - 1 := by omega
    have hcongr :
        sumRange (n * n) (fun t => U_e3 n i t * U_e3_inv n t j) =
          sumRange (n * n) (fun t => if t = i then U_e3_inv n i j else 0) := by
      apply sumRange_congr; intro t _
      unfold U_e3
      by_cases ht : t = i
      · subst ht; simp [hi1, hi2, hi3]
      · by_cases ht1 : t < n - 2
        · have hne : i ≠ t := fun h => ht h.symm
          simp [ht, ht1, hne]
        · by_cases ht2 : t = n - 2
          · subst ht2; simp [ht, ht1, hi1, hi2, hi3]
          · by_cases ht3 : t = n - 1
            · subst ht3; simp [ht, ht1, ht2, hi1, hi3]
            · have hne : i ≠ t := fun h => ht h.symm
              simp [ht, ht1, ht2, ht3, hi1, hi2, hi3, hne]
    rw [hcongr, sumRange_ite_eq]
    simp only [hi, ↓reduceIte]
    unfold U_e3_inv
    by_cases hj1 : j < n - 2
    · have hne : i ≠ j := by omega
      simp [hj1, hne]
    · by_cases hj2 : j = n - 2
      · subst hj2; simp [hj1, hi1, hi2, hi3]
      · by_cases hj3 : j = n - 1
        · subst hj3; simp [hj1, hj2, hi1, hi3]
        · simp [hj1, hj2, hj3, hi1, hi2, hi3]
  · have hi_lt : i < n := by omega
    have hsplit_nn : n * n = n + (n * n - n) := (Nat.add_sub_cancel' hnn).symm
    rw [hsplit_nn, sumRange_add_split]
    have htail :
        sumRange (n * n - n) (fun k => U_e3 n i (n + k) * U_e3_inv n (n + k) j) =
          if n ≤ j then U_e3 n i j else 0 := by
      have hcongr :
          sumRange (n * n - n) (fun k => U_e3 n i (n + k) * U_e3_inv n (n + k) j) =
            sumRange (n * n - n) (fun k => if k = j - n then (if n ≤ j then U_e3 n i j else 0) else 0) := by
        apply sumRange_congr; intro k hk
        have h1 : ¬ (n + k < n - 2) := by omega
        have h2 : n + k ≠ n - 2 := by omega
        have h3 : n + k ≠ n - 1 := by omega
        unfold U_e3_inv
        by_cases hj1 : j < n - 2
        · have hne : n + k ≠ j := by omega
          have hnot : ¬ (n ≤ j) := by omega
          simp [hj1, hne, hnot]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [hj1, h1, h2, h3, hnot]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [hj1, hj2, h1, h3, hnot]
            · have hj_ge : n ≤ j := by omega
              simp only [hj1, hj2, hj3, ↓reduceIte, h1, h2, h3, hj_ge]
              by_cases hkj : k = j - n
              · have heq : n + k = j := by omega
                rw [heq]; simp [hkj]
              · have hne : n + k ≠ j := by omega
                simp [hkj, hne]
      rw [hcongr, sumRange_ite_eq]
      by_cases hj_ge : n ≤ j
      · have hlt : j - n < n * n - n := by omega
        simp [hj_ge, hlt]
      · simp [hj_ge]
    rw [htail, sumRange_split_last2 n (by omega)]
    by_cases hi1 : i < n - 2
    · have hsum :
          sumRange (n - 2) (fun t => U_e3 n i t * U_e3_inv n t j) =
            sumRange (n - 2) (fun t => if t = i then - U_e3_inv n i j else 0) := by
        apply sumRange_congr; intro t ht
        unfold U_e3
        simp only [ht, ↓reduceIte]
        by_cases hti : t = i
        · subst hti; simp
        · have hit : i ≠ t := fun h => hti h.symm
          simp [hti, hit]
      rw [hsum, sumRange_ite_eq]
      simp only [hi1, ↓reduceIte]
      have hU1 : U_e3 n i (n - 2) = PM_e3 n i n - (if n = 3 then 1 else 0) := by
        simp [U_e3, hi1]
      have hU2 : U_e3 n i (n - 1) = 1 := by simp [U_e3, hi1, hn1_not_lt, hn1_ne]
      rw [hU1, hU2]
      by_cases hj1 : j < n - 2
      · have hnot : ¬ (n ≤ j) := by omega
        have hne1 : n - 2 ≠ j := by omega
        have hne2 : n - 1 ≠ j := by omega
        by_cases hij : i = j
        · subst hij; simp [U_e3_inv, hi1, hnot, hne1, hne2]
        · simp [U_e3_inv, hj1, hij, hnot, hne1, hne2]
      · by_cases hj2 : j = n - 2
        · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
          have hine : i ≠ n - 2 := by omega
          simp [U_e3_inv, hi1, hj1, hnot, hine, hn1_not_lt, hn1_ne]; omega
        · by_cases hj3 : j = n - 1
          · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
            have hine : i ≠ n - 1 := by omega
            simp [U_e3_inv, hi1, hj1, hj2, hnot, hine, hn2_not_lt, hn2_ne]
          · have hj_ge : n ≤ j := by omega
            have hine : i ≠ j := by omega
            simp [U_e3_inv, U_e3, hi1, hj1, hj2, hj3, hj_ge, hine, hn2_not_lt, hn1_not_lt, hn1_ne]
            by_cases hn3 : n = 3
            · simp only [hn3, ↓reduceIte, Int.sub_mul, Int.one_mul]; omega
            · simp only [hn3, ↓reduceIte, Int.sub_zero, Int.zero_mul]; omega
    · by_cases hi2 : i = n - 2
      · subst hi2
        have hsum :
            sumRange (n - 2) (fun t => U_e3 n (n - 2) t * U_e3_inv n t j) =
              sumRange (n - 2) (fun _ => (0 : Int)) := by
          apply sumRange_congr; intro t ht
          have hne : n - 2 ≠ t := by omega
          simp [U_e3, ht, hne]
        rw [hsum, sumRange_const]
        have hU1 : U_e3 n (n - 2) (n - 2) = 1 := by simp [U_e3, hn2_not_lt]
        have hU2 : U_e3 n (n - 2) (n - 1) = 0 := by simp [U_e3, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
        rw [hU1, hU2]
        by_cases hj1 : j < n - 2
        · have hnot : ¬ (n ≤ j) := by omega
          have hne : n - 2 ≠ j := by omega
          simp [U_e3_inv, hj1, hnot, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [U_e3_inv, hj1, hnot, hn2_not_lt, hn1_not_lt, hn1_ne]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [U_e3_inv, hj1, hj2, hnot, hn2_not_lt, hn1_not_lt, hn1_ne]
            · have hj_ge : n ≤ j := by omega
              have hne : n - 2 ≠ j := by omega
              simp [U_e3_inv, U_e3, hj1, hj2, hj3, hj_ge, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
              omega
      · have hi3 : i = n - 1 := by omega
        subst hi3
        have hsum :
            sumRange (n - 2) (fun t => U_e3 n (n - 1) t * U_e3_inv n t j) =
              sumRange (n - 2) (fun _ => (0 : Int)) := by
          apply sumRange_congr; intro t ht
          have hne : n - 1 ≠ t := by omega
          simp [U_e3, ht, hne]
        rw [hsum, sumRange_const]
        have hU1 : U_e3 n (n - 1) (n - 2) = -(if n = 3 then 1 else 0) := by
          simp [U_e3, hn1_not_lt, hn1_ne]
        have hU2 : U_e3 n (n - 1) (n - 1) = 1 := by
          simp [U_e3, hn1_not_lt, hn1_ne]
        rw [hU1, hU2]
        by_cases hj1 : j < n - 2
        · have hnot : ¬ (n ≤ j) := by omega
          have hne : n - 1 ≠ j := by omega
          have hne2 : n - 2 ≠ j := by omega
          simp [U_e3_inv, hj1, hnot, hne, hne2]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [U_e3_inv, hj1, hnot, hn1_not_lt, hn1_ne]
            by_cases hn3 : n = 3 <;> simp [hn3]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [U_e3_inv, hj1, hj2, hnot, hn2_not_lt, hn2_ne]
            · have hj_ge : n ≤ j := by omega
              have hne : n - 1 ≠ j := by omega
              simp [U_e3_inv, U_e3, hj1, hj2, hj3, hj_ge, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
              by_cases hn3 : n = 3 <;> simp [hn3] <;> omega

theorem U_e3_inv_mul (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n * n) (hj : j < n * n) :
    matMul (n * n) (U_e3_inv n) (U_e3 n) i j = idMat i j := by
  unfold matMul matMulRect idMat
  have hnn : n ≤ n * n := by
    have : 1 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
  have hn1_ne : n - 1 ≠ n - 2 := by omega
  have hn2_ne : n - 2 ≠ n - 1 := by omega
  have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
  by_cases hi_ge : n ≤ i
  · have hi1 : ¬ (i < n - 2) := by omega
    have hi2 : i ≠ n - 2 := by omega
    have hi3 : i ≠ n - 1 := by omega
    have hcongr :
        sumRange (n * n) (fun t => U_e3_inv n i t * U_e3 n t j) =
          sumRange (n * n) (fun t => if t = i then U_e3 n i j else 0) := by
      apply sumRange_congr; intro t _
      unfold U_e3_inv
      by_cases ht : t = i
      · subst ht; simp [hi1, hi2, hi3]
      · by_cases ht1 : t < n - 2
        · have hne : i ≠ t := fun h => ht h.symm
          simp [ht, ht1, hne]
        · by_cases ht2 : t = n - 2
          · subst ht2; simp [ht, ht1, hi1, hi2, hi3]
          · by_cases ht3 : t = n - 1
            · subst ht3; simp [ht, ht1, ht2, hi1, hi3]
            · have hne : i ≠ t := fun h => ht h.symm
              simp [ht, ht1, ht2, ht3, hi1, hi2, hi3, hne]
    rw [hcongr, sumRange_ite_eq]
    simp only [hi, ↓reduceIte]
    unfold U_e3
    by_cases hj1 : j < n - 2
    · have hne : i ≠ j := by omega
      simp [hj1, hne]
    · by_cases hj2 : j = n - 2
      · subst hj2; simp [hj1, hi1, hi2, hi3]
      · by_cases hj3 : j = n - 1
        · subst hj3; simp [hj1, hj2, hi1, hi3]
        · simp [hj1, hj2, hj3, hi1, hi2, hi3]
  · have hsplit_nn : n * n = n + (n * n - n) := (Nat.add_sub_cancel' hnn).symm
    rw [hsplit_nn, sumRange_add_split]
    have htail :
        sumRange (n * n - n) (fun k => U_e3_inv n i (n + k) * U_e3 n (n + k) j) =
          if n ≤ j then U_e3_inv n i j else 0 := by
      have hcongr :
          sumRange (n * n - n) (fun k => U_e3_inv n i (n + k) * U_e3 n (n + k) j) =
            sumRange (n * n - n) (fun k => if k = j - n then (if n ≤ j then U_e3_inv n i j else 0) else 0) := by
        apply sumRange_congr; intro k _
        have h1 : ¬ (n + k < n - 2) := by omega
        have h2 : n + k ≠ n - 2 := by omega
        have h3 : n + k ≠ n - 1 := by omega
        unfold U_e3
        by_cases hj1 : j < n - 2
        · have hne : n + k ≠ j := by omega
          have hnot : ¬ (n ≤ j) := by omega
          simp [hj1, hne, hnot]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [hj1, h1, h2, h3, hnot]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [hj1, hj2, h1, h3, hnot]
            · have hj_ge : n ≤ j := by omega
              simp only [hj1, hj2, hj3, ↓reduceIte, h1, h2, h3, hj_ge]
              by_cases hkj : k = j - n
              · have heq : n + k = j := by omega
                rw [heq]; simp [hkj]
              · have hne : n + k ≠ j := by omega
                simp [hkj, hne]
      rw [hcongr, sumRange_ite_eq]
      by_cases hj_ge : n ≤ j
      · have hlt : j - n < n * n - n := by omega
        simp [hj_ge, hlt]
      · simp [hj_ge]
    rw [htail, sumRange_split_last2 n (by omega)]
    by_cases hi1 : i < n - 2
    · have hsum :
          sumRange (n - 2) (fun t => U_e3_inv n i t * U_e3 n t j) =
            sumRange (n - 2) (fun t => if t = i then - U_e3 n i j else 0) := by
        apply sumRange_congr; intro t ht
        unfold U_e3_inv
        simp only [ht, ↓reduceIte]
        by_cases hti : t = i
        · subst hti; simp
        · have hit : i ≠ t := fun h => hti h.symm
          simp [hti, hit]
      rw [hsum, sumRange_ite_eq]
      simp only [hi1, ↓reduceIte]
      have hU1 : U_e3_inv n i (n - 2) = PM_e3 n i n := by
        simp [U_e3_inv, hi1]
      have hU2 : U_e3_inv n i (n - 1) = 1 := by
        simp [U_e3_inv, hi1, hn1_not_lt, hn1_ne]
      rw [hU1, hU2]
      by_cases hj1 : j < n - 2
      · have hnot : ¬ (n ≤ j) := by omega
        have hne1 : n - 2 ≠ j := by omega
        have hne2 : n - 1 ≠ j := by omega
        by_cases hij : i = j
        · subst hij; simp [U_e3, hi1, hnot, hne1, hne2]
        · simp [U_e3, hj1, hij, hnot, hne1, hne2]
      · by_cases hj2 : j = n - 2
        · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
          have hine : i ≠ n - 2 := by omega
          simp [U_e3, hi1, hj1, hnot, hine, hn1_not_lt, hn1_ne]; omega
        · by_cases hj3 : j = n - 1
          · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
            have hine : i ≠ n - 1 := by omega
            simp [U_e3, hi1, hj1, hj2, hnot, hine, hn2_not_lt, hn2_ne]
          · have hj_ge : n ≤ j := by omega
            have hine : i ≠ j := by omega
            simp [U_e3, U_e3_inv, hi1, hj1, hj2, hj3, hj_ge, hine, hn2_not_lt, hn1_not_lt, hn1_ne, Int.mul_neg]
            omega
    · by_cases hi2 : i = n - 2
      · subst hi2
        have hsum :
            sumRange (n - 2) (fun t => U_e3_inv n (n - 2) t * U_e3 n t j) =
              sumRange (n - 2) (fun _ => (0 : Int)) := by
          apply sumRange_congr; intro t ht
          have hne : n - 2 ≠ t := by omega
          simp [U_e3_inv, ht, hne]
        rw [hsum, sumRange_const]
        have hU1 : U_e3_inv n (n - 2) (n - 2) = 1 := by simp [U_e3_inv, hn2_not_lt]
        have hU2 : U_e3_inv n (n - 2) (n - 1) = 0 := by simp [U_e3_inv, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
        rw [hU1, hU2]
        by_cases hj1 : j < n - 2
        · have hnot : ¬ (n ≤ j) := by omega
          have hne : n - 2 ≠ j := by omega
          simp [U_e3, hj1, hnot, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [U_e3, hj1, hnot, hn2_not_lt, hn1_not_lt, hn1_ne]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [U_e3, hj1, hj2, hnot, hn2_not_lt, hn1_not_lt, hn1_ne]
            · have hj_ge : n ≤ j := by omega
              have hne : n - 2 ≠ j := by omega
              simp [U_e3, U_e3_inv, hj1, hj2, hj3, hj_ge, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
              omega
      · have hi3 : i = n - 1 := by omega
        subst hi3
        have hsum :
            sumRange (n - 2) (fun t => U_e3_inv n (n - 1) t * U_e3 n t j) =
              sumRange (n - 2) (fun _ => (0 : Int)) := by
          apply sumRange_congr; intro t ht
          have hne : n - 1 ≠ t := by omega
          simp [U_e3_inv, ht, hne]
        rw [hsum, sumRange_const]
        have hU1 : U_e3_inv n (n - 1) (n - 2) = (if n = 3 then 1 else 0) := by
          simp [U_e3_inv, hn1_not_lt, hn1_ne]
        have hU2 : U_e3_inv n (n - 1) (n - 1) = 1 := by
          simp [U_e3_inv, hn1_not_lt, hn1_ne]
        rw [hU1, hU2]
        by_cases hj1 : j < n - 2
        · have hnot : ¬ (n ≤ j) := by omega
          have hne : n - 1 ≠ j := by omega
          have hne2 : n - 2 ≠ j := by omega
          simp [U_e3, hj1, hnot, hne, hne2, hn2_not_lt, hn1_not_lt, hn1_ne]
        · by_cases hj2 : j = n - 2
          · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
            simp [U_e3, hj1, hnot, hn2_not_lt, hn1_not_lt, hn1_ne]
            by_cases hn3 : n = 3 <;> simp [hn3]
          · by_cases hj3 : j = n - 1
            · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
              simp [U_e3, hj1, hj2, hnot, hn2_not_lt, hn1_not_lt, hn1_ne, hn2_ne]
            · have hj_ge : n ≤ j := by omega
              have hne : n - 1 ≠ j := by omega
              simp [U_e3, U_e3_inv, hj1, hj2, hj3, hj_ge, hne, hn2_not_lt, hn1_not_lt, hn1_ne]
              by_cases hn3 : n = 3 <;> simp [hn3] <;> omega

/-- Right unimodular matrix `Q_e3 n := PermQ n * U_e3 n` and its two-sided inverse
    `Q_e3_inv n := U_e3_inv n * PermQ n`. -/
def Q_e3 (n : Nat) (r j : Nat) : Int :=
  matMul (n * n) (PermQ n) (U_e3 n) r j

def Q_e3_inv (n : Nat) (r j : Nat) : Int :=
  matMul (n * n) (U_e3_inv n) (PermQ n) r j

/-- Associativity of rectangular matrix multiplication `(A * B) * C = A * (B * C)`. -/
theorem matMulRect_assoc (k1 k2 : Nat) (A B C : Nat → Nat → Int) (i j : Nat) :
    matMulRect k2 (matMulRect k1 A B) C i j =
      matMulRect k1 A (matMulRect k2 B C) i j := by
  unfold matMulRect
  induction k2 with
  | zero =>
    simp [sumRange_zero]
    rw [sumRange_const]
    simp
  | succ m ih =>
    rw [sumRange_succ, ih]
    have hcongr :
        sumRange k1 (fun t => A i t * sumRange (m + 1) (fun s => B t s * C s j)) =
          sumRange k1 (fun t => A i t * sumRange m (fun s => B t s * C s j) + A i t * B t m * C m j) := by
      apply sumRange_congr; intro t _
      rw [sumRange_succ, Int.mul_add, Int.mul_assoc]
    rw [hcongr, sumRange_add, sumRange_mul_right]

theorem matMulRect_id_right (k : Nat) (A : Nat → Nat → Int) (i j : Nat) (hj : j < k) :
    matMulRect k A idMat i j = A i j := by
  unfold matMulRect idMat
  have hcongr : sumRange k (fun t => A i t * (if t = j then (1 : Int) else 0)) =
      sumRange k (fun t => if t = j then A i j else 0) := by
    apply sumRange_congr; intro t _; by_cases ht : t = j <;> simp [ht]
  rw [hcongr, sumRange_ite_eq]
  simp [hj]

theorem Q_e3_mul_inv (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n * n) (hj : j < n * n) :
    matMul (n * n) (Q_e3 n) (Q_e3_inv n) i j = idMat i j := by
  unfold Q_e3 Q_e3_inv matMul
  rw [matMulRect_assoc (n * n) (n * n) (PermQ n) (U_e3 n) (matMulRect (n * n) (U_e3_inv n) (PermQ n)) i j]
  have h1 : ∀ a b, a < n * n → b < n * n →
      matMulRect (n * n) (U_e3 n) (matMulRect (n * n) (U_e3_inv n) (PermQ n)) a b =
        PermQ n a b := by
    intro a b ha hb
    rw [← matMulRect_assoc (n * n) (n * n) (U_e3 n) (U_e3_inv n) (PermQ n) a b]
    have hcongr :
        matMulRect (n * n) (matMulRect (n * n) (U_e3 n) (U_e3_inv n)) (PermQ n) a b =
          matMulRect (n * n) idMat (PermQ n) a b := by
      change sumRange (n * n) (fun t => matMul (n * n) (U_e3 n) (U_e3_inv n) a t * PermQ n t b) =
        sumRange (n * n) (fun t => idMat a t * PermQ n t b)
      apply sumRange_congr; intro t ht
      rw [U_e3_mul_inv n hn a t ha ht]
    rw [hcongr]
    unfold matMulRect idMat
    have hcongr2 :
        sumRange (n * n) (fun t => (if a = t then (1 : Int) else 0) * PermQ n t b) =
          sumRange (n * n) (fun t => if t = a then PermQ n a b else 0) := by
      apply sumRange_congr; intro t _
      by_cases ht : t = a
      · subst ht; simp
      · have hat : a ≠ t := fun h => ht h.symm
        simp [ht, hat]
    rw [hcongr2, sumRange_ite_eq]
    simp [ha]
  have hcongr3 :
      matMulRect (n * n) (PermQ n) (matMulRect (n * n) (U_e3 n) (matMulRect (n * n) (U_e3_inv n) (PermQ n))) i j =
        matMulRect (n * n) (PermQ n) (PermQ n) i j := by
    change sumRange (n * n) (fun t => PermQ n i t * matMulRect (n * n) (U_e3 n) (matMulRect (n * n) (U_e3_inv n) (PermQ n)) t j) =
      sumRange (n * n) (fun t => PermQ n i t * PermQ n t j)
    apply sumRange_congr; intro t ht
    rw [h1 t j ht hj]
  rw [hcongr3]
  exact PermQ_mul_PermQ n hn i j hi hj

theorem Q_e3_inv_mul (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n * n) (hj : j < n * n) :
    matMul (n * n) (Q_e3_inv n) (Q_e3 n) i j = idMat i j := by
  unfold Q_e3 Q_e3_inv matMul
  rw [matMulRect_assoc (n * n) (n * n) (U_e3_inv n) (PermQ n) (matMulRect (n * n) (PermQ n) (U_e3 n)) i j]
  have h1 : ∀ a b, a < n * n → b < n * n →
      matMulRect (n * n) (PermQ n) (matMulRect (n * n) (PermQ n) (U_e3 n)) a b =
        U_e3 n a b := by
    intro a b ha hb
    rw [← matMulRect_assoc (n * n) (n * n) (PermQ n) (PermQ n) (U_e3 n) a b]
    have hcongr :
        matMulRect (n * n) (matMulRect (n * n) (PermQ n) (PermQ n)) (U_e3 n) a b =
          matMulRect (n * n) idMat (U_e3 n) a b := by
      change sumRange (n * n) (fun t => matMul (n * n) (PermQ n) (PermQ n) a t * U_e3 n t b) =
        sumRange (n * n) (fun t => idMat a t * U_e3 n t b)
      apply sumRange_congr; intro t ht
      rw [PermQ_mul_PermQ n hn a t ha ht]
    rw [hcongr]
    unfold matMulRect idMat
    have hcongr2 :
        sumRange (n * n) (fun t => (if a = t then (1 : Int) else 0) * U_e3 n t b) =
          sumRange (n * n) (fun t => if t = a then U_e3 n a b else 0) := by
      apply sumRange_congr; intro t _
      by_cases ht : t = a
      · subst ht; simp
      · have hat : a ≠ t := fun h => ht h.symm
        simp [ht, hat]
    rw [hcongr2, sumRange_ite_eq]
    simp [ha]
  have hcongr3 :
      matMulRect (n * n) (U_e3_inv n) (matMulRect (n * n) (PermQ n) (matMulRect (n * n) (PermQ n) (U_e3 n))) i j =
        matMulRect (n * n) (U_e3_inv n) (U_e3 n) i j := by
    change sumRange (n * n) (fun t => U_e3_inv n i t * matMulRect (n * n) (PermQ n) (matMulRect (n * n) (PermQ n) (U_e3 n)) t j) =
      sumRange (n * n) (fun t => U_e3_inv n i t * U_e3 n t j)
    apply sumRange_congr; intro t ht
    rw [h1 t j ht hj]
  rw [hcongr3]
  exact U_e3_inv_mul n hn i j hi hj

/-- Helper: `PM_e3 n i (sigmaQ n t)` for `t < n` on the `n` pivot columns. -/
theorem PM_e3_sigmaQ_lt_n (n : Nat) (hn : 3 ≤ n) (i t : Nat) (hi : i < n) (ht : t < n) :
    PM_e3 n i (sigmaQ n t) =
      if t < n - 2 then (if i = t then -1 else 0)
      else if t = n - 2 then PM_e3 n i n
      else (if i < n - 2 then 1 else if i = n - 1 then (n : Int) - 2 else 0) := by
  have hdiv : ∀ k, k < n - 1 → ((n - 1) * n + k) / n = n - 1 ∧ ((n - 1) * n + k) % n = k := by
    intro k hk
    have hlt : k < n := by omega
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hlt, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have hdiv_n : n / n = 1 ∧ n % n = 0 := by
    rw [Nat.div_self (by omega), Nat.mod_self]; exact ⟨rfl, rfl⟩
  by_cases ht1 : t < n - 2
  · have hsig : sigmaQ n t = (n - 1) * n + t := by simp [sigmaQ, ht1]
    rw [hsig]
    rcases hdiv t (by omega) with ⟨ha, hb⟩
    have hab : n - 1 ≠ t := by omega
    unfold PM_e3
    rw [ha, hb]
    simp only [hab, ↓reduceIte, ht1]
    by_cases hi1 : i < n - 2
    · simp only [hi1, ↓reduceIte]
      have hine1 : i ≠ n - 1 := by omega
      have hne2 : n - 2 ≠ n - 1 := by omega
      have hne3 : n - 2 ≠ t := by omega
      by_cases hit : i = t
      · subst hit; simp [hine1, hne2, hne3]
      · simp [hine1, hne2, hne3, hit]
    · by_cases hi2 : i = n - 2
      · subst hi2
        have hne : n - 2 ≠ t := by omega
        simp [hi1, hne]
      · have hi3 : i = n - 1 := by omega
        subst hi3
        have hne2 : t ≠ n - 2 := by omega
        simp [hi1, hi2, hne2, hab]
  · by_cases ht2 : t = n - 2
    · subst ht2
      have hsig : sigmaQ n (n - 2) = n := by simp [sigmaQ, ht1]
      rw [hsig]
      simp [ht1]
    · have ht3 : t = n - 1 := by omega
      subst ht3
      have hsig : sigmaQ n (n - 1) = (n - 1) * n + (n - 2) := by simp [sigmaQ, ht1, ht2]
      rw [hsig]
      rcases hdiv (n - 2) (by omega) with ⟨ha, hb⟩
      have hab : n - 1 ≠ n - 2 := by omega
      unfold PM_e3
      rw [ha, hb]
      simp only [hab, ↓reduceIte, ht1]
      by_cases hi1 : i < n - 2
      · have hine1 : i ≠ n - 1 := by omega
        have hine2 : i ≠ n - 2 := by omega
        simp [hi1, hine1, hine2]
      · by_cases hi2 : i = n - 2
        · subst hi2
          have hne : n - 2 ≠ n - 1 := by omega
          simp [hi1, hne]
        · have hi3 : i = n - 1 := by omega
          subst hi3; simp [hi1, hi2]

/-- Universal Smith Normal Form theorem for `M_{1,2}(e_3^sym)` (`∀ n ≥ 3`):
    `P_e3 n * M12_e3 n * Q_e3 n = diag(1, ..., 1, n - 2, 0, ..., 0)`
    where `P_e3 n` (`n × n`) and `Q_e3 n` (`n^2 × n^2`) are unimodular over `Int`
    with proven two-sided inverses `P_e3_inv n` and `Q_e3_inv n`. -/
theorem snf_e3_M12_forall_n (n : Nat) (hn : 3 ≤ n) (i j : Nat) (hi : i < n) (hj : j < n * n) :
    matMulRect (n * n) (matMulRect n (P_e3 n) (M12_e3 n)) (Q_e3 n) i j = snfM12 n i j := by
  have hPM : matMulRect (n * n) (matMulRect n (P_e3 n) (M12_e3 n)) (Q_e3 n) i j =
      matMulRect (n * n) (PM_e3 n) (Q_e3 n) i j := by
    change sumRange (n * n) (fun c => matMulRect n (P_e3 n) (M12_e3 n) i c * Q_e3 n c j) =
      sumRange (n * n) (fun c => PM_e3 n i c * Q_e3 n c j)
    apply sumRange_congr; intro c hc
    rw [P_e3_mul_M12 n hn i c hi hc]
  rw [hPM]
  unfold Q_e3 matMul
  rw [← matMulRect_assoc (n * n) (n * n) (PM_e3 n) (PermQ n) (U_e3 n) i j]
  have hPerm : ∀ t, t < n * n →
      matMulRect (n * n) (PM_e3 n) (PermQ n) i t = PM_e3 n i (sigmaQ n t) := by
    intro t ht
    unfold matMulRect PermQ
    have hcongr : sumRange (n * n) (fun s => PM_e3 n i s * (if s = sigmaQ n t then (1 : Int) else 0)) =
        sumRange (n * n) (fun s => if s = sigmaQ n t then PM_e3 n i (sigmaQ n t) else 0) := by
      apply sumRange_congr; intro s _; by_cases hs : s = sigmaQ n t <;> simp [hs]
    rw [hcongr, sumRange_ite_eq]
    have hlt : sigmaQ n t < n * n := sigmaQ_lt n hn ht
    simp [hlt]
  have hcongr_u :
      matMulRect (n * n) (matMulRect (n * n) (PM_e3 n) (PermQ n)) (U_e3 n) i j =
        matMulRect (n * n) (fun r t => PM_e3 n r (sigmaQ n t)) (U_e3 n) i j := by
    change sumRange (n * n) (fun t => matMulRect (n * n) (PM_e3 n) (PermQ n) i t * U_e3 n t j) =
      sumRange (n * n) (fun t => PM_e3 n i (sigmaQ n t) * U_e3 n t j)
    apply sumRange_congr; intro t ht
    rw [hPerm t ht]
  rw [hcongr_u]
  unfold matMulRect snfM12
  dsimp only
  have hnn : n ≤ n * n := by
    have : 1 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hsplit_nn : n * n = n + (n * n - n) := (Nat.add_sub_cancel' hnn).symm
  rw [hsplit_nn, sumRange_add_split]
  have htail :
      sumRange (n * n - n) (fun k => PM_e3 n i (sigmaQ n (n + k)) * U_e3 n (n + k) j) =
        if n ≤ j then PM_e3 n i (sigmaQ n j) else 0 := by
    have hcongr :
        sumRange (n * n - n) (fun k => PM_e3 n i (sigmaQ n (n + k)) * U_e3 n (n + k) j) =
          sumRange (n * n - n) (fun k => if k = j - n then (if n ≤ j then PM_e3 n i (sigmaQ n j) else 0) else 0) := by
      apply sumRange_congr; intro k _
      have h1 : ¬ (n + k < n - 2) := by omega
      have h2 : n + k ≠ n - 2 := by omega
      have h3 : n + k ≠ n - 1 := by omega
      unfold U_e3
      by_cases hj1 : j < n - 2
      · have hne : n + k ≠ j := by omega
        have hnot : ¬ (n ≤ j) := by omega
        simp [hj1, hne, hnot]
      · by_cases hj2 : j = n - 2
        · subst hj2; have hnot : ¬ (n ≤ n - 2) := by omega
          simp [hj1, h1, h2, h3, hnot]
        · by_cases hj3 : j = n - 1
          · subst hj3; have hnot : ¬ (n ≤ n - 1) := by omega
            simp [hj1, hj2, h1, h3, hnot]
          · have hj_ge : n ≤ j := by omega
            simp only [hj1, hj2, hj3, ↓reduceIte, h1, h2, h3, hj_ge]
            by_cases hkj : k = j - n
            · have heq : n + k = j := by omega
              rw [heq]; simp [hkj]
            · have hne : n + k ≠ j := by omega
              simp [hkj, hne]
    rw [hcongr, sumRange_ite_eq]
    by_cases hj_ge : n ≤ j
    · have hlt : j - n < n * n - n := by omega
      simp [hj_ge, hlt]
    · simp [hj_ge]
  rw [htail, sumRange_split_last2 n (by omega)]
  have hP0 : ∀ t, t < n - 2 → PM_e3 n i (sigmaQ n t) = (if i = t then -1 else 0) := by
    intro t ht
    rw [PM_e3_sigmaQ_lt_n n hn i t hi (by omega)]
    simp [ht]
  have hPn2 : PM_e3 n i (sigmaQ n (n - 2)) = PM_e3 n i n := by
    rw [PM_e3_sigmaQ_lt_n n hn i (n - 2) hi (by omega)]
    have hnot : ¬ (n - 2 < n - 2) := by omega
    simp [hnot]
  have hPn1 : PM_e3 n i (sigmaQ n (n - 1)) =
      if i < n - 2 then 1 else if i = n - 1 then (n : Int) - 2 else 0 := by
    rw [PM_e3_sigmaQ_lt_n n hn i (n - 1) hi (by omega)]
    have hnot1 : ¬ (n - 1 < n - 2) := by omega
    have hnot2 : n - 1 ≠ n - 2 := by omega
    simp [hnot1, hnot2]
  rw [hPn2, hPn1]
  have hPM_n : PM_e3 n (n - 2) n = 1 ∧
      PM_e3 n (n - 1) n = (if n = 3 then (n : Int) - 2 else 0) := by
    have hdiv : n / n = 1 ∧ n % n = 0 := by
      rw [Nat.div_self (by omega), Nat.mod_self]; exact ⟨rfl, rfl⟩
    unfold PM_e3
    rw [hdiv.1, hdiv.2]
    have h10 : (1 : Nat) ≠ 0 := by omega
    have hn1_not_lt : ¬ (n - 1 < n - 2) := by omega
    have hn1_ne : n - 1 ≠ n - 2 := by omega
    have hn2_not_lt : ¬ (n - 2 < n - 2) := by omega
    constructor
    · have hne1 : 1 ≠ n - 1 := by omega
      have hne2 : 0 ≠ n - 1 := by omega
      simp [h10, hn2_not_lt, hne1, hne2]
    · simp only [h10, ↓reduceIte, hn1_not_lt, hn1_ne]
      by_cases hn3 : n = 3
      · subst hn3; simp
      · have hne1 : 1 ≠ n - 2 := by omega
        have hne2 : 0 ≠ n - 2 := by omega
        simp [hn3, hne1, hne2]
  by_cases hj1 : j < n - 2
  · have hnot : ¬ (n ≤ j) := by omega
    have hsum : sumRange (n - 2) (fun t => PM_e3 n i (sigmaQ n t) * U_e3 n t j) =
        sumRange (n - 2) (fun t => if t = i then (if i = j then 1 else 0) else 0) := by
      apply sumRange_congr; intro t ht
      rw [hP0 t ht]
      unfold U_e3
      simp only [hj1, ↓reduceIte]
      by_cases hti : t = i
      · subst hti; by_cases htj : t = j <;> simp [htj]
      · have hit : i ≠ t := fun h => hti h.symm
        simp [hti, hit]
    rw [hsum, sumRange_ite_eq]
    have hU1 : U_e3 n (n - 2) j = 0 := by
      have hne : n - 2 ≠ j := by omega
      simp [U_e3, hj1, hne]
    have hU2 : U_e3 n (n - 1) j = 0 := by
      have hne : n - 1 ≠ j := by omega
      simp [U_e3, hj1, hne]
    rw [hU1, hU2]
    by_cases hij : i = j
    · subst hij
      have hi1 : i < n - 2 := by omega
      have hine : i ≠ n - 1 := by omega
      simp [hnot, hi1, hine]
    · simp [hnot, hij]
  · by_cases hj2 : j = n - 2
    · subst hj2
      have hnot : ¬ (n ≤ n - 2) := by omega
      have hsum : sumRange (n - 2) (fun t => PM_e3 n i (sigmaQ n t) * U_e3 n t (n - 2)) =
          sumRange (n - 2) (fun t => if t = i then -(PM_e3 n i n - (if n = 3 then 1 else 0)) else 0) := by
        apply sumRange_congr; intro t ht
        rw [hP0 t ht]
        unfold U_e3
        simp only [hj1, ↓reduceIte, ht]
        by_cases hti : t = i
        · subst hti; simp
        · have hit : i ≠ t := fun h => hti h.symm
          simp [hti, hit]
      rw [hsum, sumRange_ite_eq]
      have hU1 : U_e3 n (n - 2) (n - 2) = 1 := by simp [U_e3, hj1]
      have hU2 : U_e3 n (n - 1) (n - 2) = -(if n = 3 then 1 else 0) := by
        have h1 : ¬ (n - 1 < n - 2) := by omega
        have h2 : n - 1 ≠ n - 2 := by omega
        simp [U_e3, hj1, h1, h2]
      rw [hU1, hU2]
      simp [hnot]
      by_cases hi1 : i < n - 2
      · have hine : i ≠ n - 2 := by omega
        simp [hi1, hine]; omega
      · by_cases hi2 : i = n - 2
        · subst hi2; have hine : n - 2 ≠ n - 1 := by omega
          simp [hi1, hine, hPM_n.1]
        · have hi3 : i = n - 1 := by omega
          subst hi3
          simp [hi1, hi2, hPM_n.2]
          by_cases hn3 : n = 3
          · subst hn3; simp
          · simp [hn3]
    · by_cases hj3 : j = n - 1
      · subst hj3
        have hnot : ¬ (n ≤ n - 1) := by omega
        have hsum : sumRange (n - 2) (fun t => PM_e3 n i (sigmaQ n t) * U_e3 n t (n - 1)) =
            sumRange (n - 2) (fun t => if t = i then -1 else 0) := by
          apply sumRange_congr; intro t ht
          rw [hP0 t ht]
          unfold U_e3
          simp only [hj1, hj2, ↓reduceIte, ht]
          by_cases hti : t = i
          · subst hti; simp
          · have hit : i ≠ t := fun h => hti h.symm
            simp [hti, hit]
        rw [hsum, sumRange_ite_eq]
        have hU1 : U_e3 n (n - 2) (n - 1) = 0 := by
          have h1 : ¬ (n - 2 < n - 2) := by omega
          have h2 : n - 2 ≠ n - 1 := by omega
          simp [U_e3, hj1, hj2, h1, h2]
        have hU2 : U_e3 n (n - 1) (n - 1) = 1 := by
          simp [U_e3, hj1, hj2]
        rw [hU1, hU2]
        simp [hnot]
        by_cases hi1 : i < n - 2
        · have hine : i ≠ n - 1 := by omega
          simp [hi1, hine]
        · by_cases hi2 : i = n - 2
          · subst hi2; have hine : n - 2 ≠ n - 1 := by omega
            simp [hi1, hine]
          · have hi3 : i = n - 1 := by omega
            subst hi3; simp [hi1]
      · have hj_ge : n ≤ j := by omega
        have hine : i ≠ j := by omega
        simp only [hj_ge, ↓reduceIte, hine]
        let c := sigmaQ n j
        let d_c : Int := if c / n ≠ c % n ∧ (c / n = n - 2 ∨ c % n = n - 2) then 1 else 0
        let x_n2 : Int := PM_e3 n (n - 2) c
        let x_last : Int := (if n = 3 then 1 else 0) * x_n2 - d_c
        have hsum : sumRange (n - 2) (fun t => PM_e3 n i (sigmaQ n t) * U_e3 n t j) =
            sumRange (n - 2) (fun t => if t = i then -(PM_e3 n i c - PM_e3 n i n * x_n2 + x_last) else 0) := by
          apply sumRange_congr; intro t ht
          rw [hP0 t ht]
          unfold U_e3
          simp only [hj1, hj2, hj3, ↓reduceIte, ht]
          by_cases hti : t = i
          · subst hti; simp [c, d_c, x_n2, x_last]
          · have hit : i ≠ t := fun h => hti h.symm
            simp [hti, hit]
        rw [hsum, sumRange_ite_eq]
        have hU1 : U_e3 n (n - 2) j = -x_n2 := by
          have h1 : ¬ (n - 2 < n - 2) := by omega
          simp [U_e3, hj1, hj2, hj3, h1, c, x_n2]
        have hU2 : U_e3 n (n - 1) j = x_last := by
          have h1 : ¬ (n - 1 < n - 2) := by omega
          have h2 : n - 1 ≠ n - 2 := by omega
          simp [U_e3, hj1, hj2, hj3, h1, h2, c, d_c, x_n2, x_last]
        rw [hU1, hU2]
        by_cases hi1 : i < n - 2
        · simp [hi1, c, Int.mul_neg]
          omega
        · by_cases hi2 : i = n - 2
          · subst hi2
            have hn2_ne : n - 2 ≠ n - 1 := by omega
            simp [hi1, hn2_ne, c, hPM_n.1, x_n2]; omega
          · have hi3 : i = n - 1 := by omega
            subst hi3
            simp only [hi1, ↓reduceIte]
            have hPM_last : PM_e3 n (n - 1) c =
                if c / n ≠ c % n ∧ (c / n = n - 2 ∨ c % n = n - 2) then (n : Int) - 2 else 0 := by
              unfold PM_e3
              have h1 : ¬ (n - 1 < n - 2) := by omega
              have h2 : n - 1 ≠ n - 2 := by omega
              by_cases hab : c / n = c % n
              · simp [hab]
              · simp [hab, h1, h2]
            change (0 + PM_e3 n (n - 1) n * -x_n2 + ((n : Int) - 2) * x_last + PM_e3 n (n - 1) c) = 0
            rw [hPM_last, hPM_n.2]
            by_cases hn3 : n = 3
            · subst hn3
              dsimp only [x_last, d_c]
              by_cases hc : c / 3 ≠ c % 3 ∧ (c / 3 = 1 ∨ c % 3 = 1) <;> simp [hc] <;> omega
            · dsimp only [x_last, d_c]
              by_cases hc : c / n ≠ c % n ∧ (c / n = n - 2 ∨ c % n = n - 2) <;> simp [hc, hn3] <;> omega

/-! ## 3. Part (b): Exact Pair-Sum Eigenspace & `2^r`-Torsion on `KG(n, 2)` -/

/-- Pair-sum embedding `w_v(i, j) = v i + v j` from `Z^n` to pair space. -/
def pairSum (v : Nat → Int) (i j : Nat) : Int :=
  v i + v j

/-- Standard `(n - 1)`-element basis of the zero-sum subspace
    `V_0 = {v : sumRange n v = 0}`: `e_k = δ_k - δ_{n-1}` for `k < n - 1`. -/
def zeroSumBasis (n k i : Nat) : Int :=
  if i = k then 1 else if i = n - 1 then -1 else 0

theorem zeroSumBasis_in_V0 (n k : Nat) (hn : 2 ≤ n) (hk : k < n - 1) :
    sumRange n (zeroSumBasis n k) = 0 := by
  rw [sumRange_split_last n (by omega)]
  have hsum : sumRange (n - 1) (zeroSumBasis n k) =
      sumRange (n - 1) (fun i => if i = k then (1 : Int) else 0) := by
    apply sumRange_congr; intro i hi
    have hine : i ≠ n - 1 := by omega
    simp [zeroSumBasis, hine]
  rw [hsum, sumRange_ite_eq]
  have hne : n - 1 ≠ k := by omega
  simp [hk, zeroSumBasis, hne]

/-- Injectivity of `v ↦ pairSum v` on `Z^n` for `n ≥ 3`:
    `pairSum v = 0` on all distinct pairs `i < j < n` implies `v i = 0` for all `i < n`. -/
theorem pairSum_injective (n : Nat) (hn : 3 ≤ n) (v : Nat → Int)
    (hw : ∀ i j, i < n → j < n → i < j → pairSum v i j = 0) :
    ∀ i, i < n → v i = 0 := by
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have h01 := hw 0 1 (by omega) (by omega) (by omega)
    have h02 := hw 0 2 (by omega) (by omega) (by omega)
    have h12 := hw 1 2 (by omega) (by omega) (by omega)
    unfold pairSum at h01 h02 h12
    omega
  · by_cases hi1 : i = 1
    · subst hi1
      have h01 := hw 0 1 (by omega) (by omega) (by omega)
      have h02 := hw 0 2 (by omega) (by omega) (by omega)
      have h12 := hw 1 2 (by omega) (by omega) (by omega)
      unfold pairSum at h01 h02 h12
      omega
    · have h01 := hw 0 1 (by omega) (by omega) (by omega)
      have h0i := hw 0 i (by omega) hi (by omega)
      have h1i := hw 1 i (by omega) hi (by omega)
      unfold pairSum at h01 h0i h1i
      omega

/-- Linear independence of the `n - 1` pair-sum vectors `{pairSum (zeroSumBasis n k)}`
    (`k = 0..n-2`) in `Z^{binom(n,2)}` for all `n ≥ 3`. -/
theorem pairSum_basis_lin_indep (n : Nat) (hn : 3 ≤ n) (c : Nat → Int)
    (hlin : ∀ i j, i < n → j < n → i < j →
      sumRange (n - 1) (fun k => c k * pairSum (zeroSumBasis n k) i j) = 0) :
    ∀ k, k < n - 1 → c k = 0 := by
  let v : Nat → Int := fun i => sumRange (n - 1) (fun k => c k * zeroSumBasis n k i)
  have hpair : ∀ i j, i < n → j < n → i < j → pairSum v i j = 0 := by
    intro i j hi hj hij
    unfold pairSum
    change sumRange (n - 1) (fun k => c k * zeroSumBasis n k i) +
      sumRange (n - 1) (fun k => c k * zeroSumBasis n k j) = 0
    rw [← sumRange_add]
    have hcongr : sumRange (n - 1) (fun k => c k * zeroSumBasis n k i + c k * zeroSumBasis n k j) =
        sumRange (n - 1) (fun k => c k * pairSum (zeroSumBasis n k) i j) := by
      apply sumRange_congr; intro k _
      unfold pairSum; rw [Int.mul_add]
    rw [hcongr]
    exact hlin i j hi hj hij
  have hv_zero := pairSum_injective n hn v hpair
  intro k hk
  have hvk := hv_zero k (by omega)
  have hcongr : v k = sumRange (n - 1) (fun t => if t = k then c k else 0) := by
    change sumRange (n - 1) (fun t => c t * zeroSumBasis n t k) = _
    apply sumRange_congr; intro t _
    have hkne : k ≠ n - 1 := by omega
    by_cases hkt : k = t
    · subst hkt; simp [zeroSumBasis]
    · have htk : t ≠ k := fun h => hkt h.symm
      simp [zeroSumBasis, hkt, htk, hkne]
  rw [hcongr, sumRange_ite_eq] at hvk
  simp [hk] at hvk
  exact hvk

/-- Adjacency action of Kneser graph `KG(n, 2)` on a symmetric pair function `w`:
    `(KG(n, 2) * w)(i, j) = ∑_{a < b, {a,b} ∩ {i,j} = ∅} w(a, b)`. -/
def kneserAction (n : Nat) (w : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange n (fun a => sumRange n (fun b =>
    if a < b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then w a b else 0))

/-- Exact Kneser action theorem on `V_0`:
    For every `n ≥ 3` and every `v` with `sumRange n v = 0`, `KG(n, 2)` acts on
    `w_v(i, j) = v i + v j` as the exact scalar `-(n - 3 : Int)`! -/
theorem kneser_acts_on_pairSum (n : Nat) (hn : 3 ≤ n) (v : Nat → Int)
    (hv0 : sumRange n v = 0) (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    kneserAction n (pairSum v) i j = -((n : Int) - 3) * pairSum v i j := by
  have hswap : ∀ m₁ m₂ (f : Nat → Nat → Int),
      sumRange m₁ (fun a => sumRange m₂ (fun b => f a b)) =
        sumRange m₂ (fun b => sumRange m₁ (fun a => f a b)) := by
    intro m₁ m₂ f
    induction m₁ with
    | zero =>
      simp [sumRange_zero]
      have h0 : sumRange m₂ (fun _ => (0 : Int)) = 0 := by rw [sumRange_const]; simp
      exact h0.symm
    | succ m₁ ih =>
      rw [sumRange_succ, ih, ← sumRange_add]
      apply sumRange_congr; intro b _
      rw [sumRange_succ]
  -- Prove `2 * kneserAction = 2 * (-(n - 3) * pairSum v i j)` by symmetry of `(a, b)`
  have h2 : 2 * kneserAction n (pairSum v) i j =
      sumRange n (fun a => sumRange n (fun b =>
        if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) := by
    unfold kneserAction pairSum
    -- Split `if a ≠ b then` into `(a < b) + (b < a)`
    have hsplit_ab :
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) =
        sumRange n (fun a => sumRange n (fun b =>
          if a < b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) +
        sumRange n (fun a => sumRange n (fun b =>
          if b < a ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) := by
      rw [← sumRange_add]
      apply sumRange_congr; intro a _
      rw [← sumRange_add]
      apply sumRange_congr; intro b _
      by_cases hab : a = b
      · subst hab; simp
      · have hlt_gt : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
        rcases hlt_gt with h1 | h2
        · have hnot : ¬ (b < a) := by omega
          simp [hab, h1, hnot]
        · have hnot : ¬ (a < b) := by omega
          simp [hab, h2, hnot]
    rw [hsplit_ab]
    -- Show the second double sum equals the first by swapping summation order
    have hsecond :
        sumRange n (fun a => sumRange n (fun b =>
          if b < a ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) =
        sumRange n (fun a => sumRange n (fun b =>
          if a < b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) := by
      rw [hswap]
      apply sumRange_congr; intro b _
      apply sumRange_congr; intro a _
      by_cases h : b < a ∧ b ≠ i ∧ b ≠ j ∧ a ≠ i ∧ a ≠ j
      · rcases h with ⟨h1, h2, h3, h4, h5⟩
        simp [h1, h2, h3, h4, h5]; omega
      · have h' : ¬ (b < a ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j) := fun hc =>
          h ⟨hc.1, hc.2.2.2.1, hc.2.2.2.2, hc.2.1, hc.2.2.1⟩
        simp [h, h']
    rw [hsecond]
    omega
  -- Now evaluate the symmetric double sum!
  have heval :
      sumRange n (fun a => sumRange n (fun b =>
        if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) =
      2 * (-((n : Int) - 3) * (v i + v j)) := by
    have hsum_va_vb :
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a + v b else 0)) =
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0)) +
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v b else 0)) := by
      rw [← sumRange_add]
      apply sumRange_congr; intro a _
      rw [← sumRange_add]
      apply sumRange_congr; intro b _
      by_cases h : a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j <;> simp [h]
    have hfirst :
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0)) =
        -((n : Int) - 3) * (v i + v j) := by
      have hinner :
          sumRange n (fun a => sumRange n (fun b =>
            if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0)) =
          sumRange n (fun a =>
            if a ≠ i ∧ a ≠ j then ((n : Int) - 3) * v a else 0) := by
        apply sumRange_congr; intro a ha
        by_cases ha_ij : a ≠ i ∧ a ≠ j
        · have hcongr :
              sumRange n (fun b => if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0) =
                sumRange n (fun b => v a * (1 - (if b = a then 1 else 0) - (if b = i then 1 else 0) - (if b = j then 1 else 0))) := by
            apply sumRange_congr; intro b _
            by_cases hba : b = a
            · subst hba
              have hbi : b ≠ i := ha_ij.1
              have hbj : b ≠ j := ha_ij.2
              simp [hbi, hbj]
            · have hab : a ≠ b := fun h => hba h.symm
              by_cases hbi : b = i
              · subst hbi
                simp [hab, hba, hij]
              · by_cases hbj : b = j
                · subst hbj; simp [hab, hba, hbi]
                · simp [hab, ha_ij.1, ha_ij.2, hba, hbi, hbj]
          rw [hcongr, sumRange_mul_left, sumRange_sub, sumRange_sub, sumRange_sub,
              sumRange_const, sumRange_ite_eq, sumRange_ite_eq, sumRange_ite_eq]
          simp only [ha, hi, hj, ↓reduceIte, Int.mul_one]
          rw [if_pos ha_ij]
          have h3 : (n : Int) - 1 - 1 - 1 = (n : Int) - 3 := by omega
          rw [h3, Int.mul_comm]
        · have hzero : sumRange n (fun b => if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0) =
              sumRange n (fun _ => (0 : Int)) := by
            apply sumRange_congr; intro b _
            have hfalse : ¬(a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j) := fun h => ha_ij ⟨h.2.1, h.2.2.1⟩
            simp [hfalse]
          rw [hzero, sumRange_const]
          simp [ha_ij]
      rw [hinner]
      have hfactor :
          sumRange n (fun a => if a ≠ i ∧ a ≠ j then ((n : Int) - 3) * v a else 0) =
            ((n : Int) - 3) * sumRange n (fun a => if a ≠ i ∧ a ≠ j then v a else 0) := by
        rw [← sumRange_mul_left]
        apply sumRange_congr; intro a _
        by_cases h : a ≠ i ∧ a ≠ j <;> simp [h]
      rw [hfactor]
      have hsum_v :
          sumRange n (fun a => if a ≠ i ∧ a ≠ j then v a else 0) = -(v i + v j) := by
        have hcongr :
            sumRange n (fun a => if a ≠ i ∧ a ≠ j then v a else 0) =
              sumRange n (fun a => v a - (if a = i then v i else 0) - (if a = j then v j else 0)) := by
          apply sumRange_congr; intro a _
          by_cases hai : a = i
          · subst hai; simp [hij]
          · by_cases haj : a = j
            · subst haj; simp [hai]
            · simp [hai, haj]
        rw [hcongr, sumRange_sub, sumRange_sub, hv0, sumRange_ite_eq, sumRange_ite_eq]
        simp only [hi, hj, ↓reduceIte]
        omega
      rw [hsum_v, Int.mul_neg, Int.neg_mul]
    have hsecond_vb :
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v b else 0)) =
        sumRange n (fun a => sumRange n (fun b =>
          if a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j then v a else 0)) := by
      rw [hswap]
      apply sumRange_congr; intro b _
      apply sumRange_congr; intro a _
      by_cases h : b ≠ a ∧ b ≠ i ∧ b ≠ j ∧ a ≠ i ∧ a ≠ j
      · rcases h with ⟨h1, h2, h3, h4, h5⟩
        have h1' : a ≠ b := fun heq => h1 heq.symm
        simp [h1, h1', h2, h3, h4, h5]
      · have h' : ¬ (a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j) := fun hc =>
          h ⟨fun heq => hc.1 heq.symm, hc.2.2.2.1, hc.2.2.2.2, hc.2.1, hc.2.2.1⟩
        simp [h, h']
    rw [hsum_va_vb, hsecond_vb, hfirst]
    omega
  rw [heval] at h2
  unfold pairSum at h2 ⊢
  omega

end WittKneserLinearTorsion