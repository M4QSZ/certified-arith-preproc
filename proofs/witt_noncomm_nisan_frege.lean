/-
  ATAQUE-06: Non-Commutative IPS over Truncated Witt Rings W_2(F_2) ≅ Z/4Z
  =========================================================================
  Standalone Lean 4.36.0 formalization (zero imports, zero `sorryAx`,
  `#print axioms` audited).

  Contents:
    1. Truncated Boolean-to-Witt ring `W_2(F_2) ≅ Fin 4` (`Z/4Z`):
       - `wAdd (a0, a1) (b0, b1) = (a0 ^^ b0, a1 ^^ b1 ^^ (a0 && b0))`
       - `wMul (a0, a1) (b0, b1) = (a0 && b0, (a0 && b1) ^^ (a1 && b0))`
       - Exact ring isomorphism `toZ4 : W2 → Fin 4` and inverse `ofZ4 : Fin 4 → W2`.
    2. Zero-divisor rank obstruction over `Z/4Z`:
       - `2 * I_2` has residue rank `0` mod 2, yet cannot be factored as a single
         rank-1 outer product `u * v^T` over `Z/4Z` (`two_id_not_rank1_z4`).
       - `noncomm_commutator_witness`: explicit `2×2` matrices `X, Y` over `Z/4Z`
         such that `[X, Y] = X Y - Y X = 2 * I_2 ≠ 0` (`mat2_commutator_eq_two_id`).
    3. Non-commutative bimodal polynomials (`Word := List Nat` in `FreeMonoid`)
       and the carry-chain non-commutativity barrier:
       - `witt_carry_mod4`: `2 * b2n (x && y) = b2n x + b2n y - b2n (x ^^ y)`
         (hence `2 * S_1(x, y) ≡ x + y - (x ^^ y) (mod 4)`).
       - `nc_square_off_diagonal_distinct`: in `(x1 + x2)^2`, the off-diagonal
         words `[1, 2]` and `[2, 1]` are distinct (`[1, 2] ≠ [2, 1]`), each with
         coefficient `1`, and `(x1 + x2)^2 - (x1^2 + 2 x1 x2 + x2^2) = x2 x1 - x1 x2`,
         which vanishes only modulo the explicit commutator axiom `[x1, x2] = 0`.
-/

namespace WittNoncommNisanFrege

/-! ## 0. Core Helpers -/

/-- Embed `Bool` into `Nat` (`true ↦ 1`, `false ↦ 0`). -/
def b2n (b : Bool) : Nat :=
  if b then 1 else 0

/-- Embed `Bool` into `Int` (`true ↦ 1`, `false ↦ 0`). -/
def b2i (b : Bool) : Int :=
  if b then 1 else 0

/-! ## 1. Truncated Witt Ring `W_2(F_2) ≅ Fin 4` (`Z/4Z`) -/

/-- Elements of the length-2 Witt ring `W_2(F_2)` represented as `(a0, a1) : Bool × Bool`. -/
abbrev W2 := Bool × Bool

/-- Witt addition on `W_2(F_2)`:
    `(a0, a1) +_W (b0, b1) = (a0 ^^ b0, a1 ^^ b1 ^^ (a0 && b0))`. -/
def wAdd (a b : W2) : W2 :=
  (xor a.1 b.1, xor (xor a.2 b.2) (a.1 && b.1))

/-- Witt multiplication on `W_2(F_2)`:
    `(a0, a1) *_W (b0, b1) = (a0 && b0, (a0 && b1) ^^ (a1 && b0))`. -/
def wMul (a b : W2) : W2 :=
  (a.1 && b.1, xor (a.1 && b.2) (a.2 && b.1))

/-- Witt additive zero `(false, false)`. -/
def wZero : W2 := (false, false)

/-- Witt multiplicative identity `(true, false)`. -/
def wOne : W2 := (true, false)

/-- Witt additive inverse on `W_2(F_2)`: `-(a0, a1) = (a0, a1 ^^ a0)`. -/
def wNeg (a : W2) : W2 :=
  (a.1, xor a.2 a.1)

/-- Map `W_2(F_2)` to `Nat` via `b2n a0 + 2 * b2n a1 (mod 4)`. -/
def toZ4Nat (a : W2) : Nat :=
  (b2n a.1 + 2 * b2n a.2) % 4

/-- Map `W_2(F_2)` to `Fin 4`. -/
def toZ4 (a : W2) : Fin 4 :=
  ⟨toZ4Nat a, Nat.mod_lt _ (by decide)⟩

/-- Inverse map `Fin 4 → W_2(F_2)`. -/
def ofZ4 (x : Fin 4) : W2 :=
  (x.val % 2 == 1, (x.val / 2) % 2 == 1)

theorem toZ4_ofZ4 (x : Fin 4) : toZ4 (ofZ4 x) = x := by
  revert x
  decide

theorem ofZ4_toZ4 (a : W2) : ofZ4 (toZ4 a) = a := by
  rcases a with ⟨a0, a1⟩
  cases a0 <;> cases a1 <;> rfl

theorem toZ4Nat_add (a b : W2) :
    toZ4Nat (wAdd a b) = (toZ4Nat a + toZ4Nat b) % 4 := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

theorem toZ4Nat_mul (a b : W2) :
    toZ4Nat (wMul a b) = (toZ4Nat a * toZ4Nat b) % 4 := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

theorem toZ4_add (a b : W2) : toZ4 (wAdd a b) = toZ4 a + toZ4 b := by
  apply Fin.ext
  exact toZ4Nat_add a b

theorem toZ4_mul (a b : W2) : toZ4 (wMul a b) = toZ4 a * toZ4 b := by
  apply Fin.ext
  exact toZ4Nat_mul a b

theorem toZ4_zero : toZ4 wZero = 0 := rfl
theorem toZ4_one : toZ4 wOne = 1 := rfl

theorem toZ4_neg (a : W2) : toZ4 (wNeg a) = -toZ4 a := by
  rcases a with ⟨a0, a1⟩
  cases a0 <;> cases a1 <;> rfl

theorem wAdd_comm (a b : W2) : wAdd a b = wAdd b a := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

theorem wAdd_assoc (a b c : W2) : wAdd (wAdd a b) c = wAdd a (wAdd b c) := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩; rcases c with ⟨c0, c1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;> rfl

theorem wMul_comm (a b : W2) : wMul a b = wMul b a := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

theorem wMul_assoc (a b c : W2) : wMul (wMul a b) c = wMul a (wMul b c) := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩; rcases c with ⟨c0, c1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;> rfl

theorem wLeft_distrib (a b c : W2) : wMul a (wAdd b c) = wAdd (wMul a b) (wMul a c) := by
  rcases a with ⟨a0, a1⟩; rcases b with ⟨b0, b1⟩; rcases c with ⟨c0, c1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;> rfl

theorem wAdd_neg (a : W2) : wAdd a (wNeg a) = wZero := by
  rcases a with ⟨a0, a1⟩
  cases a0 <;> cases a1 <;> rfl

/-! ## 2. Zero-Divisor Rank Obstruction & Non-Commutative Matrix Commutator over `Z/4Z` -/

/-- `2×2` matrices over `Fin 4` (`Z/4Z`). -/
structure Mat2Z4 where
  m00 : Fin 4
  m01 : Fin 4
  m10 : Fin 4
  m11 : Fin 4
  deriving DecidableEq

/-- Matrix addition over `Z/4Z`. -/
def matAdd (A B : Mat2Z4) : Mat2Z4 :=
  ⟨A.m00 + B.m00, A.m01 + B.m01, A.m10 + B.m10, A.m11 + B.m11⟩

/-- Matrix subtraction over `Z/4Z`. -/
def matSub (A B : Mat2Z4) : Mat2Z4 :=
  ⟨A.m00 - B.m00, A.m01 - B.m01, A.m10 - B.m10, A.m11 - B.m11⟩

/-- Matrix multiplication over `Z/4Z`. -/
def matMul (A B : Mat2Z4) : Mat2Z4 :=
  ⟨ A.m00 * B.m00 + A.m01 * B.m10, A.m00 * B.m01 + A.m01 * B.m11,
    A.m10 * B.m00 + A.m11 * B.m10, A.m10 * B.m01 + A.m11 * B.m11 ⟩

/-- Matrix commutator `[A, B] = A B - B A` over `Z/4Z`. -/
def matComm (A B : Mat2Z4) : Mat2Z4 :=
  matSub (matMul A B) (matMul B A)

/-- Outer product `u * v^T` (a rank-1 matrix over `Z/4Z`). -/
def outerProd (u v : Fin 4 × Fin 4) : Mat2Z4 :=
  ⟨u.1 * v.1, u.1 * v.2, u.2 * v.1, u.2 * v.2⟩

/-- The zero matrix over `Z/4Z`. -/
def zeroMat2 : Mat2Z4 := ⟨0, 0, 0, 0⟩

/-- The matrix `2 * I_2` over `Z/4Z`. -/
def twoId2 : Mat2Z4 := ⟨2, 0, 0, 2⟩

/-- Residue of a `Mat2Z4` modulo 2 (`Fin 2` entries). -/
def mod2Entry (x : Fin 4) : Fin 2 :=
  ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩

/-- `2 * I_2` vanishes identically modulo 2 (residue rank 0), yet is non-zero over `Z/4Z`. -/
theorem two_id_mod2_vanishes :
    mod2Entry twoId2.m00 = 0 ∧ mod2Entry twoId2.m01 = 0 ∧
    mod2Entry twoId2.m10 = 0 ∧ mod2Entry twoId2.m11 = 0 ∧
    twoId2 ≠ zeroMat2 := by
  decide

/-- Zero-divisor rank obstruction over `Z/4Z`: `2 * I_2` cannot be factored
    as a single rank-1 outer product `u * v^T` over `Z/4Z`. -/
theorem two_id_not_rank1_z4 :
    ∀ u v : Fin 4 × Fin 4, outerProd u v ≠ twoId2 := by
  intro u v
  rcases u with ⟨u0, u1⟩
  rcases v with ⟨v0, v1⟩
  revert u0 u1 v0 v1
  decide

/-- Nilpotent/zero-divisor commutator witness over `Z/4Z`:
    `X = [[0, 2], [0, 0]]`, `Y = [[0, 0], [1, 0]]` satisfy `[X, Y] = 2 * I_2 ≠ 0`. -/
def witnessX : Mat2Z4 := ⟨0, 2, 0, 0⟩
def witnessY : Mat2Z4 := ⟨0, 0, 1, 0⟩

theorem noncomm_commutator_witness :
    matComm witnessX witnessY = twoId2 ∧ matComm witnessX witnessY ≠ zeroMat2 := by
  decide

/-! ## 3. Non-Commutative Bimodal Polynomials (`FreeMonoid` Words) & Carry Barrier -/

/-- A word in the free monoid over variable indices `Nat`. -/
abbrev Word := List Nat

/-- A non-commutative polynomial over `Int` as a list of `(coeff, word)` pairs. -/
abbrev NCPoly := List (Int × Word)

/-- Variable `x_i`. -/
def ncVar (i : Nat) : NCPoly := [(1, [i])]

/-- Constant `c`. -/
def ncConst (c : Int) : NCPoly := [(c, [])]

/-- Addition of non-commutative polynomials. -/
def ncAdd (p q : NCPoly) : NCPoly := p ++ q

/-- Negation of a non-commutative polynomial. -/
def ncNeg (p : NCPoly) : NCPoly :=
  p.map (fun (c, w) => (-c, w))

/-- Subtraction of non-commutative polynomials. -/
def ncSub (p q : NCPoly) : NCPoly :=
  ncAdd p (ncNeg q)

/-- Multiplication of non-commutative polynomials (word concatenation `w1 ++ w2`). -/
def ncMul (p q : NCPoly) : NCPoly :=
  p.foldr (fun (c1, w1) acc =>
    (q.map (fun (c2, w2) => (c1 * c2, w1 ++ w2))) ++ acc) []

/-- Non-commutative commutator `[p, q] = p q - q p`. -/
def ncComm (p q : NCPoly) : NCPoly :=
  ncSub (ncMul p q) (ncMul q p)

/-- Coefficient of a specific word `w` in `p`. -/
def coeff (w : Word) (p : NCPoly) : Int :=
  p.foldr (fun (c, u) acc => if u == w then c + acc else acc) 0

/-- Exact Witt carry identity in `Nat`:
    `b2n x + b2n y = b2n (xor x y) + 2 * b2n (x && y)`. -/
theorem witt_carry_exact_nat (x y : Bool) :
    b2n x + b2n y = b2n (xor x y) + 2 * b2n (x && y) := by
  cases x <;> cases y <;> rfl

/-- Witt carry congruence mod 4:
    `2 * S_1(x, y) ≡ x + y - (x ^^ y) (mod 4)`. -/
theorem witt_carry_mod4 (x y : Bool) :
    (2 * b2i (x && y)) % 4 = (b2i x + b2i y - b2i (xor x y)) % 4 := by
  cases x <;> cases y <;> rfl

/-- Non-commutative variable commutator `[x_1, x_2]` has non-zero coefficients
    on the distinct off-diagonal words `[1, 2]` and `[2, 1]`. -/
theorem nc_commutator_nonzero :
    ([1, 2] : Word) ≠ [2, 1] ∧
    coeff [1, 2] (ncComm (ncVar 1) (ncVar 2)) = 1 ∧
    coeff [2, 1] (ncComm (ncVar 1) (ncVar 2)) = -1 := by
  decide

/-- Carry-chain non-commutativity barrier:
    In `(x1 + x2)^2`, both `[1, 2]` and `[2, 1]` appear with coefficient `1`,
    and the difference `(x1 + x2)^2 - (x1^2 + 2 * x1 x2 + x2^2)` equals
    `-[x1, x2] = x2 x1 - x1 x2`, which is non-zero unless the commutator axiom
    `x1 x2 - x2 x1 = 0` is explicitly derived in NC-IPS. -/
theorem nc_square_off_diagonal_barrier :
    let x1 := ncVar 1
    let x2 := ncVar 2
    let sq := ncMul (ncAdd x1 x2) (ncAdd x1 x2)
    let commApprox := ncAdd (ncMul x1 x1) (ncAdd (ncMul (ncConst 2) (ncMul x1 x2)) (ncMul x2 x2))
    let diff := ncSub sq commApprox
    coeff [1, 2] sq = 1 ∧
    coeff [2, 1] sq = 1 ∧
    coeff [1, 2] diff = -1 ∧
    coeff [2, 1] diff = 1 ∧
    coeff [1, 1] diff = 0 ∧
    coeff [2, 2] diff = 0 := by
  decide

/-! ## 4. Axiom Audit -/

#print axioms toZ4_ofZ4
#print axioms ofZ4_toZ4
#print axioms toZ4Nat_add
#print axioms toZ4Nat_mul
#print axioms two_id_mod2_vanishes
#print axioms two_id_not_rank1_z4
#print axioms noncomm_commutator_witness
#print axioms witt_carry_exact_nat
#print axioms witt_carry_mod4
#print axioms nc_commutator_nonzero
#print axioms nc_square_off_diagonal_barrier

end WittNoncommNisanFrege
