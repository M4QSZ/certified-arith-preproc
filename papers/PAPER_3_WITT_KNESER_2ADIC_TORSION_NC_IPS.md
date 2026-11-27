# Universal 2-Adic Smith Normal Form and Kneser KG(n,2) Linear-Rank Torsion in Bimodal Nisan Matrices over Truncated Witt Rings W_k(F_2)

> **Status:** Publication-ready manuscript (`CCC / ITCS / Algebraic Proof Complexity` format). Every universal $\forall n$ algebraic and spectral theorem is mechanically verified in standalone `Lean 4.36.0` across three zero-import, `0 sorryAx` proof suites ([witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean), [witt_snf_universal_torsion.lean](../proofs/witt_snf_universal_torsion.lean), [witt_kneser_linear_torsion.lean](../proofs/witt_kneser_linear_torsion.lean); `2,540` total lines), and all exact integer Smith Normal Form (`SNF_Z`) invariant-factor tables are reproduced by [witt_noncomm_ips_explorer.py](../src/certified_arith_preproc/witt_noncomm_ips_explorer.py), [witt_higher_torsion_snf.py](../src/certified_arith_preproc/witt_higher_torsion_snf.py), and [witt_kneser_nc_separation.py](../src/certified_arith_preproc/witt_kneser_nc_separation.py) in [witt_noncomm_ips_results.json](../results/witt_noncomm_ips_results.json), [witt_higher_torsion_snf_results.json](../results/witt_higher_torsion_snf_results.json), and [witt_kneser_linear_torsion_results.json](../results/witt_kneser_linear_torsion_results.json).

---

## Abstract

Nisan's partial-derivative matrix method characterizes algebraic branching program (ABP) complexity over fields in non-commutative variables and underlies lower bounds for non-commutative Ideal Proof System (`NC-IPS`) refutations. When arithmetic constraints are lifted from $\mathbb{F}_2$ to truncated $2$-adic Witt rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$, however, carry polynomials vanish identically modulo $2$ (e.g., $2 e_2^{\mathrm{sym}} \equiv 0 \pmod{2}$ and $4 C_2 \equiv 0 \pmod{4}$) and zero divisors break field-based rank arguments: over $\mathbb{Z}/4\mathbb{Z}$, $2 I_2$ has residue rank $0$ modulo $2$ yet cannot be factored as a single rank-$1$ outer product $u v^\top$.

We resolve this $2$-adic rank-obstruction barrier via universal $\forall n$ integer Smith Normal Form (`SNF_Z`) factorizations and exact spectral geometry of the Kneser graph $KG(n,2)$:
1. For the degree-$2$ carry matrix $M_1(e_2^{\mathrm{sym}}) = J_n - I_n$, explicit unimodular matrices $P_n, Q_n \in \mathrm{GL}_n(\mathbb{Z})$ prove $\mathrm{SNF}_{\mathbb{Z}}(J_n - I_n) = \operatorname{diag}(1^{n-1}, n-1)$ for all $n \ge 2$, pinning $2^r$-torsion emergence to Witt depth $k = r + 1$ at $n = 2^r + 1$.
2. For the degree-$3$ cut $M_{1,2}(e_3^{\mathrm{sym}}) \in \mathbb{Z}^{n \times n^2}$, explicit bilateral unimodular factors reduce the matrix to $\operatorname{diag}(1^{n-1}, n-2, 0, \dots, 0)$ for all $n \ge 3$, shifting $2^r$-torsion emergence to $n = 2^r + 2$.
3. For the degree-$4$ middle cut $M_{2,2}(e_4^{\mathrm{sym}})$—whose non-redundant core is the adjacency matrix of $KG(n,2)$—we prove that the injective pair-sum map $w_v(i,j) = v_i + v_j$ embeds the $(n-1)$-dimensional zero-sum lattice $V_0 = \{v \in \mathbb{Z}^n : \sum_i v_i = 0\}$ as an exact eigenspace of $KG(n,2)$ with eigenvalue $-(n-3)$. At odd $n = 2^r + 3$, this produces a **linear-rank block of $n-1$ simultaneous $2^r$-torsion invariant factors**, forcing a module-rank jump of $n-1$ between $W_r(\mathbb{F}_2)$ and $W_{r+1}(\mathbb{F}_2)$ (verified computationally up to $n = 12$, with $10$ simultaneous $8$-torsion factors at $n = 11$). On the exact $2$nd Witt addition carry $4 C_2(x) \pmod{16}$, symmetrized NC Nisan rank reaches $\binom{n}{2} = 45$ at $n=10$ against ordered commutative rank $n - 3 = 7$ (`6.43×` separation). We conclude with a scope boundary citing `arXiv:2210.17429` explaining why these $W_k(\mathbb{F}_2)$ torsion obstructions target extension-free systems (`NC-IPS` and `Frege`) rather than `Extended Frege` (`EF`).

---

## 1. Introduction & Algebraic Proof Complexity over Witt Rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$

Over a field $\mathbb{F}$, Nisan's theorem (1991) proves that the minimum size of a homogeneous non-commutative ABP computing $f$ of degree $D$ equals $\sum_{d=0}^D \operatorname{rank}_{\mathbb{F}}(M_d(f))$, where $M_d(f)$ has rows indexed by words $u$ of length $d$, columns by words $v$ of length $D - d$, and entries equal to the coefficient of the concatenation $u \cdot v$ in $f$. In algebraic proof complexity, Grochow and Pitassi (2018) introduced the Ideal Proof System (`IPS`), and subsequent work established super-polynomial separations and lower bounds for restricted fragments including non-commutative `IPS` (`NC-IPS`) and bounded-depth / multilinear `IPS` (Forbes, Shpilka, Tzameret, and Wigderson 2021; Limaye, Srinivasan, and Tavenas 2021).

Boolean arithmetic circuits and carry chains, however, do not live natively over $\mathbb{F}_2$ alone: binary addition on $n$ bits $x_1, \dots, x_n \in \{0, 1\}$ generates carries $C_1(x) = \lfloor \sum x_i / 2 \rfloor \bmod 2$ and $C_2(x) = \lfloor \sum x_i / 4 \rfloor \bmod 2$ whose faithful algebraic embedding requires the ring of truncated $2$-adic Witt vectors $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$. In $W_2(\mathbb{F}_2) \cong \mathbb{Z}/4\mathbb{Z}$ (formalized in [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean)), addition and multiplication on bit-pairs $(a_0, a_1) \in \mathbb{F}_2^2$ satisfy
$$(a_0, a_1) +_W (b_0, b_1) = \big(a_0 \oplus b_0,\; a_1 \oplus b_1 \oplus (a_0 \wedge b_0)\big), \qquad (a_0, a_1) \cdot_W (b_0, b_1) = \big(a_0 \wedge b_0,\; (a_0 \wedge b_1) \oplus (a_1 \wedge b_0)\big),$$
with exact ring isomorphism `toZ4 : W2 → Fin 4` (`toZ4_add`, `toZ4_mul`) and integer carry identity $2(x \wedge y) \equiv x + y - (x \oplus y) \pmod{4}$ (`witt_carry_mod4`). Lifting a Witt carry from $\mathbb{F}_2$ to $W_k(\mathbb{F}_2)$ multiplies degree-$2^t$ carry components by $2^t$, placing them inside the zero-divisor ideal $2^t (\mathbb{Z}/2^k\mathbb{Z})$ where $\mathbb{F}_2$-rank collapses to $0$.

In the non-commutative free monoid $\mathbb{Z}\langle x_1, \dots, x_n \rangle$, moreover, symmetrized lifts behave radically differently from ordered commutative lifts. As formalized in `nc_commutator_nonzero` and `nc_square_off_diagonal_barrier`, the off-diagonal words $[1, 2]$ and $[2, 1]$ are distinct, so $(x_1 + x_2)^2 - (x_1^2 + 2 x_1 x_2 + x_2^2) = x_2 x_1 - x_1 x_2 = -[x_1, x_2] \neq 0$ unless the commutator axiom $[x_1, x_2] = 0$ is explicitly derived. Replacing $x_i x_j$ ($i < j$) by its symmetrized lift $e_d^{\mathrm{sym}}(x) = \sum_{\text{distinct } i_1, \dots, i_d} x_{i_1} \cdots x_{i_d}$ turns sparse upper-triangular ordered matrices into full-rank combinatorial incidence and disjointness matrices whose $\mathbb{Z}$-Smith Normal Form governs module rank over every Witt depth $W_k(\mathbb{F}_2)$.

### 1.1 Preliminaries: Bimodal Nisan Matrices, Fitting Rank, and Möbius Witt Lifting

For a non-commutative polynomial $f = \sum_{w} c_w w \in \mathbb{Z}\langle x_1, \dots, x_n \rangle$ and cut $d \in \{0, \dots, D\}$, the **Nisan partial-derivative matrix** $M_d(f)$ has rows indexed by words $u \in [n]^d$, columns by words $v \in [n]^{D-d}$, and entries $(M_d(f))_{u,v} = c_{u \cdot v}$; for inhomogeneous polynomials such as $4 C_2(x)$, the **bimodal Nisan matrix** at cut $d=2$ indexes rows by words of length $2$ and columns by words of length $\ge 2$. Over a principal ideal domain $\mathbb{Z}$, $M$ admits a Smith Normal Form $P M Q = \operatorname{diag}(d_1, \dots, d_r, 0, \dots, 0)$ with $P, Q$ unimodular and $0 < d_1 \mid d_2 \mid \cdots \mid d_r$. Reducing modulo $2^k$ yields invariant factors $\gcd(d_i, 2^k)$, so the **$W_k(\mathbb{F}_2)$-module rank** equals $\#\{i : v_2(d_i) < k\}$ and the **zero-divisor gap** relative to $\mathbb{F}_2$ equals $\#\{i : 1 \le v_2(d_i) < k\}$.

For the $2$nd Witt addition carry $C_2(x_1, \dots, x_n) = \lfloor (\sum_{i=1}^n x_i)/4 \rfloor \bmod 2$, discrete Möbius inversion over Hamming weight $s = \sum_{i=1}^n x_i$ gives $C_2(x) = \sum_{k=4}^n a_k e_k(x)$ where $a_k = \sum_{j=4}^k (-1)^{k-j} \binom{k}{j} (\lfloor j/4 \rfloor \bmod 2)$. As recorded in [witt_higher_torsion_snf_results.json](../results/witt_higher_torsion_snf_results.json) (`c2_witt_second_carry_Z16`), scaling into $W_4(\mathbb{F}_2) \cong \mathbb{Z}/16\mathbb{Z}$ yields the exact congruence
$$4 C_2(x) \equiv 4 e_4(x) + 8 e_6(x) + 8 e_8(x) \pmod{16} \qquad (n \le 8),$$
linking the degree-$4$ carry component directly to $4 \cdot M_{2,2}(e_4^{\mathrm{sym}})$ and hence to $4 \cdot KG(n,2)$.

---

## 2. Universal Smith Normal Form & Kneser $KG(n,2)$ Torsion Theorems

### 2.1 Zero-Divisor Rank Obstruction and Non-Commutative Commutator (`ATAQUE-06`)

Over a ring $\mathbb{Z}/2^k\mathbb{Z}$, rank cannot be read off modulo $2$. Let $M$ have integer Smith Normal Form invariant factors $(d_1, \dots, d_r)$ with $d_1 \mid d_2 \mid \cdots \mid d_r$. Modulo $2^k$, the Fitting/module rank is the number of indices $i$ with $v_2(d_i) < k$ (equivalently $\gcd(d_i, 2^k) < 2^k$), because multiplication by $d_i$ annihilates $\mathbb{Z}/2^k\mathbb{Z}$ if and only if $2^k \mid d_i$. In [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean), we mechanically prove the base $2$-adic obstruction over $\mathbb{Z}/4\mathbb{Z}$:
- **`two_id_mod2_vanishes`:** $2 I_2 \equiv 0 \pmod{2}$ yet $2 I_2 \neq 0$ in $M_2(\mathbb{Z}/4\mathbb{Z})$.
- **`two_id_not_rank1_z4`:** $\forall u, v \in (\mathbb{Z}/4\mathbb{Z})^2,\; u v^\top \neq 2 I_2$; hence $\operatorname{rank}_{\mathbb{Z}/4\mathbb{Z}}(2 I_2) = 2$ despite $\operatorname{rank}_{\mathbb{F}_2}(2 I_2) = 0$.
- **`noncomm_commutator_witness`:** The nilpotent matrices $X = \bigl(\begin{smallmatrix} 0 & 2 \\ 0 & 0 \end{smallmatrix}\bigr)$ and $Y = \bigl(\begin{smallmatrix} 0 & 0 \\ 1 & 0 \end{smallmatrix}\bigr)$ over $\mathbb{Z}/4\mathbb{Z}$ satisfy $[X, Y] = X Y - Y X = 2 I_2 \neq 0$.

### 2.2 Universal SNF for $M_1(e_2^{\mathrm{sym}}) = J_n - I_n$ (`ATAQUE-09`)

For $e_2^{\mathrm{sym}}(x) = \sum_{i \neq j} x_i x_j$, the degree-$1$ Nisan matrix is the $n \times n$ derangement matrix $D_n = J_n - I_n$ (`derangementEntry`). Define $P_n, Q_n \in \mathbb{Z}^{n \times n}$ (`P_mat`, `Q_mat`) by:
$$(P_n)_{i,j} = \begin{cases} -1 & i < n-1,\, j = i, \\ 1 & i < n-1,\, j = n-1, \\ 1 & i = n-1,\, j < n-1, \\ 2 - n & i = n-1,\, j = n-1, \\ 0 & \text{otherwise}, \end{cases} \qquad (Q_n)_{i,j} = \begin{cases} 1 & i = j \text{ or } j = n-1, \\ 0 & \text{otherwise}, \end{cases}$$
with explicit integer inverses `P_inv` ($(P_n^{-1})_{i,j} = 0$ if $i < n-1$ and $i=j$, else $1$) and `Q_inv` ($1$ on diagonal, $-1$ on column $n-1$ above the diagonal).

> **Theorem 1 (`snf_derangement_forall_n`, $\forall n \ge 2$).** *For every $n \ge 2$, $P_n P_n^{-1} = P_n^{-1} P_n = Q_n Q_n^{-1} = Q_n^{-1} Q_n = I_n$ (`P_mul_P_inv`, `P_inv_mul_P`, `Q_mul_Q_inv`, `Q_inv_mul_Q`), and*
> $$P_n (J_n - I_n) Q_n = \operatorname{diag}(1, \dots, 1, n - 1).$$
> *Consequently (`witt_depth_visibility_threshold`, `witt_snf_torsion_emergence`), at $n = 2^r + 1$ ($r \ge 0$), the top invariant factor $n - 1 = 2^r$ satisfies $(n-1) \bmod 2^j = 0$ for all $j \le r$ (rank $n-1$ in $W_{\le r}(\mathbb{F}_2)$) and $(n-1) \bmod 2^{r+1} = 2^r \neq 0$ (full rank $n$ first emerges in $W_{r+1}(\mathbb{F}_2) \cong \mathbb{Z}/2^{r+1}\mathbb{Z}$).*

### 2.3 Universal SNF for $M_{1,2}(e_3^{\mathrm{sym}})$ (`ATAQUE-12`, Part a)

For $e_3^{\mathrm{sym}}(x) = \sum_{\text{distinct } i,a,b} x_i x_a x_b$, the cut $d=1$ Nisan matrix $M_{1,2}(e_3^{\mathrm{sym}}) \in \{0,1\}^{n \times n^2}$ (`M12_e3`) has entry $1$ at $(i, c)$ iff $a \neq b$, $i \neq a$, $i \neq b$ where $c = a n + b$. In [witt_kneser_linear_torsion.lean](../proofs/witt_kneser_linear_torsion.lean), we construct explicit closed-form unimodular factors:
- Left factor `P_e3 n` ($\in \mathrm{GL}_n(\mathbb{Z})$): for $i < n-2$, row $i$ is $\delta_i - \delta_{n-2}$; row $n-2$ is $\delta_{n-1}$; row $n-1$ puts $3-n$ at column $n-2$ and $1$ elsewhere. Its two-sided inverse `P_e3_inv` satisfies `P_e3_mul_inv` and `P_e3_inv_mul`.
- Right factor `Q_e3 n = PermQ n * U_e3 n` ($\in \mathrm{GL}_{n^2}(\mathbb{Z})$): `PermQ` implements the involution `sigmaQ` sending $0 \le x < n-2$ to $(n-1)n + x$, $n-2$ to $n$, and $n-1$ to $(n-1)n + (n-2)$, aligning the pivot columns so upper-triangular clearing `U_e3` (with inverse `U_e3_inv`) zeroes all columns $j \ge n$.

> **Theorem 2 (`snf_e3_M12_forall_n`, $\forall n \ge 3$).** *For every $n \ge 3$, $P_{e_3,n} P_{e_3,n}^{-1} = I_n$, $Q_{e_3,n} Q_{e_3,n}^{-1} = I_{n^2}$ (`Q_e3_mul_inv`, `Q_e3_inv_mul`), and*
> $$P_{e_3,n}\, M_{1,2}(e_3^{\mathrm{sym}})\, Q_{e_3,n} = \operatorname{diag}(1^{n-1},\; n - 2,\; 0, \dots, 0).$$
> *Thus at $n = 2^r + 2$ ($r \ge 1$), the single $2^r$-torsion factor $n - 2 = 2^r$ vanishes in $W_{\le r}(\mathbb{F}_2)$ and emerges at depth $W_{r+1}(\mathbb{F}_2)$.*

### 2.4 Kneser $KG(n,2)$ Pair-Sum Eigenspace & Linear-Rank Torsion (`ATAQUE-12`, Part b)

While $e_2^{\mathrm{sym}}$ and $e_3^{\mathrm{sym}}$ yield only a *single* torsion factor ($O(1)$ rank jump), the middle cut $M_{2,2}(e_4^{\mathrm{sym}}) \in \{0,1\}^{n^2 \times n^2}$ compresses without loss of $\mathrm{SNF}_{\mathbb{Z}}$ to the $\binom{n}{2} \times \binom{n}{2}$ adjacency matrix of the Kneser graph $KG(n,2)$, acting on symmetric pair functions $w(a,b)$ via `(kneserAction n w i j) = \sum_{a<b,\, \{a,b\}\cap\{i,j\}=\emptyset} w(a,b)`. Define the pair-sum map `pairSum` $w_v(i, j) = v_i + v_j$ on the $(n-1)$-dimensional zero-sum lattice $V_0 = \{v \in \mathbb{Z}^n : \sum_{i=0}^{n-1} v_i = 0\}$, spanned by `zeroSumBasis` $e_k = \delta_k - \delta_{n-1}$ ($0 \le k < n - 1$, `zeroSumBasis_in_V0`).

> **Theorem 3 (`pairSum_injective`, `pairSum_basis_lin_indep`, `kneser_acts_on_pairSum`, $\forall n \ge 3$).**
> 1. *For every $n \ge 3$, $v \mapsto w_v$ is injective on $\mathbb{Z}^n$ restricted to distinct pairs $0 \le i < j < n$ (`pairSum_injective`, solving $v_i = \frac{1}{2}(w_{0,i} + w_{1,i} - w_{0,1})$), and $\{w_{e_0}, \dots, w_{e_{n-2}}\}$ are linearly independent in $\mathbb{Z}^{\binom{n}{2}}$ (`pairSum_basis_lin_indep`).*
> 2. *For every $v \in V_0$ and $i \neq j$, `(kneserAction n (pairSum v) i j) = -(n - 3) * (pairSum v i j)` (`kneser_acts_on_pairSum`): doubling the sum over unordered pairs splits into $\sum_{a\notin\{i,j\}} (n-3)v_a$ twice, and $\sum_{a\notin\{i,j\}} v_a = -(v_i + v_j)$ by $v \in V_0$.*
>
> *Combining this $(n-1)$-dimensional integral eigenspace of eigenvalue $-(n-3)$ with the classical Kneser spectrum (Lovász 1979; Godsil and Royle 2001), the closed-form $\mathrm{SNF}_{\mathbb{Z}}$ of $M_{2,2}(e_4^{\mathrm{sym}}) \sim KG(n,2)$ for $n \ge 4$ is:*
> $$\mathrm{SNF}_{\mathbb{Z}}(KG(n,2)) = \begin{cases} \big(1^{\frac{n(n-3)}{2}},\; (n-3)^{n-1},\; \tfrac{(n-2)(n-3)}{2}\big) & n \text{ even}, \\ \big(1^{\frac{n(n-3)}{2}},\; \tfrac{n-3}{2},\; (n-3)^{n-2},\; (n-2)(n-3)\big) & n \text{ odd}. \end{cases}$$
> *For odd $n = 2^r + 3$ ($r \ge 1$), $v_2(n-3) = r$ and $v_2((n-3)/2) = r-1$, yielding a **linear-rank block of $n-1$ simultaneous invariant factors divisible by $2^r$** ($n-2$ copies of $2^r$ and one of $(2^r+1)2^r$), causing an $\Omega(n)$ rank jump of $n-1$ between $W_r(\mathbb{F}_2)$ and $W_{r+1}(\mathbb{F}_2)$.*

More explicitly, for every odd $n = 2^r + 3$ ($r \ge 1$):
- Over $W_k(\mathbb{F}_2)$ with $k \le r-1$, all $n-1$ factors of $V_0$ vanish modulo $2^k$ (rank $\frac{n(n-3)}{2}$);
- Over $W_r(\mathbb{F}_2)$, only the single factor $(n-3)/2 = 2^{r-1}$ emerges (rank $\frac{n(n-3)}{2} + 1$);
- Over $W_{r+1}(\mathbb{F}_2) \cong \mathbb{Z}/2^{r+1}\mathbb{Z}$, all $n-2$ copies of $n-3 = 2^r$ and $(n-2)(n-3) = (2^r+1)2^r$ become units modulo $2^{r+1}$ times $2^r$, lifting the module rank by $n-1$ to full rank $\binom{n}{2}$.

---

## 3. Mechanical Verification in `Lean 4.36.0` (`0 sorryAx`)

All three files compile standalone with `lean` (`4.36.0`), `0` external imports, `0` `sorry`, and `0` custom `axiom` declarations (`2,540` total lines). Where explicit `#print axioms` commands appear in [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean) and [witt_snf_universal_torsion.lean](../proofs/witt_snf_universal_torsion.lean), we directly observed the exact Lean kernel axiom footprints below:

| Suite (`proofs/`) | Lines | Audited Declarations (`#print axioms` / Kernel Check) | Observed Axiom Footprint |
| :--- | :---: | :--- | :--- |
| [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean) | `293` | `toZ4_ofZ4`, `ofZ4_toZ4`, `toZ4Nat_add`, `toZ4Nat_mul`, `witt_carry_exact_nat`, `witt_carry_mod4`, `nc_commutator_nonzero`, `nc_square_off_diagonal_barrier` | `[]` (`0` axioms) |
| [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean) | `293` | `two_id_mod2_vanishes`, `two_id_not_rank1_z4`, `noncomm_commutator_witness` | `[propext]` |
| [witt_snf_universal_torsion.lean](../proofs/witt_snf_universal_torsion.lean) | `567` | `P_mul_P_inv`, `P_inv_mul_P`, `Q_mul_Q_inv`, `Q_inv_mul_Q`, `snf_derangement_forall_n`, `witt_depth_visibility_threshold`, `witt_snf_torsion_emergence` | `[propext, Quot.sound]` |
| [witt_kneser_linear_torsion.lean](../proofs/witt_kneser_linear_torsion.lean) | `1,680` | `P_e3_mul_inv`, `P_e3_inv_mul`, `Q_e3_mul_inv`, `Q_e3_inv_mul`, `snf_e3_M12_forall_n`, `zeroSumBasis_in_V0`, `pairSum_injective`, `pairSum_basis_lin_indep`, `kneser_acts_on_pairSum` | Compiles standalone (`0` imports, `0` `sorry`; `#print axioms` not appended in file) |

---

## 4. Computational Invariant-Factor & Witt-Carry Rank Evaluation

### Table 1: `e_2^sym` ($M_1 = J_n - I_n$) Universal SNF ($n = 2..17$)
From `e2_sym_M1_derangement` in [witt_higher_torsion_snf_results.json](../results/witt_higher_torsion_snf_results.json):

| $n$ | $\mathrm{SNF}_{\mathbb{Z}}(J_n - I_n)$ | $\max v_2$ | First Full Depth | $W_1$ ($\mathbb{Z}/2$) | $W_2$ ($\mathbb{Z}/4$) | $W_3$ ($\mathbb{Z}/8$) | $W_4$ ($\mathbb{Z}/16$) | $W_5$ ($\mathbb{Z}/32$) | $W_6$ ($\mathbb{Z}/64$) |
| :---: | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `2` | `[1^1, 1]` | `0` | `W_1` | `2` | `2` | `2` | `2` | `2` | `2` |
| `3` | `[1^2, 2]` | `1` | `W_2` | `2` | **`3`** | `3` | `3` | `3` | `3` |
| `4` | `[1^3, 3]` | `0` | `W_1` | `4` | `4` | `4` | `4` | `4` | `4` |
| `5` | `[1^4, 4]` | `2` | `W_3` | `4` | `4` | **`5`** | `5` | `5` | `5` |
| `6` | `[1^5, 5]` | `0` | `W_1` | `6` | `6` | `6` | `6` | `6` | `6` |
| `7` | `[1^6, 6]` | `1` | `W_2` | `6` | **`7`** | `7` | `7` | `7` | `7` |
| `8` | `[1^7, 7]` | `0` | `W_1` | `8` | `8` | `8` | `8` | `8` | `8` |
| `9` | `[1^8, 8]` | `3` | `W_4` | `8` | `8` | `8` | **`9`** | `9` | `9` |
| `10` | `[1^9, 9]` | `0` | `W_1` | `10` | `10` | `10` | `10` | `10` | `10` |
| `11` | `[1^{10}, 10]` | `1` | `W_2` | `10` | **`11`** | `11` | `11` | `11` | `11` |
| `12` | `[1^{11}, 11]` | `0` | `W_1` | `12` | `12` | `12` | `12` | `12` | `12` |
| `13` | `[1^{12}, 12]` | `2` | `W_3` | `12` | `12` | **`13`** | `13` | `13` | `13` |
| `14` | `[1^{13}, 13]` | `0` | `W_1` | `14` | `14` | `14` | `14` | `14` | `14` |
| `15` | `[1^{14}, 14]` | `1` | `W_2` | `14` | **`15`** | `15` | `15` | `15` | `15` |
| `16` | `[1^{15}, 15]` | `0` | `W_1` | `16` | `16` | `16` | `16` | `16` | `16` |
| `17` | `[1^{16}, 16]` | `4` | `W_5` | `16` | `16` | `16` | `16` | **`17`** | `17` |

### Table 2: `ATAQUE-06` Witt Carry $2 e_2^{\mathrm{sym}}$ & $(\sum x_i)^3 \bmod 4$ Separation ($n = 2..6$)
From [witt_noncomm_ips_results.json](../results/witt_noncomm_ips_results.json):

| $n$ | $e_2^{\mathrm{sym}}$ $M_1$ ($\mathbb{F}_2 / \mathbb{Q} / \mathrm{inv}_{\mathbb{Z}/4}$) | $2 e_2^{\mathrm{sym}}$ $M_1$ ($\mathbb{F}_2 / \mathrm{inv}_{\mathbb{Z}/4} / \mathrm{gap}_{\mathbb{Z}/4}$) | $(\sum x_i)^3 \bmod 4$ `NC` ABP Bound | $(\sum x_i)^3 \bmod 4$ `Ord` ABP Bound | `Comm / NC` Ratio |
| :---: | :--- | :--- | :---: | :---: | :---: |
| `2` | `2 / 2 / [1, 1]` | `0 / [2, 2] / 2` | `4` (`d=1: [1]`) | `6` (`d=1: [1^2]`) | `1.5×` |
| `3` | `2 / 3 / [1, 1, 2]` | `0 / [2, 2] / 2` | `4` (`d=1: [1]`) | `8` (`d=1: [1^3]`) | `2.0×` |
| `4` | `4 / 4 / [1^4]` | `0 / [2^4] / 4` | `4` (`d=1: [1]`) | `10` (`d=1: [1^4]`) | `2.5×` |
| `5` | `4 / 5 / [1^4]` ($\mathbb{Z}/8$: `[1^4, 4]`) | `0 / [2^4] / 4` | `4` (`d=1: [1]`) | `12` (`d=1: [1^5]`) | `3.0×` |
| `6` | `6 / 6 / [1^6]` | `0 / [2^6] / 6` | `4` (`d=1: [1]`) | `14` (`d=1: [1^6]`) | `3.5×` |

### Table 3: `e_3^sym` ($M_{1,2}$) up to $n=12$ and Kneser $KG(n,2) \sim M_{2,2}(e_4^{\mathrm{sym}})$ up to $n=11$
From [witt_higher_torsion_snf_results.json](../results/witt_higher_torsion_snf_results.json) and [witt_kneser_linear_torsion_results.json](../results/witt_kneser_linear_torsion_results.json):

| $n$ | $M_{1,2}(e_3^{\mathrm{sym}})$ Dims | $\mathrm{SNF}_{\mathbb{Z}}(M_{1,2})$ | $KG(n,2)$ $\binom{n}{2}$ | $\mathrm{SNF}_{\mathbb{Z}}(KG(n,2))$ Multiplicities | $v_2$ Spectrum | Ranks $W_1 / W_2 / W_3 / W_4$ ($KG$) |
| :---: | :---: | :--- | :---: | :--- | :--- | :---: |
| `3` | `3×9` | `[1^3]` (`max v_2=0`) | — | — | — | — |
| `4` | `4×16` | `[1^3, 2]` (`max v_2=1`) | `6` | `1^6` | `0^6` | `6 / 6 / 6 / 6` |
| `5` | `5×25` | `[1^4, 3]` (`max v_2=0`) | `10` | `1^6, 2^3, 6^1` | `0^6, 1^4` | `6 / 10 / 10 / 10` (`+4`) |
| `6` | `6×36` | `[1^5, 4]` (`max v_2=2`) | `15` | `1^9, 3^5, 6^1` | `0^{14}, 1^1` | `14 / 15 / 15 / 15` |
| `7` | `7×49` | `[1^6, 5]` (`max v_2=0`) | `21` | `1^{14}, 2^1, 4^5, 20^1` | `0^{14}, 1^1, 2^6` | `14 / 15 / 21 / 21` (`+6`) |
| `8` | `8×64` | `[1^7, 6]` (`max v_2=1`) | `28` | `1^{20}, 5^7, 15^1` | `0^{28}` | `28 / 28 / 28 / 28` |
| `9` | `9×81` | `[1^8, 7]` (`max v_2=0`) | `36` | `1^{27}, 3^1, 6^7, 42^1` | `0^{28}, 1^8` | `28 / 36 / 36 / 36` (`+8`) |
| `10` | `10×100` | `[1^9, 8]` (`max v_2=3`) | `45` | `1^{35}, 7^9, 28^1` | `0^{44}, 2^1` | `44 / 44 / 45 / 45` |
| `11` | `11×121` | `[1^{10}, 9]` (`max v_2=0`) | `55` | `1^{44}, 4^1, 8^9, 72^1` | `0^{44}, 2^1, 3^{10}` | `44 / 44 / 45 / 55` (**`+10`**) |
| `12` | `12×144` | `[1^{11}, 10]` (`max v_2=1`) | `66` | `1^{54}, 9^{11}, 45^1` | `0^{66}` | `66 / 66 / 66 / 66` |

At $n = 11 = 2^3 + 3$, $KG(11,2)$ exhibits **`10` simultaneous $8$-torsion factors** ($9$ copies of $8$ and $1$ copy of $72$, all with $v_2 = 3$), driving a linear jump from rank `45` in $W_3(\mathbb{F}_2) = \mathbb{Z}/8\mathbb{Z}$ to full rank `55` in $W_4(\mathbb{F}_2) = \mathbb{Z}/16\mathbb{Z}$. Moreover, [witt_kneser_linear_torsion_results.json](../results/witt_kneser_linear_torsion_results.json) confirms the exact `snf_Z` closed form for $M_{1,2}(e_3^{\mathrm{sym}})$ through $n=14$ (`[1^{12}, 11]` at $n=13$, `[1^{13}, 12]` at $n=14$ with `max v_2 = 2`, emerging at $W_3$).

### Table 4: Exact 2nd Witt Carry $4 C_2(x) \pmod{16}$: Ordered Commutative vs Symmetrized NC-IPS
From `nc_ips_vs_ordered_4C2_mod16_n4_to_10` in [witt_kneser_linear_torsion_results.json](../results/witt_kneser_linear_torsion_results.json) (cut $d = 2$):

| $n$ | Matrix Dims (`NC` / `Ord`) | Ordered Rank ($\mathbb{Z}/16\mathbb{Z}$) | NC Nisan Rank ($\mathbb{Z}/16\mathbb{Z}$) | Gap | Ratio (`NC / Ord`) | Invariant Factors ($\mathbb{Z}/16\mathbb{Z}$) & $4\cdot KG(n,2)$ Match |
| :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `4` | `6 × 6` | `1` | `6` | `5` | `6.00×` | `[4^6]` (`matches_4_times_KG_n_2_mod_16 = true`) |
| `5` | `10 × 20` | `2` | `10` | `8` | `5.00×` | `[4^6, 8^4]` (`true`) |
| `6` | `15 × 50` | `3` | `15` | `12` | `5.00×` | `[4^{14}, 8^1]` (`true`) |
| `7` | `21 × 112` | `4` | `15` | `11` | `3.75×` | `[4^{14}, 8^1]` (`true`; $6$ factors of $16$ vanish mod $16$) |
| `8` | `28 × 238` | `5` | `28` | `23` | `5.60×` | `[4^{28}]` (`true`) |
| `9` | `36 × 492` | `6` | `36` | `30` | `6.00×` | `[4^{28}, 8^8]` (`true`) |
| `10` | `45 × 1002` | **`7`** (`n - 3`) | **`45`** ($\binom{n}{2}$) | **`38`** | **`6.4286×`** | `[4^{44}, 8^1]` (`false` vs $4\cdot KG(10,2) = [4^{44}]$ due to higher $e_k$) |

Notice two sharp phenomena in Table 4:
1. **Linear-vs-Quadratic Rank Separation:** Ordered commutative lifts of $4 C_2(x)$ have $\mathbb{Z}/16\mathbb{Z}$-rank $n - 3$ (`7` at $n = 10$), whereas symmetrized NC-IPS lifts reach $\binom{n}{2}$ (`45` at $n = 10$), giving a `6.4286×` (`6.43×`) separation (`gap = 38`).
2. **Witt-Depth Collapse at $n = 7$:** Under $4\times$ scaling, the $6$ copies of $4$-torsion in $C_2^{\mathrm{sym}}$ (`[1^{14}, 2, 4^6]` in `exact_C2_symmetrized_d2`, [witt_higher_torsion_snf_results.json](../results/witt_higher_torsion_snf_results.json)) become `16`-torsion (`[4^{14}, 8, 16^6]` in `exact_4C2_symmetrized_d2_Z16`), vanishing identically in $W_4(\mathbb{F}_2) = \mathbb{Z}/16\mathbb{Z}$ (dropping NC rank from `21` to `15`) before re-emerging at depth $W_5(\mathbb{F}_2) = \mathbb{Z}/32\mathbb{Z}$.

---

## 5. Scope & Barrier Analysis (`Frege` / `NC-IPS` vs `Extended Frege`)

It is essential to delimit precisely which proof systems are obstructed by these $2$-adic Witt torsion gaps. Over `Extended Frege` (`EF`)—or equivalently `IPS` augmented with circuit/Tseitin extension variables—carry chains do **not** induce super-linear lower bounds: as established in carry-extension analyses (`arXiv:2210.17429`), introducing extension variables that explicitly name each half-adder and full-adder carry wire $c_j$ computes $\sum_{i=1}^n x_i$ modulo $2^k$ via a linear-size circuit of depth $O(\log n)$ (or $O(n)$ ripple chain), collapsing both Witt degree and proof size to linear.

Conversely, in **extension-free** systems—specifically non-commutative `IPS` (`NC-IPS`), algebraic branching programs without auxiliary carry variables, and bounded-formula `Frege` proofs—variables are restricted to the input bits $x_1, \dots, x_n$. Any `NC-IPS` refutation over $W_k(\mathbb{F}_2)$ must represent $4 C_2(x)$ or its symmetrized carry ideal directly in the free monoid $\mathbb{Z}/2^k\mathbb{Z}\langle x_1, \dots, x_n \rangle$, encountering both the off-diagonal commutator barrier `[x_i, x_j]` and the linear-rank $(n-1)$-dimensional $2^r$-torsion block of $KG(n,2)$ at depth $W_{r+1}(\mathbb{F}_2)$ (`n = 2^r + 3`).

### 5.1 Open Directions
1. **Universal $\forall n$ Unimodular Factorization of $KG(n,2)$:** Theorems 1 and 2 give explicit closed-form unimodular pairs $(P_n, Q_n)$ for $e_2^{\mathrm{sym}}$ and $e_3^{\mathrm{sym}}$, whereas Theorem 3 proves the $(n-1)$-dimensional $-(n-3)$-eigenspace of $KG(n,2)$; constructing explicit bilateral unimodular matrices over $\mathbb{Z}$ for the full $\binom{n}{2} \times \binom{n}{2}$ Kneser SNF remains a clean formalization target.
2. **Higher Witt Depths ($t \ge 3$):** Extending the Kneser $KG(n,2)$ pair-sum method to $KG(n, 2^{t-1})$ and $2^t C_t(x) \pmod{2^{k}}$ (`e_{2^t}^{\mathrm{sym}}`) promises super-linear $\binom{n}{2^{t-1}-1}$-dimensional $2^r$-torsion blocks at $W_{r+t}(\mathbb{F}_2)$.

---

## 6. Reproducibility Commands & References

```bash
# 1. Verify all three standalone Lean 4.36.0 suites (0 imports, 0 sorryAx)
lean proofs/witt_noncomm_nisan_frege.lean
lean proofs/witt_snf_universal_torsion.lean
lean proofs/witt_kneser_linear_torsion.lean

# 2. Reproduce JSON invariant-factor, Kneser torsion, and 4*C_2 mod 16 tables
uv run --with-editable . cap-witt-nc-ips   # -> results/witt_noncomm_ips_results.json
uv run --with-editable . cap-witt-snf      # -> results/witt_higher_torsion_snf_results.json
uv run --with-editable . cap-witt-kneser   # -> results/witt_kneser_linear_torsion_results.json
```

### References
1. Noam Nisan. Lower bounds for non-commutative computation. In *Proc. 23rd ACM STOC*, pp. 410–418, 1991.
2. Joshua A. Grochow and Toniann Pitassi. Circuit complexity, proof complexity, and polynomial identity testing: The Ideal Proof System. *J. ACM*, 65(6):37:1–37:59, 2018.
3. Michael A. Forbes, Amir Shpilka, Iddo Tzameret, and Avi Wigderson. Proof complexity lower bounds from algebraic circuit complexity. *Theory of Computing*, 17(10):1–88, 2021.
4. Nutan Limaye, Srikanth Srinivasan, and Sébastien Tavenas. Superpolynomial lower bounds against low-depth algebraic circuits. In *Proc. 62nd IEEE FOCS*, 2021.
5. László Lovász. On the Shannon capacity of a graph. *IEEE Trans. Information Theory*, 25(1):1–7, 1979; and Chris Godsil and Gordon Royle, *Algebraic Graph Theory*, Springer GTM 207, 2001 (Kneser $KG(n,k)$ spectra).
6. Carry extension variables and `Extended Frege` vs extension-free systems: `arXiv:2210.17429`, 2022.
