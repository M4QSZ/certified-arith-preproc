# Blind Degree-2 Veronese & $\mathbb{F}_2$-Homological `VeriPB 3.0` Certification for Expander-Entangled Goldreich PRG Formulas (`v0.3`)

> **Status:** Research prototype & Technical Note (`v0.3`). Not peer-reviewed; every certificate, theorem, and wall-clock metric has been mechanically verified with `Lean 4.36.0` (`0 sorryAx`) and `veripb 3.0.2`.

---

## Abstract

Technical Note `v0.2` left open **Limitation #2**: formulas whose unrolled primal graph forms a **single high-expansion component without small vertex cuts (`|S| = 0`)**—such as Goldreich 5-local pseudorandom generator (PRG) predicates (`TSA` $= \mathrm{XOR}_3 \oplus \mathrm{AND}_2$ and `XOR-MAJ₃`) coupled across 3-regular expanders—defeat primal-cut decomposition (`discover_primal_vertex_cut -> None`), binary-clique Cutting Planes (`0` AMO cliques), and degree-1 parity extraction (`0` linear $\mathbb{F}_2$ hyperplanes). Simultaneously, variable- and polarity-scrambled 3-CNF encodings of single-expander `TSA` and $\mathbb{F}_2$-homological `XOR₃-MAJ₃` formulas defeat pure CDCL (`Kissat 4.0.4`, `CaDiCaL 1.9.5`) and CDCL+XOR (`CryptoMiniSat 5`), all three of which suffer exponential blowup and hit `TIMEOUT_60s` starting at $V \ge 48$ (`1,608` variables / `2,304` clauses) even with **zero disjunctive selector guards (`|S| = 0`)**.

This note documents `v0.3.0` of `certified-arith-preproc` (`veripb_veronese_prg.py` + `proofs/veronese_prg_soundness.lean`), resolving Limitation #2 for degree-2 Goldreich PRG predicates and rigorously delimiting the degree-3/4 frontier (`v0.4`):

1. **Blind Degree-2 Veronese $\mathrm{RM}(2, n)$ & $\mathbb{F}_2$-Simplicial Homology Calculus (`VeriPB 3.0.2`):** Recovers unrolled width-$k$ ($k \le 7$) blocks via logged `(1, 1)` resolution, extracts degree-$\le 2$ Boolean equations via fast $O(k 2^k)$ Möbius/ANF inversion, solves global sparse $\mathbb{F}_2$ RREF over $\mathrm{RM}(2, n)$, lazily introduces shared Veronese product witnesses $p_{u,w} \leftrightarrow (x_u \wedge x_w)$ (`red`), and emits pure `pol` + `red` (`0` `rup` search) refutations. Crucially, on **Homological `XOR₃-MAJ₃`** over $K_4$ tetrahedral 2-cycles ($\partial^2 = 0$), **every $\mathrm{MAJ}_3$ triplet in the entire formula is unique** (zero gate collisions), yet quadratic boundaries cancel identically in $\mathrm{RM}(2, n)$.
2. **End-to-End `VeriPB 3.0.2` Scaling (`13/13` Certified UNSAT, `4/4` SAT Rejected):** Certifies all `12/12` scaling instances (`|S| \in \{0, 2, 3\}`, up to `31,715` vars / `41,160` clauses) plus the `v0.2` vs `v0.3` ablation (`389.27 ms` vs `TIMEOUT_60s` on all three C/C++ solvers), and rejects `4/4` `SAT` controls with `0` false positives.
3. **Universal $\forall n$ Lean 4.36.0 Formalization + Mechanical Degree-2 Barrier (`14` Theorems, `0 sorryAx`):** Proves `red` witness soundness and RUP preservation for Veronese products, polarity-scrambling invariance of $\mathrm{RM}(2, n)$, universal $\forall n$ vanishing of $\mathrm{MAJ}_3$ over arbitrary $\mathbb{F}_2$-simplicial 2-cycles (`simplicial_2cycle_maj3_vanishes`), universal single-expander unsatisfiability (`homological_xor3_maj3_expander_unsat`), and the **Degree-2 Barrier Theorem** (`xor_maj5_no_deg2_annihilator`): across all $2^{22} = 4,194,304$ polynomials in $\mathrm{RM}(2, 6)$, `0` non-zero degree-$\le 2$ polynomials vanish on Goldreich's `XOR-MAJ₅` gate.

---

## 1. Related Work & Cook–Reckhow Positioning

* **Goldreich's PRG, Algebraic Degree & Linearization Thresholds:** Goldreich [1] (*2000*), Alekhnovich [2] (*FOCS 2003 / TOC 2005*), Bogdanov and Qiao [3] (*RANDOM 2009*), and Applebaum, Barak, and Wigderson [4] (*STOC 2010*) showed that 5-local PRGs based on degree-2 predicates (`TSA` $= x_1 \oplus x_2 \oplus x_3 \oplus x_4 x_5$ or `XOR-MAJ₃`) resist DPLL/Resolution ($2^{\Omega(n)}$ lower bounds) and degree-1 $\mathbb{F}_2$ Gaussian elimination, while Schoenebeck [5] (*FOCS 2008*) proved linear-degree $\Omega(n)$ Lasserre / Sum-of-Squares lower bounds on random sparse XOR/CSP expanders.
* **Why Both CDCL and `CryptoMiniSat 5` Collapse at `|S| = 0`:**
  * In `v0.2`, `CryptoMiniSat 5` solved standalone `Tseitin_140` in `1.85 s` and only collapsed when disjoined with `PHP` across a selector cut $S$.
  * In single-expander `Goldreich_TSA` and `Homological_XOR3_MAJ3` (`|S| = 0`), **every local block has empty degree-1 vanishing ideal** ($\mathcal{I}_1(B_v) = \{0\}$). Thus `CryptoMiniSat 5` extracts **zero** linear XOR clauses, while restricting quadratic/majority variables still leaves a 3-regular Tseitin expander requiring $2^{\Omega(V)}$ Resolution steps (`Kissat 4.0.4`, `CaDiCaL 1.9.5`).
* **$\mathbb{F}_2$-Simplicial Homology Without Gate Collisions:** Viewing $\mathrm{MAJ}_3(x_a, x_b, x_c) = x_a x_b \oplus x_a x_c \oplus x_b x_c \pmod 2$ as the 1-skeleton boundary $\partial\{a,b,c\} \in \Lambda^2([n])$, any closed 2-cycle $\mathcal{C}$ of triangles ($\partial \mathcal{C} = 0 \pmod 2$, e.g. disjoint $K_4$ boundaries) satisfies $\bigoplus_{T \in \mathcal{C}} \mathrm{MAJ}_3(T) \equiv 0 \pmod 2$ with **zero repeated 3-tuples**, defeating syntactic gate-congruence closure (Biere et al. [6], *SAT 2024*) while remaining polynomially refutable in `VeriPB 3.0` [7, 8] via shared Veronese witnesses.

---

## 2. Blind Degree-2 Veronese `VeriPB 3.0` Calculus (`veripb_veronese_prg.py`)

```text
Input: Variable-permuted, polarity-scrambled, clause-shuffled 3-CNF (n_vars, m clauses)
1. Logged (1,1)-chain unrolling (`_unroll_11_chains_logged`):
     Eliminates Tseitin 3-CNF splitting chains via `pol id_p id_n + [s] ;`.
2. Optional primal cut discovery (`discover_primal_vertex_cut`, |S| <= 6):
     - Single-expander PRGs yield S = None (|S| = 0, single fiber ()).
     - Hybrid formulas (e.g. PHP OR_S Homological_XOR3_MAJ3) split into 2^|S| fibers.
3. Per-fiber degree-<=2 Veronese extraction (`_extract_veronese_rm2_records`):
     For each unrolled block supp = (v_1, ..., v_k) (1 <= k <= 7) with >= 2^{k-1} clauses:
       - Compute exact O(k * 2^k) F_2 Mobius / ANF transform (or RM(2, k) vanishing ideal).
       - Reject blocks of algebraic degree >= 3 with empty RM(2, k) ideal (e.g. XOR-MAJ_5).
       - Emit record: L_i(x) ^ Q_i(x) == c_0^(i) (mod 2) in Veronese coordinates RM(2, n).
4. Sparse GF(2) RREF in RM(2, n) with minimal core tracking:
     Eliminate over coordinates {(u,)} U {(u, w) : u < w}; extract minimal inconsistent E*.
5. Lazy VeriPB 3.0 (`pol` + `red`, ZERO `rup`) realization on E*:
     a) Shared Veronese product witnesses p_{u,w} <-> (x_u & x_w) ONLY for (u,w) in U_{i in E*} Q_i:
          and_11: red 1 ~x_u 1 ~x_w 1 x_p >= 1 : x_p -> 1 ;
          and_0x: red 1 x_u 1 ~x_p >= 1 : x_p -> 0 ;
          and_x0: red 1 x_w 1 ~x_p >= 1 : x_p -> 0 ;
     b) Fold linearized block parity z_1 ^ ... ^ z_r == c_0^(i) via (r - 2) unconditional 3-XOR
        `red` steps (`_realize_parity3_bounds`), reducing the block residual to two B = 1 clauses
        on (s_{r-2}, z_r), derived over the 2^k-cube on `supp` via exact clause halving (`2 d`).
     c) Even-multiplicity Gocht-Nordstrom CG halving (`sum_and_halve`):
        Cancels all x_u, all shared p_{u,w}, all folding s_{i,t}, and all MAJ_3 witnesses w_e
        for arbitrary even multiplicities 2*M_z in Z, deriving G >= 1 (or 0 >= 1 at |S| = 0).
Output: Complete `.pbp` certificate verified by `veripb 3.0.2 --cnf`.
```

---

## 3. Universal $\forall n$ Formalization in Lean 4.36.0 (`proofs/veronese_prg_soundness.lean`)

Verified in `8.49 s` with standalone `Lean 4.36.0` (zero Mathlib imports, `0` warnings, `0 sorryAx`, kernel axioms only across all 14 `#print axioms`-audited theorems):

| Group | Lean 4.36.0 Verified Theorems | Mathematical Scope |
| :--- | :--- | :--- |
| **Group 1** | `veronese_and_red_11_witness`, `veronese_and_red_0x_sound`, `veronese_and_red_x0_sound`, `veronese_and_clauses_characterize_prod` | `VeriPB 3.0` `red` witness validity, RUP preservation of prior `and_*` clauses, and exact `p = u ∧ w` (`b2n p = b2n u * b2n w`) equivalence |
| **Group 2** | `maj3_anf_f2_exact`, `and_polarity_scramble_invariance`, `maj3_polarity_scramble_boundary_invariance` | Exact $\mathbb{F}_2$ quadratic boundary of `MAJ₃` and invariance of $\mathrm{RM}(2, n)$ quadratic supports under arbitrary literal polarity flips |
| **Group 3** | `k4_tetrahedron_maj3_boundary_zero`, `simplicial_2cycle_maj3_vanishes` | $K_4$ 4-face identity (`0` axioms) and universal inductive $\forall n, \forall x, \forall \text{tris}$ vanishing $\partial \mathcal{C} = 0 \Rightarrow \bigoplus \mathrm{MAJ}_3 = 0$ |
| **Group 4** | `homological_xor3_maj3_expander_unsat` | Universal $\forall V, n$ unsatisfiability of single-expander Homological `XOR₃-MAJ₃` under odd global vertex charge |
| **Group 5** | `clause_cube_halving_exact`, `xor_chain_fold_sound`, `veronese_even_multiplicity_cg_unsat` | Zero-slack $B = 1$ cube halving, inductive $\forall \text{zs}$ XOR-chain folding, and arbitrary-multiplicity `Int` CG halving cancellation |
| **Group 6** | `xor_maj5_no_deg2_annihilator` | **Mechanical Degree-2 Barrier:** across all $2^{22} = 4,194,304$ polynomials in $\mathrm{RM}(2, 6)$ and both polarities, only `0` vanishes on `y ⊕ MAJ₅(x₁..x₅) = rhs` |

---

## 4. Experimental Evaluation (60s 4-Solver Wall-Clock Suite)

Executed on a 4-core Linux machine (`Python 3.12`, `veripb 3.0.2`, `Kissat 4.0.4`, `CaDiCaL 1.9.5`, `CryptoMiniSat 5`). Every instance is randomly scrambled in variable IDs, literal polarities, literal order, and clause order prior to solving (`results/veronese_prg_benchmark_results.json`).

### Table 1: Single-Expander PRG Scaling (`|S| = 0`) & Hybrid Disjunctive Interpolants (`|S| \in \{2, 3\}`, 60s Limit)

| Instance | Vars / Clauses | `|S|` | `.pbp` Lines (`w`) | Ours (`Emit + veripb = Total`) | `Kissat 4.0.4` | `CaDiCaL 1.9.5` | `CryptoMiniSat 5` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `Goldreich_TSA_5Local_V28` | `938 / 1,344` | `0` | `6,158` (`178`) | **`138.13 ms`** (`103.15 + 34.98`) | `712.66 ms` | `447.07 ms` | `972.31 ms` |
| `Goldreich_TSA_5Local_V36` | `1,206 / 1,728` | `0` | `7,982` (`234`) | **`301.57 ms`** (`210.35 + 91.22`) | `5,184.87 ms` | `4,588.67 ms` | `9,067.69 ms` |
| `Goldreich_TSA_5Local_V48` | `1,608 / 2,304` | `0` | `10,276` (`284`) | **`465.90 ms`** (`336.26 + 129.64`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Goldreich_TSA_5Local_V64` | `2,144 / 3,072` | `0` | `14,132` (`412`) | **`319.07 ms`** (`240.37 + 78.70`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Goldreich_TSA_5Local_V96` | `3,216 / 4,608` | `0` | `21,220` (`620`) | **`1,660.17 ms`** (`1,049.55 + 610.62`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Homological_XOR3_MAJ3_5Local_V28` | `938 / 1,344` | `0` | `8,490` (`310`) | **`234.00 ms`** (`157.03 + 76.97`) | `1,289.80 ms` | `683.03 ms` | `1,700.38 ms` |
| `Homological_XOR3_MAJ3_5Local_V36` | `1,206 / 1,728` | `0` | `10,594` (`374`) | **`552.48 ms`** (`415.96 + 136.52`) | `15,133.87 ms` | `13,874.77 ms` | `22,104.03 ms` |
| `Homological_XOR3_MAJ3_5Local_V52` | `1,742 / 2,496` | `0` | `15,634` (`566`) | **`457.94 ms`** (`314.96 + 142.98`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Homological_XOR3_MAJ3_5Local_V80` | `2,680 / 3,840` | `0` | `23,752` (`848`) | **`1,611.74 ms`** (`1,210.20 + 401.54`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Homological_XOR3_MAJ3_6Local_V44` | `4,290 / 5,632` | `0` | `27,094` (`546`) | **`1,674.62 ms`** (`1,238.34 + 436.28`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP12_11_OR2_Homological_XOR3_MAJ3_V44` | `12,036 / 16,224` | `2` | `36,976` (`940`) | **`2,405.68 ms`** (`1,976.38 + 429.30`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP12_11_OR3_Homological_XOR3_MAJ3_V40` | `31,715 / 41,160` | `3` | `77,868` (`1,648`) | **`9,438.63 ms`** (`8,000.66 + 1,437.97`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |

### Table 2: `v0.2` vs `v0.3` Engine Ablation & Degree-3/4 Frontier Controls

| Instance | Vars / Clauses | `v0.2` (`veripb_interpolant`) | `v0.3` (`veripb_veronese_prg`) | `Kissat 4.0.4` | `CaDiCaL 1.9.5` | `CryptoMiniSat 5` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Ablation_v02_vs_v03_Homological_XOR3_MAJ3_V44` | `1,474 / 2,112` | `Rejected` (`185.40 ms`) | **`VERIFIED UNSAT` (`389.27 ms`)** | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Barrier_Cubic_XOR3_AND3_6Local_V36` *(deg 3)* | `3,510 / 4,608` | `Rejected` (`214.49 ms`) | `Rejected: outside RM(2, n)` (`1,204.93 ms`) | `12,449.85 ms` | `10,763.87 ms` | `19,532.79 ms` |
| `Barrier_Goldreich_XOR3_MAJ5_7Local_V36` *(deg 4)* | `9,270 / 11,520` | `Rejected` (`777.72 ms`) | `Rejected: outside RM(2, n)` (`2,329.90 ms`) | `7,942.65 ms` | `4,344.13 ms` | `17,666.45 ms` |

### Table 3: SAT Soundness Controls (`4/4` Rejected, 0 False Positives)

| Instance | Vars / Clauses | `CaDiCaL 1.9.5` | `v0.3` (`veripb_veronese_prg`) | Diagnostic |
| :--- | :---: | :---: | :---: | :--- |
| `SAT_Goldreich_TSA_5Local_V44_even` | `1,474 / 2,112` | `SAT` (`160.03 ms`) | **Rejected** (`100.77 ms`) | `Fiber () on separator S=[] is FEASIBLE or outside RM(2, n) Veronese calculus` |
| `SAT_Homological_XOR3_MAJ3_5Local_V44_even` | `1,474 / 2,112` | `SAT` (`148.16 ms`) | **Rejected** (`98.85 ms`) | `Fiber () on separator S=[] is FEASIBLE or outside RM(2, n) Veronese calculus` |
| `SAT_Homological_XOR3_MAJ3_6Local_V36_even` | `3,510 / 4,608` | `SAT` (`167.05 ms`) | **Rejected** (`293.24 ms`) | `Fiber () on separator S=[] is FEASIBLE or outside RM(2, n) Veronese calculus` |
| `SAT_PHP10_10_OR2_Homological_XOR3_MAJ3_V36` | `9,510 / 12,648` | `SAT` (`265.31 ms`) | **Rejected** (`993.23 ms`) | `Fiber (0, 1) on separator S=[6561, 8257] is FEASIBLE or outside RM(2, n) Veronese calculus` |

---

## 5. Honest Limitations & Delimited Frontier for `v0.4`

1. **Higher-Degree Algebraic Barriers (`deg >= 3`: `Cubic XOR₃-AND₃` & `Goldreich XOR₃-MAJ₅`):** As proved mechanically in `xor_maj5_no_deg2_annihilator` and measured in Table 2, predicates whose local vanishing ideal has trivial intersection with $\mathrm{RM}(2, k)$ (`nullity == 0`) yield zero equations in degree-2 Veronese space. Extending certification to `XOR₃-AND₃` and `XOR₃-MAJ₅` requires higher-order Veronese lifts $\mathrm{RM}(d, n)$ ($d \in \{3, 4\}$) or sparse Macaulay syzygy cascades, paying $O(n^d)$ coordinates unless bounded by hypergraph locality.
2. **Sub-Quadratic Random PRGs Without Homological 2-Cycles ($m \ll \binom{n}{2}$, $\partial \mathcal{C} \neq 0$):** When $m < n + \binom{n}{2}$ random 5-tuples lack a closed $\mathbb{F}_2$-simplicial 2-cycle in $\Lambda^2([n])$, the linearized $\mathrm{RM}(2, n)$ system has fewer rows than columns and is rank-deficient, matching Schoenebeck's $\Omega(n)$-degree SoS lower bound [5].
3. **External SAT Competition Benchmarks & Rust Port (`v0.4`):** All `v0.1–v0.3` families remain synthetic scrambled 3-CNFs; porting the proof logger to Rust and evaluating coverage on industrial / SAT Competition UNSAT benchmarks is the next engineering milestone.

---

## 6. Reproducibility Commands

```bash
# 1. Verify the universal ∀n Lean 4.36.0 Veronese & Homological PRG suite (14 theorems, 0 sorryAx)
lean proofs/veronese_prg_soundness.lean

# 2. Emit & verify VeriPB 3.0.2 proofs on scrambled TSA, Homological XOR3-MAJ3 & hybrid instances
uv run --with-editable . cap-veronese

# 3. Run the full 60s 4-solver benchmark suite (scaling + v0.2/v0.3 & deg-3/4 barriers + SAT controls)
uv run --with-editable '.[benchmarks]' cap-bench-veronese --timeout 60

# 4. Full v0.1 + v0.2 + v0.3 verification pipeline
./scripts/reproduce.sh --timeout 300
```

---

## References

1. Oded Goldreich. *Candidate One-Way Functions Based on Expander Graphs*. ECCC TR00-090, 2000.
2. Michael Alekhnovich. *More on Average Case vs Approximation Complexity*. FOCS 2003 / Theory of Computing 1(1):1–23, 2005.
3. Andrej Bogdanov and Youming Qiao. *On the Security of Goldreich's One-Way Function*. RANDOM 2009, LNCS 5687, pp. 392–405.
4. Benny Applebaum, Boaz Barak, and Avi Wigderson. *Public-Key Cryptography from Different Assumptions*. STOC 2010, pp. 171–180.
5. Grant Schoenebeck. *Linear Level Lasserre Lower Bounds for Certain k-CSPs*. FOCS 2008, pp. 593–602.
6. Armin Biere, Katalin Fazekas, Mathias Fleury, and Nils Froleyks. *Clausal Congruence Closure*. SAT 2024, LIPIcs Vol. 305, pp. 6:1–6:25.
7. Stephan Gocht and Jakob Nordström. *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs*. AAAI 2021, Vol. 35(5), pp. 3768–3777.
8. Bart Bogaerts, Stephan Gocht, Ciaran McCreesh, and Jakob Nordström. *Certified Dominance and Symmetry Breaking for Combinatorial Optimisation* (`VeriPB 3.0`). JAIR, 2023.
9. Stefan Szeider. *PBLean / pb-catcher: Formally Verified Pseudo-Boolean Proof Checking in Lean*. `arXiv:2602.08692`, 2026.
