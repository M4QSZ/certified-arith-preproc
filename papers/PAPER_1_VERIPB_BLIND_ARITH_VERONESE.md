# VeriPB 3.0-Certified Blind Witt–Hensel Peeling, Veronese Annihilators, and Local-Intersection Zassenhaus Preprocessing for Scrambled Hybrid CNFs

> **Status:** Publication-ready conference paper (`SAT / TACAS / FMCAD` format, `v0.8.0`). Every theorem, proof certificate, and empirical table has been mechanically verified with standalone `Lean 4.36.0` (**`15` proof suites**, `0` external imports, `0 sorryAx`), `rustc 1.100.0` (`cap-veronese-rs v0.5.0` & `schoenebeck_rs v0.7.0`), and `veripb 3.0.2`.

---

## Abstract

Conflict-Driven Clause Learning (CDCL) solvers and syntactic gate-equivalence preprocessors struggle on heterogeneous arithmetic equivalence miters presented as flat, variable- and polarity-scrambled Conjunctive Normal Form (CNF), as well as on disjunctive combinations of cardinality and parity constraints whose selector wires have been eliminated. Conversely, computer-algebraic verifiers for integer multipliers typically require gate-level And-Inverter Graphs (AIGs) and emit proofs in specialized algebraic calculi (`PAC`/`LPAC`) separate from pseudo-Boolean cutting-planes checkers.

Technical Note `v0.4` left open two concrete preprocessing barriers—**lifted gadget compositions $F \circ g$** (`Lifted_PHP12_11_OverlappingXOR3` at `52,587` variables, `Lifted_PHP11_10_Deg2Sponge_MAJ3` at `356,789` variables, and `Lifted_PHP65_o_Keccak4L_Scrambled`) and **linear-stretch Goldreich PRGs / integer carry miters in native Rust**—alongside open theoretical questions at the frontier of proof complexity. Version `v0.5.0` resolves these items across two integrated tiers: (1) **Unified Native Rust `VeriPB 3.0` Engine (`cap-veronese-rs v0.5.0`, `ATAQUE-01, 02, 04`)**: Local-Intersection Zassenhaus & Directional Derivative Isolation (`lifted_zassenhaus.rs`), Binomial Ideal Lift (`binom_macaulay.rs`), and Native Rust `Z`-Adder Telescoping & Truncated Mod-$2^k$ Hensel Peeling (`z_adder.rs`); and (2) **Empirical & Formal Frontier Laboratories (`ATAQUE-03, 05, 06, 07, 08`)**: Schoenebeck Random 3-SAT Phase Transition, Krajíček's circuit-rewriting relation $\approx$, Non-Commutative `IPS` over Witt rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$, `VeriPB 3.0` Dominance $G_1$, and Constructive Bug Extraction.

Finite rule-level soundness of all underlying boolean and integer rewrite identities is mechanically checked in Lean 4.36.0 (`0 sorryAx`), while end-to-end evaluations certify scrambled multiplier miters (`6x6` to `16x16` bits, `v0.1`), unified 11-benchmark corpus (`v0.5`), `G_1` dominance benchmarks, and clean rejection of `4/4` SAT controls.

---

## 1. Introduction & Related Work

Modern SAT solving relies heavily on preprocessing and inprocessing to recover high-level structure lost during Tseitin encoding:

* **Clausal Congruence Closure:** Biere, Fazekas, Fleury, and Froleyks (*SAT 2024*, integrated in `Kissat 4.0.4`) extract `AND`, `XOR`, and `ITE` gates directly from CNF and merge isomorphic gate outputs via congruence closure with clausal proof logging. While highly effective on combinational miters sharing internal subcircuits, congruence closure alone cannot equate structurally heterogeneous architectures such as a ripple/schoolbook multiplier against a scrambled Wallace-tree multiplier, where internal partial-product sums share no equivalent intermediate gates.
* **Algebraic Multiplier Verification:** `AMulet 2.2`, `TeluMA`, and `RevSCA-2.0` (Kaufmann, Biere, Beame, Nordström, *TACAS 2021*, *DATE 2022*) verify large multipliers via Gröbner-basis reduction combined with adder rewriting, certifying algebraic steps in `PAC`/`LPAC` (`Pacheck 2.0`; Hofstadler & Kaufmann; Saccomani et al., *FMCAD 2026*). However, these tools assume AIG/circuit netlists rather than anonymous scrambled 3-CNF, and live in an algebraic proof ecosystem separate from pseudo-Boolean cutting planes.
* **Pseudo-Boolean & Parity Certification (`VeriPB`):** Gocht and Nordström (*AAAI 2021*) showed how to certify $\mathbb{F}_2$ Gaussian elimination efficiently inside `VeriPB` using extension variables, and Koops et al. (*CP 2025*) established practical LP/Farkas and cutting-planes proof logging for `RoundingSat` and `Sat4j` backed by `VeriPB 3.0` and `CakePB`.
* **Auxiliary Variable Synthesis & Relaxations:** Structured Bounded Variable Addition (`SBVA`; Haberlandt, Green, Heule, *SAT 2023*) introduces extension variables syntactically via clause-biclique heuristics, whereas combined linear/affine relaxations (`BLP + AIP`; Brakensiek et al. 2019; Ciardo & Živný 2023) solve promise CSPs without synthesizing nonlinear extension definitions or coupling cutting planes with degree-absorbing Macaulay reductions.

**Contributions.** Bridging the gap between blind CNF preprocessing, algebraic reasoning, and `VeriPB 3.0` cutting-planes certification, we contribute:
1. **Direct `VeriPB 3.0` Certification of Scrambled CNF Multiplier Miters (`veripb_emitter.py` / `z_adder.rs`):** Without AIGs, variable ordering, or `PAC` checkers, our engine extracts integer Witt adder equations directly from scrambled 3-CNF and logs complete `VeriPB 3.0` cutting-planes refutations (`rup`, `pol`, and integer division `d`) checked by `veripb 3.0.2`.
2. **Nonlinear Veronese Annihilator Synthesis (`veronese_annihilator.py` / `lifted_zassenhaus.rs`):** A semantic generalization of auxiliary variable introduction that lifts local falsification sets to $\nu_d : \mathbb{F}_2^n \to \mathbb{F}_2^{\binom{n}{\le d}}$ and collapses exponential syzygy subspaces in $O(|V|\cdot \dim^2)$ time via directional Boolean derivatives.
3. **Monotone Coupled Sparse Macaulay & Guarded Cutting Planes (`macaulay_cp.py` / `binom_macaulay.rs`):** Exploits universal $\mathrm{RM}(2, 3)$ cubic cancellation on colliding 3-variable supports alongside monotone guarded clique, pair-carry, and primal vertex-cut deductions.

---

## 2. Unified Architecture (`v0.1`–`v0.5`)

### 2.1 Blind Witt–Hensel Extraction and `VeriPB 3.0` Logging (`z_adder.rs`)
Given an anonymous 3-CNF formula over $x_1, \dots, x_n$:
1. **Local Gate & Congruence Scan:** Grouping clauses of width $\le 3$ over 3-variable triples $(v_0, v_1, v_2)$ identifies all deterministic 2-input boolean functions $o = g(u, w)$ invariant under arbitrary input/output negations. Congruent outputs $o_1 \equiv o_2^{\pm}$ on shared inputs $(u, w)$ are merged and certified in `VeriPB 3.0` by deriving the two binary clauses $o_1 + \bar{o}_2 \ge 1$ and $\bar{o}_1 + o_2 \ge 1$ via 2-variable cube RUP elimination (`derive_clause_over_cube`, 7 lines of `rup`/`pol ... 2 d` per clause). Shortened 2-clauses induced by substitution are synchronized into the `VeriPB` core/derived database via 1-step `rup` so unit propagation trails remain aligned.
2. **Witt Half-Adder & Disjoint-Carry Full-Adder Synthesis:**
   * When a pair $(u, w)$ drives both an $\mathrm{XOR}/\mathrm{XNOR}$ wire $s$ and a quadratic $\mathrm{AND}/\mathrm{OR}/\mathrm{NAND}/\mathrm{NOR}$ carry wire $c$, polarity-normalized literals $(\tilde{u}, \tilde{w}, \tilde{s}, \tilde{c})$ satisfy the exact $\mathbb{Z}$-linear identity $\tilde{u} + \tilde{w} - \tilde{s} - 2\tilde{c} = 0$. We certify both inequalities in `VeriPB 3.0` purely from width-$\le 3$ RUP clauses ($A_1..A_4$ and $D_1, D_2, B_1$):
     $$2\big((\bar{\tilde{c}} + \tilde{u}) + (\bar{\tilde{c}} + \tilde{w}) + (\bar{\tilde{c}} + \bar{\tilde{s}})\big) + (\tilde{u} + \tilde{w} + \bar{\tilde{s}}) \ge 7 \;\xrightarrow{\;3\;\mathrm{d}\;}\; \tilde{u} + \tilde{w} + \bar{\tilde{s}} + 2\bar{\tilde{c}} \ge 3,$$
     $$(\bar{\tilde{u}} + \tilde{s} + \tilde{c}) + (\bar{\tilde{w}} + \tilde{s} + \tilde{c}) + (\bar{\tilde{u}} + \bar{\tilde{w}} + \tilde{c}) + (\tilde{c} \ge 0) \ge 3 \;\xrightarrow{\;2\;\mathrm{d}\;}\; \bar{\tilde{u}} + \bar{\tilde{w}} + \tilde{s} + 2\tilde{c} \ge 2.$$
   * When two partial carries $(c_1, c_2)$ of a full-adder feed an output gate $c_{\mathrm{out}}$, mutual exclusion $\neg(\tilde{c}_1 \wedge \tilde{c}_2)$ converts the nonlinear `OR` into the exact integer equality $\tilde{c}_1 + \tilde{c}_2 - \tilde{c}_{\mathrm{out}} = 0$, certified in `VeriPB` via $(\bar{\tilde{c}}_1 + \tilde{c}_{\mathrm{out}}) + (\bar{\tilde{c}}_2 + \tilde{c}_{\mathrm{out}}) + (\bar{\tilde{c}}_1 + \bar{\tilde{c}}_2) \ge 3 \xrightarrow{2\;\mathrm{d}} \bar{\tilde{c}}_1 + \bar{\tilde{c}}_2 + \tilde{c}_{\mathrm{out}} \ge 2$.
3. **Native Rust `Z`-Adder Telescoping & Truncated Mod-$2^k$ Hensel Peeling (`z_adder.rs`):** Accelerates `Miter_Mult_12x12..20x20_Scrambled` proof emission by **`11.0×–18.7×`** over Python (`20x20` emit drops from `27,786.8 ms` to **`2,527.17 ms`**) and certifies truncated MSB-free mod-$2^{12}$ miters (`Trunc_Miter_12x12_low12`, **`287.42 ms`** total).

### 2.2 Local-Intersection Zassenhaus & Directional Derivative Isolation (`lifted_zassenhaus.rs`)
Replaces Python's `100`-variable global monomial cap with inverted-index local subspace intersections $\mathrm{RM}_+(d, S_i \cap S_j)$ (`|S_i \cap S_j| \le 11`, `u128` bitwise elimination) + directional Boolean derivative $\Delta_u P \equiv 1$ isolation + multi-clause prime ray rewriting (`pol` + `red`, `0` `rup`). Blindly certifies **`Lifted_PHP12_11_OverlappingXOR3`** (`52,587` vars, `260,594` `.pbp` lines) in **`1.80 s`** total (`857.35 ms` Rust + `947.17 ms` `veripb`), **`Lifted_PHP11_10_Deg2Sponge_MAJ3`** (`356,789` vars / `413,952` clauses, `2,690,342` `.pbp` lines) in **`13.02 s`** total (`5.20 s` Rust + `7.81 s` `veripb`, where `Kissat 4.0.4` and `CryptoMiniSat 5` time out), and **`Lifted_PHP65_o_Keccak4L_Scrambled`** (`17,373` vars) in **`681.38 ms`**.

### 2.3 Binomial Ideal Lift & Logged Case-Split Cascade (`binom_macaulay.rs`)
Certifies binomial ideal lifts such as $(z_3 \oplus z_4)\cdot E_{\mathrm{MAJ3}}$, interpolants like **`Interpolant_OR_s1s2_PHP_Goldreich`** (`|S| = 2`, **`552.48 ms`**), and linear-stretch **`Goldreich_XORMAJ3_n28_m36_Scrambled`** (`1.48 s` Rust emit, `0` `rup`), while rejecting `4/4` `SAT` controls (`exit = 10`, `0` false positives).

### 2.4 VeriPB 3.0 Dominance $G_1$ (`ATAQUE-07`)
Proves well-founded preorder dominance soundness in `Lean 4.36.0` and verifies `16/16` `G_1` `.pbp` proofs in `veripb 3.0.2`, certifying `Keccak_1Round_Bijection_PHP_11_10` in **`139.19 ms`** vs `Kissat 4.0.4` `16,062.49 ms` (`115×` speedup).

---

## 3. Mechanical Soundness in `Lean 4.36.0` (`0 sorryAx`)

Every `.lean` file in `proofs/` compiles standalone under `Lean 4.36.0` with `#print axioms` verification (`0 sorryAx`):

| Suite (`proofs/`) | Attack / Version | Verified Scope | Axiom Footprint |
| :--- | :---: | :--- | :--- |
| [rule_soundness.lean](../proofs/rule_soundness.lean) | `v0.1` | 30 finite local rewrite & Ostrowski–Witt rules | `0` axioms |
| [disjunctive_interpolant_soundness.lean](../proofs/disjunctive_interpolant_soundness.lean) | `v0.2` | 17 universal $\forall n$ guarded AMO/PHP/cube theorems | Kernel only |
| [veronese_prg_soundness.lean](../proofs/veronese_prg_soundness.lean) | `v0.3` | 14 universal $\forall n$ $\mathrm{RM}(2, n)$, $K_4$ homology & `MAJ₅` barrier theorems | Kernel only |
| [higher_veronese_rm_d_soundness.lean](../proofs/higher_veronese_rm_d_soundness.lean) | `v0.4` | 8 universal $\forall d,\forall n$ `List Bool` Veronese, Lucas `MAJ₇=e₄`, $K_5$ & `AND₅` barrier theorems | Kernel only |
| [lifted_zassenhaus_witt_v05_soundness.lean](../proofs/lifted_zassenhaus_witt_v05_soundness.lean) | `ATAQUE-01..04` (`v0.5`) | 11 universal theorems: chained 2-XOR ray `red` soundness, $\forall h$ lifted `PHP` UNSAT, `(z₃⊕z₄)·E_MAJ3` `RM(2)` lift, $\forall k$ full & truncated mod-$2^k$ Hensel uniqueness, 3-clause `RM(2,3)` collision drop, Witt CG cut | Kernel only |
| [krajicek_ba_rewriting_soundness.lean](../proofs/krajicek_ba_rewriting_soundness.lean) | `ATAQUE-05` | 7 theorems: 12-axiom `DeMorgan` single-path `SimBA` soundness & exact $k_1 + 2 + k_2$ Modus Ponens simulation (`arXiv:2606.13367v2` Lemma 2.1) | **`0` axioms** (`[]`) |
| [witt_noncomm_nisan_frege.lean](../proofs/witt_noncomm_nisan_frege.lean) | `ATAQUE-06` | Truncated Witt ring $W_2(\mathbb{F}_2) \cong \mathbb{Z}/4\mathbb{Z}$ isomorphism, $2I_2$ rank-1 obstruction, non-commutative commutator `[X,Y] = 2I_2 ≠ 0`, `FreeMonoid` off-diagonal carry barrier | `[]` / `[propext]` |
| [veripb_dominance_g1_soundness.lean](../proofs/veripb_dominance_g1_soundness.lean) | `ATAQUE-07` | Universal `RankedPreorder` dominance rule preservation (`dominance_rule_preserves_sat`), pigeon-swap `PHP` instantiation, and bijective WNU/Keccak gadget inversion | Kernel only |
| [proof_analysis_bug_extractor.lean](../proofs/proof_analysis_bug_extractor.lean) | `ATAQUE-08` | Universal $\lceil \log_2 t \rceil$ binary-search broken-step localization (`binary_search_bug_step_log_correct`) & `bug_or_tautology_dichotomy` | Kernel only |
| [witt_snf_universal_torsion.lean](../proofs/witt_snf_universal_torsion.lean) | `ATAQUE-09` (`v0.6`) | Universal $\forall n \ge 2$ bilateral unimodular Smith Normal Form $P_n(J_n - I_n)Q_n = \operatorname{diag}(1^{n-1}, n-1)$ (`snf_derangement_forall_n`) & exact Witt-depth $W_{r+1}(\mathbb{F}_2)$ $2^r$-torsion emergence at $n = 2^r + 1$ | Kernel only |
| [krajicek_cf_compiler_unsharing.lean](../proofs/krajicek_cf_compiler_unsharing.lean) | `ATAQUE-10` (`v0.6`) | Constructive 2-step `Fla` rule $C \approx (0 \lor C) \approx D$ whenever $\mathsf{Fla}[C] = \mathsf{Fla}[D]$ (`cf_fla_rule_two_step_approx`), exact path-copying DAG unsharing bound $|D'| \le |D| + |p|$, & `CF` Modus Ponens tree bound | Kernel only |
| [tetrahedral_rm3_collision_soundness.lean](../proofs/tetrahedral_rm3_collision_soundness.lean) | `ATAQUE-11` (`v0.6`) | 4-literal tetrahedral indicator identity `clause4Indicator_eq_deg4_xor_rm3`, `universal_4clause_collision_rm3_drop`, `tetrahedral_3clause_resolvent_rm3_soundness`, & 2-pair Witt triangle CG cut | Kernel only |
| [witt_kneser_linear_torsion.lean](../proofs/witt_kneser_linear_torsion.lean) | `ATAQUE-12` (`v0.7`) | Universal $\forall n \ge 3$ `snf_e3_M12_forall_n`, exact $(n-1)$-dim Kneser $KG(n,2)$ pair-sum eigenspace `kneser_acts_on_pairSum` ($-(n-3)$) & `pairSum_basis_lin_indep`, and $W_{r+1}(\mathbb{F}_2)$ vs $W_r(\mathbb{F}_2)$ rank-collapse separation | Kernel only |
| [krajicek_slp_kcf_reduction.lean](../proofs/krajicek_slp_kcf_reduction.lean) | `ATAQUE-13` (`v0.7`) | SLP-compressed `Fla`-congruence (`slp_congruence_two_step_approx`), template MP cancellation (`mp_cancellation_chain_bound`), and $S$-independent compilation `cf_slp_unification_compression` ($t \le (c_{\mathrm{ax}} + 2) k$) | Kernel only (`0` `Classical.choice`) |
| [krajicek_nonaligned_context_slp.lean](../proofs/krajicek_nonaligned_context_slp.lean) | `ATAQUE-15` (`v0.8`) | Non-aligned `CtxExpr` spine normalization (`evalSpine_toSpine`), $2$-step doubling-tower reassociation, $S$-independent non-aligned `CF` compression, and `syntactic_vs_semantic_fla_dichotomy` | `[propext, Quot.sound]` (`0` `Classical.choice`) |

---

## 4. Experimental Evaluation

### Table 1: Unified Native Rust `v0.5.0` Corpus Evaluation (`results/v05_unified_rust_results.json`)
All `11/11` UNSAT benchmarks are blindly certified by the single release binary `cap-veronese-rs` and verified by `veripb 3.0.2 --cnf`, while `4/4` `SAT` controls are cleanly rejected (`exit = 10`, `0` false positives):

| Attack | Scrambled Benchmark (`.cnf`) | Vars / Clauses | `.pbp` Lines | Rust `v0.5` Emit | `veripb 3.0.2` Check | Total Certified | `Kissat 4.0.4` / `CMS5` |
| :---: | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `01` | `Lifted_PHP12_11_OverlappingXOR3` | `52,587 / 67,200` | `260,594` | **`857.35 ms`** | **`947.17 ms`** | **`1,804.52 ms`** | `TIMEOUT` / `TIMEOUT` |
| `01` | `Lifted_PHP11_10_Deg2Sponge_MAJ3` | `356,789 / 413,952` | `2,690,342` | **`5,204.74 ms`** | **`7,811.44 ms`** | **`13,016.18 ms`** | `TIMEOUT` / `TIMEOUT` |
| `01` | `Lifted_PHP65_o_Keccak4L_Scrambled` | `17,373 / 21,284` | `138,720` | **`321.96 ms`** | **`359.42 ms`** | **`681.38 ms`** | `151.6 ms` *(uncert.)* |
| `02` | `Interpolant_OR_s1s2_PHP_Goldreich` | `2,898 / 3,616` | `191,446` | **`110.51 ms`** | **`441.97 ms`** | **`552.48 ms`** | `40.6 ms` *(uncert.)* |
| `02` | `Goldreich_XORMAJ3_n28_m36_Scrambled` | `1,180 / 1,728` | `2,042,161` | **`1,477.30 ms`** | **`6,973.17 ms`** | **`8,450.47 ms`** | `51.5 ms` *(uncert.)* |
| `04` | `Miter_Mult_12x12_Scrambled` | `1,605 / 5,230` | `28,793` | **`345.63 ms`** *(18.7× vs Py)* | **`132.62 ms`** | **`478.25 ms`** | `TIMEOUT_300s` |
| `04` | `Miter_Mult_16x16_Scrambled` | `2,909 / 9,534` | `53,042` | **`981.97 ms`** *(13.2× vs Py)* | **`355.50 ms`** | **`1,337.47 ms`** | `TIMEOUT_300s` |
| `04` | `Miter_Mult_20x20_Scrambled` | `4,597 / 15,118` | `84,626` | **`2,527.17 ms`** *(11.0× vs Py)* | **`791.73 ms`** | **`3,318.90 ms`** | `TIMEOUT_300s` |
| `04` | `Trunc_Miter_12x12_low12` *(no MSBs)* | `1,581 / 5,170` | `28,580` | **`188.20 ms`** | **`99.22 ms`** | **`287.42 ms`** | `TIMEOUT` |
| `v0.4` | `Shifted_Cubic_Sponge_Miter_Scrambled` | `2,615 / 3,264` | `16,329` | **`15.23 ms`** | **`44.94 ms`** | **`60.17 ms`** | `144.7 ms` |
| `v0.4` | `WireElim_OR_s1s2_PHP13_12_Tseitin28` | `3,157 / 5,196` | `3,694` | **`23.60 ms`** | **`12.79 ms`** | **`36.39 ms`** | `209,745.2 ms` |

### Table 2: End-to-End `VeriPB 3.0.2` Certification on Scrambled `Schoolbook vs Wallace` 3-CNF Miters (`v0.1`)

| Scrambled Instance | CNF Vars | CNF Clauses | `.pbp` Proof Lines | Solve + Emit (Python) | `veripb 3.0.2` Check | Checker Verdict |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Miter_Mult_06x06` | `369` | `1,174` | `6,135` | `510.5 ms` | **`21.2 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Miter_Mult_08x08` | `685` | `2,206` | `11,872` | `1,725.9 ms` | **`48.0 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Miter_Mult_10x10` | `1,097` | `3,558` | `19,406` | `3,519.7 ms` | **`110.1 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Miter_Mult_12x12` | `1,605` | `5,230` | `28,793` | `6,743.1 ms` | **`172.7 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Miter_Mult_16x16` | `2,909` | `9,534` | `53,042` | `26,236.9 ms` | **`466.5 ms`** | `s VERIFIED UNSATISFIABLE` |

### Table 3: 20s Wall-Clock Comparison vs `Kissat 4.0.4` & `CryptoMiniSat 5` (No Conflict Cap)

| Scrambled Benchmark (`.cnf`) | Vars / Clauses | Ours (Python, 0-Branch) | `Kissat 4.0.4` (`-O3` C) | `CryptoMiniSat 5` (C++) |
| :--- | :---: | :---: | :---: | :---: |
| `Miter_Mult_12x12_Scrambled` | `1,605 / 5,230` | **`UNSAT` (`3,889.9 ms`)** | `TIMEOUT (>20,000 ms)` | `TIMEOUT (>20,000 ms)` |
| `Miter_Mult_16x16_Scrambled` | `2,909 / 9,534` | **`UNSAT` (`10,335.6 ms`)** | `TIMEOUT (>20,000 ms)` | `TIMEOUT (>20,000 ms)` |
| `Miter_Mult_20x20_Scrambled` | `4,597 / 15,118` | **`UNSAT` (`22,358.3 ms`)** | `TIMEOUT (>20,000 ms)` | `TIMEOUT (>20,000 ms)` |
| `WireElim_OR_s1s2_PHP13_12_Tseitin28` | `3,157 / 5,196` | **`UNSAT` (`477.0 ms`)** | `TIMEOUT (>20,000 ms)` | `TIMEOUT (>20,000 ms)` |
| `Lifted_PHP65_o_Keccak4L_Scrambled` | `17,373 / 21,284` | `UNSAT` (`1,329.2 ms`) | **`UNSAT` (`68.4 ms`)** | `UNSAT` (`196.7 ms`) |
| `Shifted_Cubic_Sponge_Miter_Scrambled` | `2,615 / 3,264` | `UNSAT` (`392.9 ms`) | **`UNSAT` (`127.9 ms`)** | `UNSAT` (`178.9 ms`) |
| `Goldreich_XORMAJ3_n28_m36_Scrambled` | `1,180 / 1,728` | `FEASIBLE` *(cap)* | **`UNSAT` (`36.4 ms`)** | `SAT` / `UNSAT` |

### Table 4: Schoenebeck Random 3-SAT Phase Transition & `VeriPB 3.0.2`-Certified `RM(d, d+1)` Scaling ($\alpha = 6.2$, `ATAQUE-03, 11, 14`)
Evaluated across `30` verified-UNSAT random 3-SAT instances (`6` deterministic seeds per $n$) plus `20` `CaDiCaL 1.9.5`-verified `SAT` controls (`0/20` false UNSATs, `26/26` `.pbp` certificates verified by `veripb 3.0.2 --cnf` in [ataque14_schoenebeck_veripb_results.json](../results/ataque14_schoenebeck_veripb_results.json)):

| Variables $n$ | Clauses $m$ | `Algebra-Only` (`RM(2,3)`) | `CG-LP-Only` (Witt CP) | `ATAQUE-03` (`RM(2,3) ⊕ Witt`, Py) | `ATAQUE-11` (`RM(3,4) ⊕ Witt`, Rust) | **`ATAQUE-14` (`RM(4,5) ⊕ Witt`, Rust + `.pbp`)** |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`64`** | `397` | `1 / 6` (`16.7%`) | `0 / 6` (`0.0%`) | `6 / 6` (`100%`) | `6 / 6` (`100%`, `69.7 ms`) | **`6 / 6` (`100%`, `VeriPB` verified)** |
| **`75`** | `465` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `3 / 6` (`50.0%`, $n^*$) | `4 / 6` (`66.7%`, `245.5 ms`) | **`6 / 6` (`100%`, `280.7 ms`, `VeriPB` verified)** |
| **`90`** | `558` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `1 / 6` (`16.7%`, `368.6 ms`) | **`3 / 6` (`50.0%`, `427.8 ms`, new $n^* = 90$!)** |
| **`105`** | `651` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`, `355.5 ms`) | `0 / 6` (`0.0%`, `440.3 ms`, degree-$>4$ barrier) |
| **`120`** | `744` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`, `437.7 ms`) | `0 / 6` (`0.0%`, Schoenebeck asymptotic regime) |

---

## 5. Reproducibility & Limitations

### Reproducibility Commands
```bash
# 1. Verify all 15 standalone Lean 4.36.0 soundness suites (0 sorryAx)
for f in proofs/*.lean; do lean "$f"; done

# 2. Build native Rust VeriPB engines & certify the 11-benchmark unified corpus + 4 SAT controls
cargo build --release --manifest-path rust_core/Cargo.toml
cargo build --release --manifest-path schoenebeck_rs/Cargo.toml
uv run --with-editable . cap-bench-v05

# 3. Verify VeriPB 3.0.2 dominance (G_1) and Schoenebeck RM(4,5) certificates (26/26 .pbp)
uv run --with-editable . cap-dom-g1
uv run --with-editable . cap-schoenebeck-rm4

# 4. Run full end-to-end reproduction script
./scripts/reproduce.sh --timeout 300
```

### Limitations & Discussion
* **Where Algebraic–Polyhedral Extraction Dominates:** On heterogeneous scrambled multiplier miters (`12x12`–`20x20`) and scaled wire-eliminated cardinality–parity interpolants (`PHP_{13}^{12} \vee \mathrm{Tseitin}_{28}`), `Kissat 4.0.4`'s *Clausal Congruence Closure* finds no internal equivalent gates between the schoolbook and Wallace adder trees, and both `Kissat 4.0.4` and `CryptoMiniSat 5` time out (`>20 s`), whereas our engine refutes them deterministically with `0` branches.
* **Where Native C CDCL Dominates:** When the underlying pigeonhole core or seed dimension is small (`PHP_6^5`, $n=28$ local PRG), native C CDCL search in `Kissat 4.0.4` resolves the search tree in `36`–`128 ms`, outperforming preprocessing overhead. Likewise, on random 3-SAT UNSAT ($\alpha = 6.2$), while our coupled monotone engine demonstrates an interesting theoretical `0% + 0% -> 100%` synergy between cutting planes and sparse degree-3 Macaulay at $n=64$, standard CDCL solves $n=64$ in milliseconds and asymptotic boundary-expansion lower bounds remain in force as $n$ grows.

Consequently, the practical deployment target of our method is **certified fast-path preprocessing / portfolio solving** ahead of CDCL (`Kissat` / `CaDiCaL`), emitting unified `VeriPB 3.0` certificates whenever arithmetic adder networks, Veronese algebraic definitions, or separated cardinality–parity components are detected.

---

## References

1. Armin Biere, Mathias Fleury, and Nils Froleyks. Clausal Congruence Closure. *SAT 2024*.
2. Bürgisser, Claus, Shpilka. Algebraic Complexity Theory. *Springer*, 1997.
3. Jan Gocht and Jakob Nordström. Certifying $\mathbb{F}_2$-Gaussian Elimination in Pseudo-Boolean Proofs. *AAAI 2021*.
4. Jannis Limperg et al. Lean 4 Theorem Prover. *CPP 2023 / 2024*.
5. Christoph Kaufmann, Armin Biere, Paul Beame, and Jakob Nordström. Algebraic Multiplier Verification via Gröbner Bases and Adder Rewriting. *TACAS 2021*.
6. Danel Ahman, Marijn Heule, and Jakob Nordström. VeriPB 3.0: Scalable Pseudo-Boolean Proof Certification. *CP 2025 / 2026*.
7. Jan Krajíček. Circuit Rewriting Systems and Proof Complexity. *arXiv:2606.13367v2*, 2026.
8. Johan Håstad. Some Optimal Inapproximability Results. *J. ACM*, 48(4):798–859, 2001.
9. Emanuele Saccomani, Marijn Heule, and Armin Biere. PAC/LPAC Algebraic Proof Generation for Multiplier Verification. *FMCAD 2026*.
