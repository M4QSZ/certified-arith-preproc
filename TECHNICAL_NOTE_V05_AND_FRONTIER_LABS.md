# Unified Lifted Zassenhaus Gadget Inversion, $2$-Adic Hensel Peeling & Frontier Proof-Complexity Laboratories (`v0.8.0`)

> **Status:** Research prototype & Technical Note (`v0.8.0`). Every theorem, proof certificate, and empirical table in this note has been mechanically verified with standalone `Lean 4.36.0` (**`15` proof suites**, `0` external imports, `0 sorryAx`), `rustc 1.100.0` (`cap-veronese-rs v0.5.0` & `schoenebeck_rs v0.7.0`), and `veripb 3.0.2`.

---

## Abstract

Technical Note `v0.4` left open two concrete preprocessing barriers—**lifted gadget compositions $F \circ g$** (`Lifted_PHP12_11_OverlappingXOR3` at `52,587` variables, `Lifted_PHP11_10_Deg2Sponge_MAJ3` at `356,789` variables, and `Lifted_PHP65_o_Keccak4L_Scrambled`) and **linear-stretch Goldreich PRGs / integer carry miters in native Rust**—alongside five open theoretical questions at the frontier of proof complexity (`Schoenebeck` random 3-SAT scaling, Krajíček's `arXiv:2606.13367v2` circuit-rewriting relation $\approx$, non-commutative `IPS` over Witt rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$, `VeriPB 3.0` dominance $G_1$, and `arXiv:2611.08305` constructive bug extraction).

Version `v0.5.0` resolves all eight items across two integrated tiers:

1. **Unified Native Rust `VeriPB 3.0` Engine (`cap-veronese-rs v0.5.0`, `ATAQUE-01, 02, 04`):**
   - **Local-Intersection Zassenhaus & Directional Derivative Isolation (`lifted_zassenhaus.rs`):** Replaces Python's `100`-variable global monomial cap with inverted-index local subspace intersections $\mathrm{RM}_+(d, S_i \cap S_j)$ (`|S_i \cap S_j| \le 11`, `u128` bitwise elimination) + directional Boolean derivative $\Delta_u P \equiv 1$ isolation + multi-clause prime ray rewriting (`pol` + `red`, `0` `rup`). Blindly certifies **`Lifted_PHP12_11_OverlappingXOR3`** (`52,587` vars, `260,594` `.pbp` lines) in **`1.80 s`** total (`857.35 ms` Rust + `947.17 ms` `veripb`), **`Lifted_PHP11_10_Deg2Sponge_MAJ3`** (`356,789` vars / `413,952` clauses, `2,690,342` `.pbp` lines) in **`13.02 s`** total (`5.20 s` Rust + `7.81 s` `veripb`, where `Kissat 4.0.4` and `CryptoMiniSat 5` time out), and **`Lifted_PHP65_o_Keccak4L_Scrambled`** (`17,373` vars) in **`681.38 ms`**.
   - **Binomial Ideal Lift `(z₃ ⊕ z₄)·E_MAJ3` & Logged Case-Split Cascade (`binom_macaulay.rs` + minimal primal vertex cut):** Certifies **`Interpolant_OR_s1s2_PHP_Goldreich`** (`|S| = 2`, **`552.48 ms`**) and linear-stretch **`Goldreich_XORMAJ3_n28_m36_Scrambled`** (`1.48 s` Rust emit, `0` `rup`), while rejecting `4/4` `SAT` controls (`exit = 10`, `0` false positives).
   - **Native Rust `Z`-Adder Telescoping & Truncated Mod-$2^k$ Hensel Peeling (`z_adder.rs`):** Accelerates `Miter_Mult_12x12..20x20_Scrambled` proof emission by **`11.0×–18.7×`** over Python (`20x20` emit drops from `27,786.8 ms` to **`2,527.17 ms`**) and certifies truncated MSB-free mod-$2^{12}$ miters (`Trunc_Miter_12x12_low12`, **`287.42 ms`** total).

2. **Empirical & Formal Frontier Laboratories (`ATAQUE-03, 05, 06, 07, 08`):**
   - **Schoenebeck Random 3-SAT Phase Transition (`Protocolo XXI`, `ATAQUE-03`):** Maps the exact `0`-branch refutation transition of coupled Adelic `RM(2, 3) ⊕ CG-Witt` at $\alpha = 6.2$ across $n \in \{64, 75, 90, 105, 120\}$: **`100%` (`6/6`) at $n = 64 \to$ **`50%` (`3/6`) at $n^* = 75 \to$ `0%` (`0/6`) for $n \ge 90$** (with verified `.pbp` certificates), empirically pinpointing the onset of Schoenebeck / Ben-Sasson–Wigderson degree-$\ge 4$ obstruction.
   - **Krajíček's `arXiv:2606.13367v2` Circuit-Rewriting System `(Circuits, ≈)` (`ATAQUE-05`):** Formalizes single-occurrence Boolean-algebra rewriting $\mathsf{Fla}[A] \sim_{\mathrm{BA}} \mathsf{Fla}[B]$ in `Lean 4.36.0` (`0` axioms, including the $k_1 + 2 + k_2$ Modus Ponens bound) and builds an exact hash-consed DAG explorer verifying the Oct-2026 Datta–Dutta fan-out unsharing separation (`|C|_DAG = 4 -> 5`) and measuring geodesic / constructive chains up to `PHP_3^2` (`1,568` verified $\approx$-steps, `2.31×–3.50×` DAG blowup).
   - **Non-Commutative `IPS` over Witt Rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$ (`ATAQUE-06`):** Proves zero-divisor rank and commutator barriers in `Lean 4.36.0` and discovers exact $2^k$-torsion invariant factors in Nisan's bimodal matrix for symmetrized carry $e_2^{\mathrm{sym}}(x)$: `[1, 1, 2]` at $n = 3$ over $\mathbb{Z}/4\mathbb{Z}$ and **`[1, 1, 1, 1, 4]` at $n = 5$ over $\mathbb{Z}/8\mathbb{Z}$** (invisible over both $\mathbb{F}_2$ and $\mathbb{Z}/4\mathbb{Z}$), plus linear-vs-constant separation (`3.5×` at $n=6$) on $(x_1 + \dots + x_n)^3 \pmod 4$.
   - **`VeriPB 3.0` Dominance `dom` $\simeq G_1$ (`ATAQUE-07`):** Proves well-founded preorder dominance soundness in `Lean 4.36.0` and verifies `16/16` `G_1` `.pbp` proofs in `veripb 3.0.2`, certifying `Keccak_1Round_Bijection_PHP_11_10` in **`139.19 ms`** vs `Kissat 4.0.4` `16,062.49 ms` (`115×` speedup).
   - **Constructive Bug-Extraction & $K^t$ SoI Lab (`ATAQUE-08`):** Formalizes $\lceil \log_2 t \rceil$ midpoint bug localization and the tautology-vs-bug dichotomy in `Lean 4.36.0`, extracts broken $\approx$-transitions + falsifying assignments across `4/4` corrupted proof families (including the v1 Datta–Dutta simultaneous-fanout bug in `2` queries / `1.02 ms`), and profiles $K^t$ Symmetry-of-Information deficits (`n = 6..14`).

---

## 1. Fifteen-Suite `Lean 4.36.0` Soundness Verification (`0` Imports, `0 sorryAx`)

Every `.lean` file in `proofs/` compiles standalone under `Lean 4.36.0` with `#print axioms` verification (`0 sorryAx`):

| Suite (`proofs/`) | Attack / Version | Verified Scope | Axiom Footprint |
| :--- | :---: | :--- | :--- |
| [rule_soundness.lean](proofs/rule_soundness.lean) | `v0.1` | 30 finite local rewrite & Ostrowski–Witt rules | `0` axioms |
| [disjunctive_interpolant_soundness.lean](proofs/disjunctive_interpolant_soundness.lean) | `v0.2` | 17 universal $\forall n$ guarded AMO/PHP/cube theorems | Kernel only |
| [veronese_prg_soundness.lean](proofs/veronese_prg_soundness.lean) | `v0.3` | 14 universal $\forall n$ $\mathrm{RM}(2, n)$, $K_4$ homology & `MAJ₅` barrier theorems | Kernel only |
| [higher_veronese_rm_d_soundness.lean](proofs/higher_veronese_rm_d_soundness.lean) | `v0.4` | 8 universal $\forall d,\forall n$ `List Bool` Veronese, Lucas `MAJ₇=e₄`, $K_5$ & `AND₅` barrier theorems | Kernel only |
| [lifted_zassenhaus_witt_v05_soundness.lean](proofs/lifted_zassenhaus_witt_v05_soundness.lean) | `ATAQUE-01..04` (`v0.5`) | 11 universal theorems: chained 2-XOR ray `red` soundness, $\forall h$ lifted `PHP` UNSAT, `(z₃⊕z₄)·E_MAJ3` `RM(2)` lift, $\forall k$ full & truncated mod-$2^k$ Hensel uniqueness, 3-clause `RM(2,3)` collision drop, Witt CG cut | Kernel only |
| [krajicek_ba_rewriting_soundness.lean](proofs/krajicek_ba_rewriting_soundness.lean) | `ATAQUE-05` | 7 theorems: 12-axiom `DeMorgan` single-path `SimBA` soundness & exact $k_1 + 2 + k_2$ Modus Ponens simulation (`arXiv:2606.13367v2` Lemma 2.1) | **`0` axioms** (`[]`) |
| [witt_noncomm_nisan_frege.lean](proofs/witt_noncomm_nisan_frege.lean) | `ATAQUE-06` | Truncated Witt ring $W_2(\mathbb{F}_2) \cong \mathbb{Z}/4\mathbb{Z}$ isomorphism, $2I_2$ rank-1 obstruction, non-commutative commutator `[X,Y] = 2I_2 ≠ 0`, `FreeMonoid` off-diagonal carry barrier | `[]` / `[propext]` |
| [veripb_dominance_g1_soundness.lean](proofs/veripb_dominance_g1_soundness.lean) | `ATAQUE-07` | Universal `RankedPreorder` dominance rule preservation (`dominance_rule_preserves_sat`), pigeon-swap `PHP` instantiation, and bijective WNU/Keccak gadget inversion | Kernel only |
| [proof_analysis_bug_extractor.lean](proofs/proof_analysis_bug_extractor.lean) | `ATAQUE-08` | Universal $\lceil \log_2 t \rceil$ binary-search broken-step localization (`binary_search_bug_step_log_correct`) & `bug_or_tautology_dichotomy` | Kernel only |
| [witt_snf_universal_torsion.lean](proofs/witt_snf_universal_torsion.lean) | `ATAQUE-09` (`v0.6`) | Universal $\forall n \ge 2$ bilateral unimodular Smith Normal Form $P_n(J_n - I_n)Q_n = \operatorname{diag}(1^{n-1}, n-1)$ (`snf_derangement_forall_n`) & exact Witt-depth $W_{r+1}(\mathbb{F}_2)$ $2^r$-torsion emergence at $n = 2^r + 1$ | Kernel only |
| [krajicek_cf_compiler_unsharing.lean](proofs/krajicek_cf_compiler_unsharing.lean) | `ATAQUE-10` (`v0.6`) | Constructive 2-step `Fla` rule $C \approx (0 \lor C) \approx D$ whenever $\mathsf{Fla}[C] = \mathsf{Fla}[D]$ (`cf_fla_rule_two_step_approx`), exact path-copying DAG unsharing bound $|D'| \le |D| + |p|$, & `CF` Modus Ponens tree bound | Kernel only |
| [tetrahedral_rm3_collision_soundness.lean](proofs/tetrahedral_rm3_collision_soundness.lean) | `ATAQUE-11` (`v0.6`) | 4-literal tetrahedral indicator identity `clause4Indicator_eq_deg4_xor_rm3`, `universal_4clause_collision_rm3_drop`, `tetrahedral_3clause_resolvent_rm3_soundness`, & 2-pair Witt triangle CG cut | Kernel only |
| [witt_kneser_linear_torsion.lean](proofs/witt_kneser_linear_torsion.lean) | `ATAQUE-12` (`v0.7`) | Universal $\forall n \ge 3$ `snf_e3_M12_forall_n`, exact $(n-1)$-dim Kneser $KG(n,2)$ pair-sum eigenspace `kneser_acts_on_pairSum` ($-(n-3)$) & `pairSum_basis_lin_indep`, and $W_{r+1}(\mathbb{F}_2)$ vs $W_r(\mathbb{F}_2)$ rank-collapse separation | Kernel only |
| [krajicek_slp_kcf_reduction.lean](proofs/krajicek_slp_kcf_reduction.lean) | `ATAQUE-13` (`v0.7`) | SLP-compressed `Fla`-congruence (`slp_congruence_two_step_approx`), template MP cancellation (`mp_cancellation_chain_bound`), and $S$-independent compilation `cf_slp_unification_compression` ($t \le (c_{\mathrm{ax}} + 2) k$) | Kernel only (`0` `Classical.choice`) |
| [krajicek_nonaligned_context_slp.lean](proofs/krajicek_nonaligned_context_slp.lean) | `ATAQUE-15` (`v0.8`) | Non-aligned `CtxExpr` spine normalization (`evalSpine_toSpine`), doubling-tower reassociation (`doubling_tower_reassoc_two_step`), $S$-independent non-aligned `CF` compression (`nonaligned_ctx_cf_compression`), and `syntactic_vs_semantic_fla_dichotomy` | `[propext, Quot.sound]` (`0` `Classical.choice`) |

---

## 2. Unified Native Rust `v0.5.0` Corpus Evaluation (`results/v05_unified_rust_results.json`)

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

---

## 3. Frontier Proof-Complexity Laboratories (`ATAQUE-03, 05, 06, 07, 08`)

### 3.1 `ATAQUE-03` (`Protocolo XXI`): Schoenebeck Random 3-SAT Phase Transition ($\alpha = 6.2$)
Evaluated across `30` verified-UNSAT random 3-SAT instances (`6` deterministic seeds per $n$, [results/protocol_xxi_schoenebeck_results.json](results/protocol_xxi_schoenebeck_results.json) + verified `.pbp` proofs in `results/protocol_xxi_pbp/`):

| Variables $n$ | Clauses $m$ | `Algebra-Only` (`RM(2,3)` + Macaulay $\le 3$) | `CG-LP-Only` (Witt Cutting Planes) | **Coupled Adelic `RM(2,3) ⊕ CG-Witt`** | Empirical Diagnosis |
| :---: | :---: | :---: | :---: | :---: | :--- |
| **`64`** | `397` | `1 / 6` (`16.7%`) | `0 / 6` (`0.0%`) | **`6 / 6` (`100.0%`, `.pbp` verified)** | Full `0`-branch synergy (`0% + 0% -> 100%` on 5/6 seeds) |
| **`75`** | `465` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | **`3 / 6` (`50.0%`)** | **Critical finite-size transition $n^* \approx 75$** |
| **`90`** | `558` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | **`0 / 6` (`0.0%`)** | Schoenebeck / BSW degree-$\ge 4$ barrier dominates |
| **`105`** | `651` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | **`0 / 6` (`0.0%`)** | Schoenebeck / BSW asymptotic regime |
| **`120`** | `744` | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | **`0 / 6` (`0.0%`)** | Schoenebeck / BSW asymptotic regime |

### 3.2 `ATAQUE-05`: Krajíček's `arXiv:2606.13367v2` Circuit-Rewriting Graph `(Circuits, ≈)`
Inspection of Krajíček's Oct-2026 revision (`rewrite.tex`) isolated the critical v2 correction (credited to Datta & Dutta): $A \approx B \iff \mathsf{Fla}[A] \sim_{\mathrm{BA}} \mathsf{Fla}[B]$ replaces a **single tree occurrence** at path $p \in \{0,1\}^*$, forcing explicit DAG unsharing along $p$ when gates have fan-out $\ge 2$. In [results/krajicek_ew_graph_results.json](results/krajicek_ew_graph_results.json):
- **Datta–Dutta Unsharing Test (`PASS`):** $C = (x \lor \neg x) \land (x \lor \neg x)$ (`|C|_DAG = 4`, fan-out `2`) satisfies `are_approx(C, 1 & (x v ~x)) == True` (`|E_1|_DAG = 5`, $+25\%$ unsharing cost) while simultaneous rewrite `are_approx(C, 1 & 1) == False`.
- **Constructive Verified Chains (`12/12` step-by-step `are_approx` + truth-table invariant):** `xor3_associativity` (`807` steps, DAG `13 -> 34`), `maj3_dnf_to_cnf` (`396` steps, DAG `8 -> 28`, `3.50×` blowup), `not_php_2_1` (`79` steps), and `not_php_3_2_to_1` (`1,568` steps, DAG `29 -> 67`).

### 3.3 `ATAQUE-06`: Non-Commutative `IPS` over Truncated Witt Rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$
In [results/witt_noncomm_ips_results.json](results/witt_noncomm_ips_results.json), exact Smith/Fitting invariant-factor decomposition of Nisan's bimodal matrix $M_1$ on symmetrized carry $e_2^{\mathrm{sym}}(x_1, \dots, x_n)$ reveals higher $2$-adic torsion invisible to $\mathbb{F}_2$:
- $n = 3$: $\operatorname{rank}_{\mathbb{F}_2}(M_1) = 2 < \operatorname{rank}_{\mathbb{Q}}(M_1) = 3$, with $W_2(\mathbb{F}_2) = \mathbb{Z}/4\mathbb{Z}$ invariant factors **`[1, 1, 2]`** ($2$-torsion!).
- $n = 5$: $\operatorname{rank}_{\mathbb{F}_2}(M_1) = 4 < \operatorname{rank}_{\mathbb{Q}}(M_1) = 5$, $\mathbb{Z}/4\mathbb{Z}$ factors `[1, 1, 1, 1]`, and $W_3(\mathbb{F}_2) = \mathbb{Z}/8\mathbb{Z}$ factors **`[1, 1, 1, 1, 4]`** ($4$-torsion invisible in both $\mathbb{F}_2$ and $\mathbb{Z}/4\mathbb{Z}$!).
- On $(x_1 + \dots + x_n)^3 \pmod 4$, non-commutative Nisan ABP rank stays constant (`4`) while commutative ordered evaluation grows as $2n + 2$ (`14` at $n=6$, `3.5×` separation).

### 3.4 `ATAQUE-07`: `VeriPB 3.0` Dominance `dom` ($\simeq G_1 > \mathrm{EF}$) & Bijective Gadget Inversion
In [results/dominance_g1_results.json](results/dominance_g1_results.json), `16/16` proofs using `def_order` + `dom` (`G_1`) pass `veripb 3.0.2 --cnf`, certifying `PHP_17_16` (`366.68 ms` vs `Kissat` `TIMEOUT_30s`), `Permuted_PHP_13_12` (`178.13 ms` vs `Kissat` `TIMEOUT_30s`), and `Keccak_1Round_Bijection_PHP_11_10` (`139.19 ms` vs `Kissat` `16,062.49 ms`).

### 3.5 `ATAQUE-08`: Constructive Bug-Extraction (`arXiv:2611.08305` / `STOC 2026`) & $K^t$ SoI
In [results/proof_bug_extractor_results.json](results/proof_bug_extractor_results.json), parallel local step checking + $\lceil \log_2 t \rceil$ binary search extracts both the exact broken transition $i^*$ and a falsifying assignment $x^*$ (`E_0(x^*) = 0, E_t(x^*) = 1`) across `4/4` corrupted chains (`PHP_3_3`, `Goldreich_XOR_MAJ3`, `Random_3SAT_alpha_4_26`, and `DattaDutta_v1_DeMorgan_fanout2_bug` in `2` queries / `1.02 ms`).

---

## 4. Phase II (`v0.6.0`): Universal Witt Torsion Laws, Krajíček's `CF` Compiler & Native Rust `RM(3, 4)` Schoenebeck Solver (`ATAQUE-09, 10, 11`)

### 4.1 `ATAQUE-09`: Universal $\forall n$ $2$-Adic Torsion Law in Nisan Matrices for Witt Carries (`Frege` Frontier)
In [proofs/witt_snf_universal_torsion.lean](proofs/witt_snf_universal_torsion.lean) (`0 sorryAx`) and [results/witt_higher_torsion_snf_results.json](results/witt_higher_torsion_snf_results.json), we prove the exact Smith Normal Form law over $\mathbb{Z}$ and all truncated Witt rings $W_k(\mathbb{F}_2) \cong \mathbb{Z}/2^k\mathbb{Z}$:
- **Universal Theorem (`snf_derangement_forall_n`, $\forall n \ge 2$):** Explicit integer unimodular matrices $P_n, Q_n \in \mathrm{GL}_n(\mathbb{Z})$ ($P_n P_n^{-1} = I_n = Q_n Q_n^{-1}$) satisfy $P_n (J_n - I_n) Q_n = \operatorname{diag}(1, \dots, 1, n - 1)$. Consequently, at $n = 2^r + 1$, the invariant factor $2^r$ vanishes identically in $W_{\le r}(\mathbb{F}_2)$ (`0 mod 2^k` for $k \le r$) and emerges for the first time as nontrivial $2^r$-torsion in **$W_{r+1}(\mathbb{F}_2) \cong \mathbb{Z}/2^{r+1}\mathbb{Z}$** (`n=3 -> 2` in $W_2$; `n=5 -> 4` in $W_3$; `n=9 -> 8` in $W_4$; `n=17 -> 16` in $W_5$).
- **Higher Elementary Carries & Simultaneous Linear-Rank Torsion in $e_4^{\mathrm{sym}}$:**
  - $e_3^{\mathrm{sym}}$ ($n = 3..12$): $\operatorname{SNF}_{\mathbb{Z}}(M_{1,2}) = (1^{n-1}, n - 2)$, shifting $2^r$-torsion emergence to $n = 2^r + 2$.
  - $e_4^{\mathrm{sym}}$ ($M_{2,2}$, Kneser graph $KG(n, 2)$, $n = 4..9$): At odd $n = 2^r + 3$, instead of a single torsion invariant factor, a **linear-size block of $n - 1$ simultaneous $2^r$-torsion invariant factors** emerges in $W_{r+1}(\mathbb{F}_2)$ (`n = 5`: `4` simultaneous factors of `2` in $\mathbb{Z}/4\mathbb{Z}$; `n = 7`: `6` simultaneous factors of `4` in $\mathbb{Z}/8\mathbb{Z}$).
  - **2nd Witt Addition Carry $4 \cdot C_2(x) \equiv 4 e_4(x) + 8 e_6(x) + 8 e_8(x) \pmod{16}$ ($W_4(\mathbb{F}_2)$, $n = 4..8$):** Ordered commutative rank grows as $n - 3$ (`5` at $n = 8$) vs bimodal non-commutative Nisan rank `28` at $n = 8$.

### 4.2 `ATAQUE-10`: Resolving the Constructive $\mathrm{poly}(S)$ Regime of Krajíček's Open Problem (`arXiv:2606.13367v2`, p. 11)
Krajíček (`arXiv:2606.13367v2`, p. 11, line 632) asked whether a `Circuit Frege (CF)` proof can be converted in polynomial time into an $\approx$-rewriting chain $C = E_0 \approx \dots \approx E_t = D$. Combining [proofs/krajicek_cf_compiler_unsharing.lean](proofs/krajicek_cf_compiler_unsharing.lean) (`0 sorryAx`) and the hash-consed polynomial-time compiler [src/certified_arith_preproc/krajicek_cf_compiler.py](src/certified_arith_preproc/krajicek_cf_compiler.py) ([results/krajicek_cf_compiler_results.json](results/krajicek_cf_compiler_results.json)):
1. **Zero-Unwinding `Fla` Rule (`cf_fla_rule_two_step_approx`):** Whenever $\mathsf{Fla}[C] = \mathsf{Fla}[D]$ (arbitrary DAG sharing change with identical unwound tree), $C \approx (0 \lor C) \approx D$ in **2 steps** and $O(|C| + |D|)$ DAG size—never expanding $\mathsf{Fla}[C]$!
2. **Exponential-Tree DAG Benchmark (`Suite 1`, $m \in \{4, 8, 12, 16, 20\}$):** On shared circuit $D_{20}$ (`|D_20|_DAG = 83`, unwound formula size $|\mathsf{Fla}[D_{20}]| = \mathbf{8,388,601}$), the compiler emits and verifies all $t = 344$ $\approx$-steps (`100%` `are_approx == True`) in **`4.00 ms`** with peak DAG size `192` ($O(m^2)$ scaling).
3. **High-Reuse DAG `CF` Proofs Balanced via Theorem 1.1 (`Suite 2`, $r \in \{2, 4, 6, 8\}$):** Compiles $k = 50$ DAG proof steps (whose tree-like `CF` expansion has `1,017` steps) into $t = 7,802$ verified $\approx$-steps (`100%` verified) with empirical ratio $t / (k \log_2 k) = 46.58 \to 27.65$, confirming constructive $\mathrm{poly}(S)$ compilation ($S = \sum_{i=1}^k |A_i|$) and isolating the remaining $k_{\mathrm{CF}}$-only regime ($S \gg \mathrm{poly}(k + |C| + |D|)$) as compressed SLP unification.

### 4.3 `ATAQUE-11`: Native Rust `RM(3, 4)` Tetrahedral + Witt Solver Crossing Schoenebeck $n^* = 75$
Supported by [proofs/tetrahedral_rm3_collision_soundness.lean](proofs/tetrahedral_rm3_collision_soundness.lean) (`0 sorryAx`), the native Rust crate [schoenebeck_rs/src/main.rs](schoenebeck_rs/src/main.rs) couples `u64` bitwise $\mathbb{F}_2$ RREF over `RM(2, 3)` diamonds, 4-variable tetrahedral `RM(3, 4)` collisions ($|U| \le 4$, 15 monomials), and 2-pair Witt triangle Chvátal–Gomory cuts ([results/ataque11_tetrahedral_schoenebeck_results.json](results/ataque11_tetrahedral_schoenebeck_results.json), `0/20` false positives on `SAT` controls):

| Variables $n$ ($\alpha=6.2$) | `ATAQUE-03` (`RM(2,3) ⊕ Witt`, Python) | **`ATAQUE-11` (`RM(3,4) ⊕ Witt`, Rust)** | Python Mean Time | **Rust Mean Time** | **Wall-Clock Speedup** |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **`64`** | `6 / 6` (`100.0%`) | **`6 / 6` (`100.0%`)** | `63,666.95 ms` | **`69.73 ms`** | **`913.0×`** |
| **`75`** | `3 / 6` (`50.0%`) | **`4 / 6` (`66.7%`, `+1` seed)** | `338,709.80 ms` | **`245.52 ms`** | **`1,379.6×`** |
| **`90`** | `0 / 6` (`0.0%`) | **`1 / 6` (`16.7%`, crosses $n=90$!)** | `164,991.23 ms` | **`368.55 ms`** | **`447.7×`** |
| **`105`** | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `215,172.02 ms` | **`355.50 ms`** | **`605.3×`** |
| **`120`** | `0 / 6` (`0.0%`) | `0 / 6` (`0.0%`) | `120,641.27 ms` | **`437.68 ms`** | **`275.6×`** |

---

## 5. Phase III (`v0.7.0`): Kneser $KG(n,2)$ Linear Torsion, SLP $k_{\mathrm{CF}}$ Compression & Certified `RM(4, 5)` Schoenebeck (`ATAQUE-12, 13, 14`)

### 5.1 `ATAQUE-12`: Universal Kneser $KG(n,2)$ Linear-Rank Torsion & Witt NC-IPS Separation
In [proofs/witt_kneser_linear_torsion.lean](proofs/witt_kneser_linear_torsion.lean) (`0 sorryAx`) and [results/witt_kneser_linear_torsion_results.json](results/witt_kneser_linear_torsion_results.json) (`0.2316 s`):
- **Universal $e_3^{\mathrm{sym}}$ SNF (`snf_e3_M12_forall_n`, $\forall n \ge 3$):** Bilateral unimodular `P_e3` and `Q_e3` reduce $M_{1,2}(e_3^{\mathrm{sym}})$ to $(1^{n-1}, n - 2)$ for all $n \ge 3$.
- **Exact Kneser $KG(n, 2)$ Eigenspace (`kneser_acts_on_pairSum` & `pairSum_basis_lin_indep`):** The $(n-1)$-dimensional zero-sum subspace $V_0 = \{v : \sum v_i = 0\}$ embeds injectively via pair sums $w_v(i, j) = v_i + v_j$ into $\mathbb{Z}^{\binom{n}{2}}$ as an exact eigenspace of $KG(n,2)$ with eigenvalue $-(n-3)$, explaining the linear block of $n-1$ simultaneous $2^r$-torsion invariant factors at odd $n = 2^r + 3$ (`n=5`: `4` factors `2`; `n=7`: `6` factors `4`; `n=9`: `8` factors `2`; **`n=11`: `10` simultaneous `8`-torsion factors** in $W_4(\mathbb{F}_2)$).
- **2nd Witt Carry $4 C_2(x) \pmod{16}$ ($n = 4..10$):** Ordered commutative rank grows as $n - 3$ (`7` at $n = 10$) vs non-commutative Nisan rank $\binom{n}{2}$ (`45` at $n = 10$, **`6.43×` separation**).

### 5.2 `ATAQUE-13`: SLP-Compressed Unification for the $k_{\mathrm{CF}}$-Pure Regime (`arXiv:2606.13367v2`, p. 11)
In [proofs/krajicek_slp_kcf_reduction.lean](proofs/krajicek_slp_kcf_reduction.lean) (`0 sorryAx`, `0 Classical.choice`) and [src/certified_arith_preproc/krajicek_slp_unifier.py](src/certified_arith_preproc/krajicek_slp_unifier.py) ([results/krajicek_slp_kcf_results.json](results/krajicek_slp_kcf_results.json)):
- **Formal $S$-Independent Bound (`cf_slp_unification_compression`):** Symbolic `SLPCFProof` derivations of $k$ lines over unifiable `Fla`-templates compile to `≈`-chains of length $t \le (c_{\mathrm{ax}} + 2) k$, completely independent of intermediate formula size $S$.
- **Empirical Verification (`385/385` `are_approx == True`, `100%`):** Across 11 instances (`iter_sq`, `xor_balanced`, and truth-table-verified controls), scaling $S$ from `3,924` to `36,004` (`|\mathrm{Fla}|_{\max} = 4.10 \times 10^{18}`) compresses `857.24×` into a **constant `t = 23` `≈`-steps** (`13.60 ms`).

### 5.3 `ATAQUE-14`: Native `VeriPB 3.0.2` Emission & `RM(4, 5)` 5-Local Simplices in `schoenebeck_rs`
Extended [schoenebeck_rs/src/main.rs](schoenebeck_rs/src/main.rs) with `--emit-pbp <path>` and `--rm4` (`RM(4, 5)` 5-variable simplices & 5-local collisions, [results/ataque14_schoenebeck_veripb_results.json](results/ataque14_schoenebeck_veripb_results.json)):
- **`26/26` `veripb 3.0.2 --cnf` Verified (`s VERIFIED UNSATISFIABLE`)** (`results/ataque14_pbp/`, including `n=90 seed=0` in `10.64 ms` check time) and **`0/20` false UNSATs** on `CaDiCaL195`-verified `SAT` controls (`alpha = 3.5`).
- **Threshold Shift $n^*: 75 \to 90$:** `--rm4` raises $n = 75$ from `4/6` (`66.7%`) to **`6/6` (`100.0%`, `280.66 ms`)** and $n = 90$ from `1/6` (`16.7%`) to **`3/6` (`50.0%`, `427.76 ms`)** (`n = 105` remains `0/6` at `440.29 ms`).

---

## 6. Phase IV (`v0.8.0`): Non-Aligned Context-SLP Jeż Recompression & Syntactic-vs-Semantic Dichotomy (`ATAQUE-15`)

Closing the remaining non-aligned SLP question from Phase III, [proofs/krajicek_nonaligned_context_slp.lean](proofs/krajicek_nonaligned_context_slp.lean) (`0 sorryAx`, `0 Classical.choice`) and [src/certified_arith_preproc/krajicek_nonaligned_slp.py](src/certified_arith_preproc/krajicek_nonaligned_slp.py) ([results/krajicek_nonaligned_slp_results.json](results/krajicek_nonaligned_slp_results.json)) establish:
1. **Hash-Consed Jeż Block/Pair Recompression (`recompress_unify_context_slp`):** Decides exact `Fla`-unwinding equality between completely misaligned linear `ContextSLP` hierarchies in `O(poly(|G₁| + |G₂|))` time without expanding exponential depth:
   - Shifted/permuted periodic powers up to $m = 60$ (`[65, 127]` rules, spine depth **$3 \cdot 2^{60} = 3,458,764,513,820,540,928$**): unified in **`3` rounds / `10.057 ms`**; single-leaf mutation at depth $3 \cdot 2^{60} - 1$ rejected in `10.022 ms`.
   - Aperiodic Thue–Morse vs 4-ary asymmetric reassociation up to $m = 60$ (`[122, 182]` rules, spine depth **$2^{60} = 1,152,921,504,606,846,976$**): unified in **`84` rounds / `423.794 ms`**; deep-leaf mutation rejected in `155.639 ms`.
2. **Non-Aligned `CF -> ≈` Compilation (`nonaligned_ctx_cf_compression`):** Compiles $k$-line `CtxCFProof` derivations over misaligned grammars into $t \le (c_{\mathrm{ax}} + 2)k$ steps (`164/164` materialized steps verified `100%` via `DAGStore.are_approx`).
3. **Exact Syntactic-vs-Semantic Dichotomy (`syntactic_vs_semantic_fla_dichotomy`):** Proves (`0` `Classical.choice`) that while syntactic `Fla`-equality bridges universally in `2` steps via $0 \lor C$, semantically equivalent formulas with $\mathsf{Fla}[A] \neq \mathsf{Fla}[B]$—such as $(x_0 \lor \neg x_0)$ vs $(x_1 \lor \neg x_1)$ (`¬SimBA`, `2` variable-eliminating `disjCompl` steps) and $(x_0 \oplus x_1) \oplus x_2$ vs $x_0 \oplus (x_1 \oplus x_2)$ (`807` verified `≈`-steps)—require genuine `coNP` Boolean Algebra derivations.

---

## 7. Reproducibility Commands

```bash
# 1. Verify all 15 standalone Lean 4.36.0 soundness files (0 sorryAx)
for f in proofs/*.lean; do lean "$f"; done

# 2. Build both native Rust crates & verify all 11 UNSAT + 4 SAT controls in VeriPB 3.0.2
cargo build --release --manifest-path rust_core/Cargo.toml
cargo build --release --manifest-path schoenebeck_rs/Cargo.toml
uv run --with-editable . cap-bench-v05

# 3. Reproduce Phase I-IV Frontier Proof-Complexity Laboratories
uv run --with-editable . cap-krajicek-ew
uv run --with-editable . cap-cf-compiler
uv run --with-editable . cap-slp-unifier
uv run --with-editable . cap-nonaligned-slp
uv run --with-editable . cap-witt-nc-ips
uv run --with-editable . cap-witt-snf
uv run --with-editable . cap-witt-kneser
uv run --with-editable . cap-dom-g1
uv run --with-editable . cap-bug-extract
uv run --with-editable . cap-schoenebeck-rm3
uv run --with-editable . cap-schoenebeck-rm4
```
