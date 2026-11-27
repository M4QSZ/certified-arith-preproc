# Technical Note / Preprint Draft (v0.2): Blind `VeriPB 3.0`-Certified Disjunctive Interpolants and Universal Lean 4 Soundness

> **Status:** Research Prototype & Technical Note v0.2 — Not peer-reviewed; machine-verified via Lean 4.36.0 and VeriPB 3.0.2.

---

## Abstract

Wire-eliminated disjunctive formulas of the form $\mathrm{PHP}_p^h \vee_S \mathrm{Tseitin}_G$—where a small selector cut $S$ switches between a Pigeonhole Principle core and a Tseitin parity core over 3-regular graphs, and long guarded clauses are split into anonymous, variable- and polarity-scrambled 3-CNF—defeat both state-of-the-art Conflict-Driven Clause Learning (CDCL) solvers and CDCL+XOR solvers. Pure CDCL (`Kissat 4.0.4`, `CaDiCaL 1.9.5`) faces exponential resolution lower bounds on both $\mathrm{PHP}$ and $\mathrm{Tseitin}$, while CDCL+XOR (`CryptoMiniSat 5`) is blinded by `(1,1)` wire-elimination chains and still collapses on the $\mathrm{PHP}$ branch.

This technical note documents `v0.2.0` of `certified-arith-preproc`, introducing a blind disjunctive `VeriPB 3.0` proof-emitting calculus (`veripb_interpolant.py`) paired with a universal $\forall n$ formalization in Lean 4.36.0 (`proofs/disjunctive_interpolant_soundness.lean`):
1. **End-to-End `VeriPB 3.0.2` Certification:** Achieves `13/13` `s VERIFIED UNSATISFIABLE` proofs across $|S| \in \{0, 2, 3\}$ (11 scaling/multi-selector instances and 2 standalone $|S|=0$ ablations), scaling up to `16,656` variables and `29,664` clauses (`PHP24_23_OR2_Tseitin52`) in `3,089.9 ms` total (`2,972.8 ms` Python emit + `117.1 ms` `veripb 3.0.2` check) where `Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5` all time out at `60 s`.
2. **Zero-False-Positive SAT Rejection:** Rejects `4/4` satisfiable control instances (verified `SAT` by `CaDiCaL 1.9.5`) with zero false positives.
3. **Universal $\forall n$ Lean 4.36.0 Soundness:** Mechanically verifies 17 declarations across 7 theorem groups with `0 sorryAx` and kernel axioms only, closing Limitation #4 of Technical Note v0.1 for the disjunctive calculus.

---

## 1. Related Work & Proof-Complexity Positioning

* **Feasible Interpolation & Monotone vs. Non-Monotone Separations:** Pudlák (*JSL 1997*) [1] and Krajíček (*JSL 1997*) [2] established feasible interpolation for Resolution and Cutting Planes, showing that refutations of split formulas $A(x, z) \wedge B(y, z)$ yield small monotone circuits separating the projections when shared variables $z$ appear positively in one half and negatively in the other. Subsequent work by Hrubeš and Pudlák (*FOCS 2017*) [3] and Garg, Göös, Kamath, and Sokolov (*STOC 2018*) [4] sharpened exponential separations between monotone and non-monotone / dag-like Cutting Planes and communication protocols.
* **Why Both CDCL and CDCL+XOR Collapse on Wire-Eliminated $\mathrm{PHP}_p^h \vee_S \mathrm{Tseitin}_G$:**
  * *Clausal Congruence & Resolution (`Kissat 4.0.4`, `CaDiCaL 1.9.5`):* `Kissat 4.0.4` integrates *SAT 2024* clausal congruence closure [5] to merge structurally equivalent `AND`/`XOR`/`ITE` gates. However, $\mathrm{PHP}_p^h$ and $\mathrm{Tseitin}_G$ are both exponentially hard for Resolution, and their heterogeneous disjunction shares no equivalent internal gates to merge.
  * *Gauss-Jordan XOR (`CryptoMiniSat 5`):* While `CryptoMiniSat 5` solves standalone $\mathrm{Tseitin}_{140}$ on 3-regular expanders in `1,854.25 ms` via Gaussian elimination over $\mathbb{F}_2$, it collapses on `PHP_p^h OR_S Tseitin_G` for two reasons: (i) `(1,1)` Tseitin wire-elimination splits long selector-guarded clauses into 3-CNF chains, obscuring the underlying parity supports behind auxiliary variables; and (ii) even after branching on $S$, the $\mathrm{PHP}$ fibers contain no XOR structure, forcing `CryptoMiniSat 5` back into exponential CDCL search.
* **Pseudo-Boolean & Parity Certification:** Gocht and Nordström (*AAAI 2021*) [6] introduced compact `VeriPB` parity refutations using extension variables and witness-based redundancy, later generalized in `VeriPB 3.0` (Bogaerts et al.) [7] with `pol`, `red`, and `rup` rules. Szeider (*PBLean / pb-catcher*, `arXiv:2602.08692`) [8] formalized pseudo-Boolean proof checking in Lean. Our work complements this ecosystem by emitting `VeriPB 3.0` certificates directly from anonymous scrambled 3-CNF without a priori knowledge of the separator $S$, the $\mathrm{PHP}$ cliques, or the $\mathrm{Tseitin}$ parity equations.

---

## 2. Blind Disjunctive `VeriPB 3.0` Calculus (`veripb_interpolant.py`)

Given an anonymous DIMACS 3-CNF $(V, \mathcal{C})$, `certify_disjunctive_interpolant_veripb` executes five deterministic stages to emit a complete `.pbp` proof ending in `output NONE ; conclusion UNSAT : <contra_id> ;`.

### 2.1 Logged `(1,1)`-Chain Unrolling (`_unroll_11_chains_logged`)
Tseitin splitting variables introduced when flattening long guarded clauses into 3-CNF occur exactly once positively and once negatively. `_unroll_11_chains_logged` iteratively identifies non-protected variables $v \notin \mathrm{protected\_vars}$ with occurrence count $(1, 1)$ across disjoint clause indices $(pi, ni)$ and logs each resolution step directly in `VeriPB 3.0` cutting planes:
* `pol id_p id_n + s ;` when the resolvent halves share literals (applying saturation `s`), or
* `pol id_p id_n + ;` when the halves are literal-disjoint.

This unrolling is run **globally** before separator discovery (exposing the true primal graph) and **fiber-locally** after projecting onto each assignment $b \in \{0,1\}^{|S|}$ (with `protected_vars = set(cut_vars)` so separator literals remain intact as uniform guards).

### 2.2 Pigeonhole-Anchored $O(|V| \cdot \deg)$ Primal Vertex-Cut Discovery (`discover_primal_vertex_cut`)
To recover an unknown separator $S$ ($1 \le |S| \le \text{max\_cut}$, default $\text{max\_cut} = 6$) without exponential search:
1. Build the primal variable co-occurrence graph $G_{\mathrm{primal}} = (V, E)$ over the globally unrolled clauses and sort vertices by `(len(adj[v]), v)`.
2. By the Pigeonhole Principle, among the first $\text{max\_cut} + 1$ minimum-degree anchor vertices, at least one anchor $u$ lies outside any separator $S$ of size $\le \text{max\_cut}$.
3. For each non-neighbor $v \notin N(u)$, form the candidate cut $S_{\mathrm{cand}} = N(u) \cap N(v)$. Whenever $1 \le |S_{\mathrm{cand}}| \le \text{max\_cut}$, a fast BFS from $u$ in $G_{\mathrm{primal}} - S_{\mathrm{cand}}$ checks whether $S_{\mathrm{cand}}$ disconnects $G_{\mathrm{primal}}$ into $\ge 2$ components each of size $\ge 3$.

If no cut is found (e.g., standalone `PHP` or `Tseitin`), the solver falls back cleanly to $|S| = 0$ (empty guard $G = 0$).

### 2.3 Guarded Chvátal–Gomory Clique AMO Induction & `PHP` Guard Derivation (`_try_certify_guarded_php`)
Within a projected fiber where every clause carries the uniform guard $G = \sum_{g \in \mathrm{guard\_lits}} g$, `_try_certify_guarded_php` detects binary guarded clauses $G + \bar{\ell}_1 + \bar{\ell}_2 \ge 1$ (`amo_cid`) and disjoint At-Least-One (ALO) clauses (trying `min_alo_len` $\in \{3, 2\}$), partitioning the ALO literals into cliques $Q_1, \dots, Q_h$ with $p > h$:
* **Inductive Clique AMO:** For each clique $Q_j$ of size $m_q \ge 2$, starting from $I_2 = \mathrm{amo\_cid}[(q_0, q_1)]$, each step $m \in \{2, \dots, m_q - 1\}$ combines the previous inductive inequality $I_m$ with the $m$ pairwise clauses $M_{i, m+1}$ and applies Chvátal–Gomory division (`m d`):
  $$\frac{(m - 1) I_m + \sum_{i=0}^{m-1} M_{i, m+1}}{m} \;\longrightarrow\; m G + \sum_{i=0}^{m} \bar{q}_i \ge m.$$
* **Guard Derivation (0 Extension Variables):** Summing all $p$ guarded ALO clauses and all $h$ clique AMO inequalities cancels every pigeon-hole literal via $\ell + \bar{\ell} = 1$, leaving $c_{\mathrm{guard}} \cdot G \ge p - h \ge 1$ where $c_{\mathrm{guard}} = p + \sum_{j=1}^h (m_{Q_j} - 1)$ (for $m_{Q_j} \ge 2$). A single division (`c_guard d`) derives $G \ge 1$ (or $0 \ge 1$ if $G$ is empty) with **0 extension variables**.

### 2.4 Guarded $\mathrm{MAJ}_3$ `red`-Witness Parity Linearization (`_try_certify_guarded_parity`)
For parity fibers, `_try_certify_guarded_parity` groups guarded clauses of width $k \in \{1, 2, 3, 4\}$ by variable support and identifies full parity equations $\bigoplus_{j=1}^k x_{v_j} = \mathrm{rhs}$.
* **Lazy $\mathbb{F}_2$ RREF Witness Emission:** A sparse $\mathbb{F}_2$ RREF pass tracks row-combination bitmasks `comb` over the extracted equations. Only when an inconsistent combination `unsat_mask` ($\mathbf{0} = 1$) is found are `red` witnesses and `pol` steps emitted, and **only** for the equations in `unsat_mask`.
* **Guarded $\mathrm{MAJ}_3$ Linearization (`_realize_parity3_bounds`):** For $k = 3$ (and for $k = 4$ by splitting $v_1 \oplus v_2 \oplus v_3 \oplus v_4 = \mathrm{rhs}$ via a fresh witness $z \leftrightarrow v_1 \oplus v_2$ defined by 4 unconditional `red` clauses), a fresh witness $w = \mathrm{MAJ}_3(y_1, y_2, y_3)$ satisfies the exact integer identity
  $$y_1 + y_2 + y_3 - 2\,\mathrm{MAJ}_3(y_1, y_2, y_3) = y_1 \oplus y_2 \oplus y_3.$$
  Emitting two `red` constraints:
  * $R_1$: $y_1 + y_2 + y_3 + 2\bar{w} \ge 2 \quad (: x_w \to 0)$,
  * $R_2$: $\bar{y}_1 + \bar{y}_2 + \bar{y}_3 + 2w \ge 2 \quad (: x_w \to 1)$,
  and combining $R_2$ with the four guarded forbidden-point clauses $K_1, K_2, K_3, K_4$ via $L_i = \lceil (R_2 + K_i)/2 \rceil$ ($i \in \{1,2,3\}$) and
  $$\left\lceil \frac{2(L_1 + L_2 + L_3) + K_4}{3} \right\rceil \;\longrightarrow\; 3G + \bar{y}_1 + \bar{y}_2 + \bar{y}_3 + 2w \ge 3$$
  yields paired guarded bounds $U^+$ (from $R_1$, guard coeff $0$) and $U^-$ (guard coeff $3$ when $G$ is non-empty).
* **Even-Coefficient CG Halving Cancellation (`sum_and_halve`):** Summing the selected $U^+$ inequalities (and separately $U^-$), weakening by $G \ge 0$ if the total guard coefficient is odd, and dividing by `2 d` cancels all internal variables when the two halves are added, leaving $m_{\mathrm{tot}} G \ge 1$ which divides by `tot_m d` to yield $G \ge 1$.

### 2.5 Boolean Cube Halving Reassembly (`collapse_cube`)
Once every fiber $b \in \{0, 1\}^{|S|}$ is certified with its guard clause $D_b$ (`guard_lits >= 1`), `collapse_cube` performs a binary tree of $2^{|S|} - 1$ cutting-planes halving steps:
$$\text{pol } \mathrm{id}_0\;\mathrm{id}_1\;\texttt{+}\;\texttt{2}\;\texttt{d}\;\texttt{;}$$
canceling one separator variable per level until `0 >= 1` (`contra_id`) is derived at the root.

---

## 3. Universal $\forall n$ Formalization in Lean 4.36.0 (`proofs/disjunctive_interpolant_soundness.lean`)

Limitation #4 of Technical Note v0.1 noted that `proofs/rule_soundness.lean` verified 30 finite local rewrite rules via `decide +revert` rather than universal $\forall n$ soundness. For the disjunctive calculus, `proofs/disjunctive_interpolant_soundness.lean` closes this gap with a standalone Lean 4.36.0 formalization (zero Mathlib imports, zero external axioms, `0 sorryAx`) across **7 theorem groups** (**17 `#print axioms`-checked declarations**):

| Group | Key Declarations | Universal Scope |
| :--- | :--- | :--- |
| **Helpers** | `b2n_not`, `b2n_add_not` | Boolean-to-`Nat` embedding `b2n` |
| **Theorem 1** | `chain11_pb_cancel_sound`, `chain11_unroll_steps_sound` | Inductive soundness of `(1,1)`-chain unrolling for arbitrary `vs : List Bool` |
| **Theorem 2** | `guarded_amo_cg_step_sound`, `cg_ceiling_div_id`, `guarded_amo_cg_G0_xnew_true`, `guarded_amo_step_full` | Guarded AMO Chvátal–Gomory step and $\lceil (m^2 - m + 1)/m \rceil = m$ for all `m ≥ 1` |
| **Theorem 3** | `guarded_php_unsat_derives_guard` | Universal `∀ p h` (`h < p`) Pigeonhole guarded Cutting-Planes derivation of `G ≥ 1` |
| **Theorem 4** | `maj3_witness_exact_xor_z`, `parity3_red_witness_false`, `parity3_red_witness_true`, `guarded_parity3_veripb_sound` | Exact `maj3` decomposition, `red` witness validity, and guarded 3-XOR CP derivation |
| **Theorem 5** | `even_coeff_cg_halving_cancel_sound` | Even-coefficient CG halving and cancellation over `Int` |
| **Theorem 6** | `tseitin_graph_handshaking_parity` | Tseitin graph handshaking parity invariance over arbitrary `edges : List (Nat × Nat × Bool)` on `n` vertices |
| **Theorem 7** | `cubeGuardSat_self`, `boolean_cube_halving_unsat` | Boolean cube halving unsatisfiability over `Fin k` for all `k : Nat` |

---

## 4. Experimental Evaluation (60s 4-Solver Suite + 300s Cross-Reference)

All timing results below are taken verbatim from [results/interpolant_benchmark_results.json](results/interpolant_benchmark_results.json) under a `60.0 s` wall-clock timeout comparing our Python prototype (`veripb_interpolant.py` + `veripb 3.0.2`) against `Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5`.

### Table 1: Scaling & Multi-Selector Disjunctive Interpolants (`|S| = 2` and `|S| = 3` Random 3-Regular Expanders)

| Instance | Vars / Clauses | `|S|` | `.pbp` Lines (`w`) | Ours (Emit + `veripb` = Total) | `Kissat 4.0.4` | `CaDiCaL 1.9.5` | `CryptoMiniSat 5` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `PHP07_06_OR2_Tseitin14` | `674 / 1,008` | `2` | `878` (`28`) | **`32.77 ms`** (`24.4 + 8.37`) | `154.9 ms` | `179.33 ms` | `203.81 ms` |
| `PHP08_07_OR2_Tseitin16` | `922 / 1,408` | `2` | `1,168` (`32`) | **`64.78 ms`** (`53.78 + 11.0`) | `263.35 ms` | `446.17 ms` | `240.74 ms` |
| `PHP10_09_OR2_Tseitin20` | `1,592 / 2,520` | `2` | `1,934` (`40`) | **`138.35 ms`** (`114.8 + 23.55`) | `8,126.79 ms` | `8,649.59 ms` | `986.64 ms` |
| `PHP11_10_OR2_Tseitin22` | `2,026 / 3,256` | `2` | `2,422` (`44`) | **`195.54 ms`** (`162.55 + 32.99`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP12_11_OR2_Tseitin24` | `2,534 / 4,128` | `2` | `2,988` (`48`) | **`278.52 ms`** (`258.76 + 19.76`) | `10,608.28 ms` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP13_12_OR2_Tseitin28` | `3,157 / 5,196` | `2` | `3,694` (`56`) | **`300.90 ms`** (`278.39 + 22.51`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP16_15_OR2_Tseitin36` | `5,496 / 9,312` | `2` | `6,264` (`72`) | **`523.04 ms`** (`489.45 + 33.59`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP20_19_OR2_Tseitin44` | `10,052 / 17,536` | `2` | `11,156` (`88`) | **`1,499.29 ms`** (`1,433.26 + 66.03`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP24_23_OR2_Tseitin52` | `16,656 / 29,664` | `2` | `18,160` (`104`) | **`3,089.92 ms`** (`2,972.84 + 117.08`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP12_11_OR3_Expander30` | `8,820 / 12,360` | `3` | `10,124` (`120`) | **`727.43 ms`** (`665.51 + 61.92`) | `35,968.12 ms` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `PHP14_13_OR3_Expander36` | `13,419 / 18,964` | `3` | `15,124` (`144`) | **`1,353.55 ms`** (`1,252.8 + 100.75`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |

*300s Cross-Reference (Technical Note v0.1):* On `WireElim_OR_s1s2_PHP13_12_Tseitin28` (`3,157` vars / `5,196` clauses), `Kissat 4.0.4` required `209,745.2 ms` while `CryptoMiniSat 5` still hit `TIMEOUT_300s`. Our specialized `veripb_interpolant.py` + `veripb 3.0.2` pipeline certifies the same size class (`PHP13_12_OR2_Tseitin28`) in `300.90 ms`.

### Table 2: Orthogonal `|S| = 0` Standalone Ablation

| Instance | Vars / Clauses | `|S|` | `.pbp` Lines (`w`) | Ours (Emit + `veripb` = Total) | `Kissat 4.0.4` | `CaDiCaL 1.9.5` | `CryptoMiniSat 5` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `Standalone_PHP14_13_Scrambled` | `322 / 1,337` | `0` | `302` (`0`) | **`740.52 ms`** (`734.04 + 6.48`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Standalone_Tseitin140_Expander_Scrambled` | `210 / 560` | `0` | `848` (`140`) | **`34.50 ms`** (`25.66 + 8.84`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `UNSAT` (`1,854.25 ms`) |

This ablation empirically isolates the dual bottleneck: `CryptoMiniSat 5` solves pure `Tseitin_140` via Gauss-Jordan elimination (`1,854.25 ms`) while `Kissat` and `CaDiCaL` time out, yet `CryptoMiniSat 5` also times out once `Tseitin` is disjoined with `PHP` behind wire-eliminated selector guards.

### Table 3: SAT Soundness Controls (`4/4` Rejected, 0 False Positives)

| Instance | Vars / Clauses | `CaDiCaL 1.9.5` | Ours (`veripb_interpolant.py`) | Diagnostic |
| :--- | :---: | :---: | :---: | :--- |
| `SAT_PHP08_08_OR2_Tseitin16_odd` | `1,026 / 1,568` | `SAT` (`63.59 ms`) | **Rejected** (`57.13 ms`) | `Fiber (0, 1) on separator S=[222, 587] is FEASIBLE or uncertified` |
| `SAT_PHP08_07_OR2_Tseitin16_even` | `922 / 1,408` | `SAT` (`64.27 ms`) | **Rejected** (`34.40 ms`) | `Fiber (0, 0) on separator S=[144, 394] is FEASIBLE or uncertified` |
| `SAT_PHP10_10_OR3_Expander24_odd` | `5,921 / 8,216` | `SAT` (`108.55 ms`) | **Rejected** (`183.36 ms`) | `Fiber (0, 0, 1) on separator S=[1749, 3588, 4652] is FEASIBLE or uncertified` |
| `SAT_Standalone_Tseitin24_even` | `36 / 96` | `SAT` (`60.17 ms`) | **Rejected** (`3.34 ms`) | `Fiber () on separator S=[] is FEASIBLE or uncertified` |

---

## 5. Honest Limitations & Open Problems

1. **Bounded Cut Width ($|S| \le 6$):** Enumerating every fiber $b \in \{0, 1\}^{|S|}$ incurs a $2^{|S|}$ factor in proof size and runtime. While effective for small selector cuts ($|S| \in \{0, 2, 3\}$), scaling to wide separators ($|S| \gg 6$) would require recursive or treewidth-bounded cut decomposition.
2. **Non-Decomposable Expander-Entangled Constraints:** Formulas whose primal graph is a single high-expansion component without small vertex cuts—such as `Goldreich_XORMAJ3` PRG instances—cannot be split by `discover_primal_vertex_cut` and fall outside the current disjunctive PHP/parity engines.
3. **Synthetic Benchmarks Only:** All benchmarks in Tables 1–3 are generated synthetically (`gen_wire_eliminated_php_tseitin`, `gen_multiguard_php_tseitin_3cnf`, and standalone generators in `benchmark_interpolants.py`) and scrambled. Evaluation on external SAT Competition / industrial hardware-software benchmarks remains future work.

---

## 6. Portable Reproducibility Commands

```bash
# 1. Verify the universal ∀n Lean 4.36.0 soundness suite (17 declarations, 0 sorryAx)
lean proofs/disjunctive_interpolant_soundness.lean

# 2. Emit & verify VeriPB 3.0.2 proofs for scrambled disjunctive interpolants (|S| ∈ {2, 3})
uv run --with-editable . python -m certified_arith_preproc.veripb_interpolant \
  --out-dir results/interpolant_proofs \
  --json-out results/interpolant_veripb_results.json

# 3. Run the 60s 4-solver benchmark suite (scaling + ablations + SAT controls)
uv run --with-editable '.[benchmarks]' python -m certified_arith_preproc.benchmark_interpolants \
  --timeout 60 \
  --cnf-dir results/interpolant_bench_cnf \
  --pbp-dir results/interpolant_bench_pbp \
  --json-out results/interpolant_benchmark_results.json

# Or run the full v0.1 + v0.2 verification suite via:
./scripts/reproduce.sh --timeout 300
```

---

## References

1. Pavel Pudlák. *Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations*. Journal of Symbolic Logic (JSL), 62(3):981–998, 1997.
2. Jan Krajíček. *Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic*. Journal of Symbolic Logic (JSL), 62(2):457–486, 1997.
3. Pavel Hrubeš and Pavel Pudlák. *Random Formulas, Monotone Circuits, and Interpolation*. In 58th IEEE Annual Symposium on Foundations of Computer Science (FOCS 2017), pp. 121–131.
4. Ankit Garg, Mika Göös, Pritish Kamath, and Dmitry Sokolov. *Monotone Circuit Lower Bounds from Resolution*. In 50th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2018), pp. 902–911.
5. Armin Biere, Katalin Fazekas, Mathias Fleury, and Nils Froleyks. *Clausal Congruence Closure*. In 27th International Conference on Theory and Applications of Satisfiability Testing (SAT 2024), LIPIcs Vol. 305, pp. 6:1–6:25.
6. Stephan Gocht and Jakob Nordström. *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs*. In Proceedings of the AAAI Conference on Artificial Intelligence (AAAI 2021), Vol. 35(5), pp. 3768–3777.
7. Bart Bogaerts, Stephan Gocht, Ciaran McCreesh, and Jakob Nordström. *Certified Dominance and Symmetry Breaking for Combinatorial Optimisation* (`VeriPB 3.0`). Journal of Artificial Intelligence Research (JAIR), 2023.
8. Stefan Szeider. *PBLean / pb-catcher: Formally Verified Pseudo-Boolean Proof Checking in Lean*. `arXiv:2602.08692`, 2026.
