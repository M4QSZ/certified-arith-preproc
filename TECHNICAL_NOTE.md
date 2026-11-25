# Technical Note / Preprint Draft: VeriPB-Certified Arithmetic Adder Extraction and Dual Annihilator Preprocessing for Scrambled CNF Formulas

> **Status:** Research Prototype & Technical Note (v0.1). Not peer-reviewed or submitted; intended as a reproducible technical companion and foundation for future SAT / Formal Verification work.

---

## Abstract

Heterogeneous arithmetic equivalence miters (such as comparing a schoolbook/ripple multiplier against a Wallace-tree multiplier) and wire-eliminated disjunctive combinations of pigeonhole and parity constraints pose severe bottlenecks for Conflict-Driven Clause Learning (CDCL) solvers when presented as flat, variable- and polarity-scrambled 3-CNF formulas. Meanwhile, algebraic multiplier verifiers typically operate on gate-level And-Inverter Graphs (AIGs) and emit proofs in algebraic calculi (`PAC`/`LPAC`) separate from pseudo-Boolean proof checkers.

This technical note documents a prototype preprocessing and refutation pipeline operating directly on anonymous 3-CNF formulas:
1. **Blind Arithmetic Adder Extraction & `VeriPB 3.0` Certification:** Recovers deterministic 2-input gates under arbitrary permutations and phase flips, merges congruent outputs, synthesizes integer half-adder and disjoint-carry full-adder equations via bounded-cube Reverse Unit Propagation (RUP) and cutting-planes division, eliminates internal carries via a single sparse rational RREF pass, and logs machine-checked `VeriPB 3.0` proofs for 2-adic/GCD bit-peeling refutations.
2. **Dual Reed–Muller Annihilator Synthesis & Coupled Sparse Macaulay / Cutting Planes:** Identifies hidden nonlinear definitions by lifting local falsification sets to degree-$d$ Reed–Muller coordinates $\mathrm{RM}(d, n)$ with $O(|V|\cdot \dim^2)$ directional Boolean derivative isolation, and couples width-3 diamond collisions, 4-variable petal ideals, sparse $\mathbb{F}_2$ RREF, and monotone guarded clique / pair-carry cutting planes.

Across scrambled `Schoolbook vs Wallace` miters (`6x6` to `16x16` bits), `veripb 3.0.2` validates every generated `.pbp` proof in `37.2 ms`–`400.9 ms`. In a 300s wall-clock comparison against `Kissat 4.0.4` and `CryptoMiniSat 5`, our Python prototype solves `12x12`–`20x20` scrambled multiplier miters (`6.7 s`–`27.8 s`) where both C/C++ solvers time out at `300 s`, and solves a wire-eliminated `PHP_{13}^{12} \vee \mathrm{Tseitin}_{28}` interpolant `73x` faster than `Kissat 4.0.4` (`2.87 s` vs `209.75 s`).

---

## 1. Related Work & Positioning

* **Clausal Congruence Closure:** Biere, Fazekas, Fleury, and Froleyks [1] (*SAT 2024*, integrated in `Kissat 4.0.4`) recover `AND`, `XOR`, and `ITE` gates directly from CNF and merge structurally equivalent outputs. On heterogeneous multipliers (`Schoolbook vs Wallace`), internal partial-product reduction trees differ structurally, leaving no equivalent internal gates to merge at the clausal level before exponential branching occurs.
* **Algebraic Multiplier Verification:** Kaufmann and Biere [2] (*AMulet 2.0*, *TACAS 2021*) verify gate-level multipliers via Gröbner-basis rewriting and adder substitution on AIGs with algebraic `PAC` proof logging. Our prototype complements this line by operating directly on scrambled 3-CNF (without AIG inputs) and logging refutations directly in the `VeriPB 3.0` cutting-planes format.
* **Pseudo-Boolean & Parity Certification:** Gocht and Nordström [3] (*AAAI 2021*) introduced efficient `VeriPB` parity certification using extension variables, and Koops et al. [4] (*CP 2025*) demonstrated practical LP/Farkas and cutting-planes proof logging for pseudo-Boolean optimization (`RoundingSat` / `Sat4j` + `VeriPB` / `CakePB`).
* **Syntactic Auxiliary Variable Reencoding:** Haberlandt, Green, and Heule [5] (*SBVA*, *SAT 2023*) stabilize Bounded Variable Addition using structured tie-breaking on clause-biclique patterns, whereas our dual annihilator synthesis targets nonlinear local constraints where clause patterns lack clean Cartesian bicliques.

---

## 2. Pipeline Overview

### 2.1 `3-CNF -> VeriPB 3.0` Adder Extraction Pseudocode (`veripb_emitter.py`)

```text
Input: Anonymous DIMACS 3-CNF (n_vars, m clauses)
1. Repeat until fixpoint:
     a) Apply unit propagation, binary unit resolution, and 2-XOR equivalences (`rup` + sync).
     b) Scan 3-variable triples for deterministic 2-input gates o = g(u, w).
     c) Merge congruent gate outputs (o1 == +/- o2) via 2-variable cube RUP (`pol ... 2 d`).
2. Extract arithmetic Z-equations from residual gates:
     a) Half-Adder pairs (u, w) -> (s, c): derive u + w - s - 2c = 0 via 7 bounded-cube RUP clauses + `d`.
     b) Disjoint-Carry Full-Adder OR gates (c1, c2) -> cout with !(c1 & c2): derive c1 + c2 - cout = 0.
3. Single sparse rational RREF over Q (prioritizing internal wires with occ >= 2 as pivots):
     Track exact rational linear combination weights `lambda_e` over base equations.
4. Incremental 2-adic / GCD bit-peeling on low-support pivot rows:
     Clear denominators -> compute g = gcd(coeffs).
     - If g > 1 and g does not divide RHS:
         Emit `pol <comb_ge> <g> d`, `pol <comb_le> <g> d`, and sum -> `0 >= 1` (`veripb` UNSAT).
     - Else if 1 or 2 odd coefficients remain:
         Derive implied unit or 2-XOR via `pol ... + 2 d` and propagate until contradiction.
Output: Complete `.pbp` proof ending in `output NONE ; conclusion UNSAT : <cid> ;`
```

### 2.2 Dual Reed–Muller Annihilator Synthesis (`veronese_annihilator.py`)
For nonlinear local clause blocks on support $U$ ($|U| \le 12$), let $F_{\mathrm{bad}} \subseteq \{0,1\}^{|U|}$ be the falsified truth-table points. Lifting $F_{\mathrm{bad}}$ into the degree-$d$ Reed–Muller / Veronese coordinate basis $\nu_d$ and intersecting projected dual annihilators via bitwise Zassenhaus elimination yields candidate polynomial subspaces. Whenever a quasilinear definition $q = P(z \setminus \{u\}) \oplus u$ is obscured by syzygy multiples $f \cdot q$, its directional Boolean derivative satisfies $\Delta_u(f \cdot q) = f$ identically; projecting out degree-$\ge 2$ monomials containing $u$ enforces $\Delta_u P \equiv 1$ and isolates $P = q$ in $O(|V| \cdot \dim^2)$ operations without $2^{\dim}$ enumeration.

### 2.3 Coupled Sparse Macaulay & Guarded Cutting Planes (`macaulay_cp.py`)
Any two distinct 3-clauses over the same 3-variable triple share the identical leading cubic monomial $x_1 x_2 x_3$ in $\mathbb{F}_2[x_1, x_2, x_3]/(x_i^2 - x_i)$, so their difference cancels the cubic term and yields an exact quadratic equation in $\mathrm{RM}(2, 3)$. Our hybrid loop couples collision-prioritized width-3 diamond resolution, 4-variable petal vanishing ideals, and sparse $O(\mathrm{nnz})$ $\mathbb{F}_2$ RREF with monotone modular hyperplanes ($\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5$), guarded clique cutting planes, pair-carry/2-XOR LP rounding, and primal vertex-cut decomposition for wire-eliminated disjunctive formulas.

### 2.4 Two-Layer Verification Scope
* **Finite Rule Soundness (`proofs/rule_soundness.lean`):** 30 theorems checked in Lean 4.36.0 (`decide +revert`, `0` external axioms, `0 sorryAx`) confirm the exact finite boolean/integer validity of the local algebraic and cutting-plane rewrite identities.
* **Per-Instance End-to-End Certification (`veripb 3.0.2`):** Because the Python solver and sparse RREF engine are not themselves formalized in Lean, every arithmetic miter refutation is independently verified from the raw DIMACS `.cnf` by the external Rust checker `veripb 3.0.2`.

---

## 3. Experimental Evaluation (300s Wall-Clock Budget)

All experiments ran on a 4-core Linux machine (`Python 3.12`, `numpy`, `scipy` HiGHS, `python-sat`, `pycryptosat`, `Kissat 4.0.4` compiled with `-O3`, `veripb 3.0.2`). All benchmarks were generated synthetically and subjected to random variable permutation, polarity inversion, and clause shuffling prior to solving.

### Table 1: End-to-End `VeriPB 3.0.2` Certification (`Schoolbook vs Wallace` Scrambled 3-CNF Miters)

| Scrambled Instance | Vars | Clauses | `.pbp` Lines | Solve + Emit (Python) | `veripb 3.0.2` Check | Verdict |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `Scrambled_Miter_06x06` | `369` | `1,174` | `6,135` | `532.4 ms` | **`37.2 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_08x08` | `685` | `2,206` | `11,872` | `1,641.2 ms` | **`43.9 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_10x10` | `1,097` | `3,558` | `19,406` | `3,524.4 ms` | **`87.8 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_12x12` | `1,605` | `5,230` | `28,793` | `6,483.2 ms` | **`213.8 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_16x16` | `2,909` | `9,534` | `53,042` | `28,230.8 ms` | **`400.9 ms`** | `s VERIFIED UNSATISFIABLE` |

### Table 2: 300s Wall-Clock Comparison vs `Kissat 4.0.4` & `CryptoMiniSat 5`

| Scrambled Benchmark (`.cnf`) | Vars / Clauses | Ours (Python, 0-Branch) | `Kissat 4.0.4` (`-O3` C) | `CryptoMiniSat 5` (C++) | `RoundingSat` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `Miter_Mult_12x12_Scrambled` | `1,605 / 5,230` | **`UNSAT` (`6,722.8 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` | `N/A` |
| `Miter_Mult_16x16_Scrambled` | `2,909 / 9,534` | **`UNSAT` (`12,999.4 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` | `N/A` |
| `Miter_Mult_20x20_Scrambled` | `4,597 / 15,118` | **`UNSAT` (`27,786.8 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` | `N/A` |
| `WireElim_OR_s1s2_PHP13_12_Tseitin28` | `3,157 / 5,196` | **`UNSAT` (`2,874.7 ms`)** | `UNSAT` (`209,745.2 ms`) | `TIMEOUT_300s` | `N/A` |
| `Lifted_PHP65_o_Keccak4L_Scrambled` | `17,373 / 21,284` | `UNSAT` (`3,885.2 ms`) | **`UNSAT` (`151.6 ms`)** | `UNSAT` (`213.4 ms`) | `N/A` |
| `Shifted_Cubic_Sponge_Miter_Scrambled` | `2,615 / 3,264` | `UNSAT` (`235.3 ms`) | **`UNSAT` (`144.7 ms`)** | `UNSAT` (`252.7 ms`) | `N/A` |
| `Goldreich_XORMAJ3_n28_m36_Scrambled` | `1,180 / 1,728` | `FEASIBLE` *(cap)* | **`UNSAT` (`51.5 ms`)** | `UNSAT` (`116.4 ms`) | `N/A` |

---

## 4. Limitations & Transparency

1. **Synthetic Benchmarks Only:** All benchmarks in Tables 1 and 2 come from the synthetic generators in `benchmarks.py`. Evaluation on external SAT Competition / industrial hardware miter benchmarks is left as future work.
2. **Where Native C CDCL Solvers Win:** On smaller lifted pigeonhole cores (`PHP_6^5`), small cubic ring miters, and `Goldreich XOR-MAJ3` at $n=28$ (where our unrolled `(1,1)` pre-pass hits its `max_active_vars=48` cap and the outer loop skips circuits $>500$ vars), `Kissat 4.0.4` and `CryptoMiniSat 5` solve the instances in `51`–`253 ms`. This motivates positioning our engine as a **fast-path certified preprocessor / portfolio component** ahead of CDCL rather than a standalone replacement.
3. **`RoundingSat` Availability:** `RoundingSat` could not be compiled in this environment due to missing `cmake` and `Boost >= 1.70`; `benchmark_solvers.py` supports `--roundingsat-bin` when installed.
4. **Scope of `rule_soundness.lean` vs `VeriPB`:** The 30 Lean 4 theorems verify finite local rewrite rules via `decide +revert` rather than asymptotic $\forall n$ correctness of the Python implementation; end-to-end refutation soundness is instead guaranteed per instance by `veripb 3.0.2`.
5. **Small-Scale Random 3-SAT Observation:** In earlier exploratory runs on random 3-SAT UNSAT ($\alpha = 6.2$, $n=64$), coupling degree-3 sparse Macaulay with guarded cutting planes yielded `8/8` zero-branch refutations (`13.6 s`) where each component alone achieved `0/8` (`16/16` SAT checks passed). This is noted strictly as a small-$n$ empirical observation; standard CDCL solves $n=64$ in milliseconds and asymptotic expansion lower bounds apply as $n$ grows.
6. **AI-Assisted Development Note:** This research prototype, Lean 4 rule-soundness suite, and documentation were developed with AI-assisted coding and search workflows, and verified directly via local execution of `lean`, `veripb 3.0.2`, `kissat 4.0.4`, and `pycryptosat`.

---

## 5. Portable Reproducibility Commands

```bash
# 1. Verify all 30 finite local rewrite rules in Lean 4 (0 axioms)
lean proofs/rule_soundness.lean

# 2. Emit & check VeriPB 3.0.2 proofs for 6x6..16x16 scrambled multiplier miters
uv run --with-editable . python -m certified_arith_preproc.veripb_emitter --bits 6 8 10 12 16

# 3. Run the 300s wall-clock comparison against Kissat 4.0.4 and CryptoMiniSat 5
uv run --with-editable '.[benchmarks]' python -m certified_arith_preproc.benchmark_solvers --timeout 300

# Or run all three steps via:
./scripts/reproduce.sh --timeout 300
```

---

## References

1. Armin Biere, Katalin Fazekas, Mathias Fleury, and Nils Froleyks. *Clausal Congruence Closure*. In 27th International Conference on Theory and Applications of Satisfiability Testing (SAT 2024), LIPIcs Vol. 305, pp. 6:1–6:25. DOI: `10.4230/LIPIcs.SAT.2024.6`.
2. Daniela Kaufmann and Armin Biere. *AMulet 2.0 for Verifying Multiplier Circuits*. In Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2021), LNCS, pp. 357–364. DOI: `10.1007/978-3-030-72013-1_19`.
3. Stephan Gocht and Jakob Nordström. *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs*. In Proceedings of the AAAI Conference on Artificial Intelligence (AAAI 2021), Vol. 35(5), pp. 3768–3777. DOI: `10.1609/aaai.v35i5.16494`.
4. Wietze Koops, Daniel Le Berre, Magnus O. Myreen, Jakob Nordström, Andy Oertel, Yong Kiam Tan, and Marc Vinyals. *Practically Feasible Proof Logging for Pseudo-Boolean Optimization*. In 31st International Conference on Principles and Practice of Constraint Programming (CP 2025), LIPIcs, Art. 21. DOI: `10.4230/LIPIcs.CP.2025.21`.
5. Andrew Haberlandt, Harrison Green, and Marijn J. H. Heule. *Effective Auxiliary Variables via Structured Reencoding*. In 26th International Conference on Theory and Applications of Satisfiability Testing (SAT 2023), LIPIcs, Art. 11. DOI: `10.4230/LIPIcs.SAT.2023.11`.
