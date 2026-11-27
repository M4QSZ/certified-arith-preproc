# certified-arith-preproc (`v0.8.0`)

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean%204.36.0-15%20suites%20%C2%B7%200%20sorryAx-brightgreen.svg)](proofs/krajicek_nonaligned_context_slp.lean)
[![VeriPB](https://img.shields.io/badge/VeriPB-3.0.2%20verified%20%28pol%2Bred%2Bdom%29-brightgreen.svg)](results/ataque14_schoenebeck_veripb_results.json)
[![Rust](https://img.shields.io/badge/Rust-1.100%2B%20%28v0.7%20crates%29-orange.svg)](rust_core/src/main.rs)
[![Python](https://img.shields.io/badge/Python-3.10%2B-blue.svg)](pyproject.toml)

A research prototype for **`VeriPB 3.0`-certified blind arithmetic preprocessing** (`v0.1`–`v0.8`: `Z`-adder Hensel peeling, disjunctive vertex-cut interpolants, higher-order Veronese $\mathrm{RM}(d, n)$, local-intersection Zassenhaus gadget inversion on lifted CNFs up to `356,789` variables, and binomial Macaulay PRG lifts) alongside **formal & computational frontier proof-complexity laboratories** (`Schoenebeck` random 3-SAT phase transition & native `VeriPB`-certified Rust `RM(4,5)` solver shifting $n^*$ from `75` to `90`, complete polynomial-time resolution & syntactic-vs-semantic dichotomy of Krajíček's `arXiv:2606.13367v2` circuit-rewriting system $\approx$ across DAGs, aligned SLPs, and non-aligned Context-SLPs via Jeż recompression up to depth $3.46 \times 10^{18}$, universal $\forall n$ $2$-adic torsion laws in Kneser $KG(n,2)$ & Witt rings $W_k(\mathbb{F}_2)$, `VeriPB 3.0` dominance $G_1$, and `arXiv:2611.08305` constructive bug extraction).

### Standalone Publication-Ready Papers (`papers/`)
1. **[Paper 1 — Certified Blind Preprocessing (`VeriPB 3.0` & `RM(d,n)`)](papers/PAPER_1_VERIPB_BLIND_ARITH_VERONESE.md):** *VeriPB 3.0-Certified Blind Witt–Hensel Peeling, Veronese Annihilators, and Local-Intersection Zassenhaus Preprocessing for Scrambled Hybrid CNFs*.
2. **[Paper 2 — Krajíček's `CF -> ≈-Chain` Dichotomy (`arXiv:2606.13367v2`)](papers/PAPER_2_KRAJICEK_CF_APPROX_COMPLETE_DICHOTOMY.md):** *Polynomial-Time Recompression and Exact Syntactic-vs-Semantic Dichotomy for Krajíček's Circuit-Rewriting Problem (`CF -> ≈-Chains`)*.
3. **[Paper 3 — Witt–Kneser $2^r$-Adic Torsion (`NC-IPS` / `Frege`)](papers/PAPER_3_WITT_KNESER_2ADIC_TORSION_NC_IPS.md):** *Universal 2-Adic Smith Normal Form and Kneser $KG(n,2)$ Linear-Rank Torsion in Bimodal Nisan Matrices over Truncated Witt Rings $W_k(\mathbb{F}_2)$*.

### Technical Notes & Attack Queue
* **Attack Roadmap & Completed Queue (`15/15` Fase I–IV):** [RUTAS_ATAQUE_P_VS_NP.md](RUTAS_ATAQUE_P_VS_NP.md)
* **Technical Note v0.8 (Unified Rust Lifted Zassenhaus, Kneser Witt Torsion, Complete Krajíček SLP Dichotomy & Certified `RM(4,5)` Schoenebeck):** [TECHNICAL_NOTE_V05_AND_FRONTIER_LABS.md](TECHNICAL_NOTE_V05_AND_FRONTIER_LABS.md)
* **Paper / Technical Note v0.4 (Higher-Order `RM(d<=4)`, $K_5$ Cubic Homology & Native Rust Engine):** [TECHNICAL_NOTE_HIGHER_VERONESE_RUST.md](TECHNICAL_NOTE_HIGHER_VERONESE_RUST.md)
* **Paper / Technical Note v0.3 (Degree-2 Veronese & $\mathbb{F}_2$-Homological Goldreich PRG Expanders):** [TECHNICAL_NOTE_VERONESE_HOMOLOGICAL_PRG.md](TECHNICAL_NOTE_VERONESE_HOMOLOGICAL_PRG.md)
* **Paper / Technical Note v0.2 (Disjunctive Interpolants & Universal $\forall n$ Lean 4 Soundness):** [TECHNICAL_NOTE_DISJUNCTIVE_INTERPOLANTS.md](TECHNICAL_NOTE_DISJUNCTIVE_INTERPOLANTS.md)
* **Paper / Technical Note v0.1 (Adder Miters & Dual Annihilators):** [TECHNICAL_NOTE.md](TECHNICAL_NOTE.md)

---

## Architecture Overview

1. **Blind Gate & Adder Extraction (`adder_extraction.py` + `veripb_emitter.py`, v0.1):** Recovers 2-input boolean gates under arbitrary variable/polarity permutations, merges congruent outputs, extracts $\mathbb{Z}$-linear half-adder ($u + w - s - 2c = 0$) and disjoint-carry full-adder ($c_1 + c_2 - c_{\mathrm{out}} = 0$) identities, eliminates internal carries via sparse rational RREF, and emits `VeriPB 3.0` (`rup`, `pol`, `d`) certificates for 2-adic/GCD peeling.
2. **Blind Disjunctive `VeriPB 3.0` Interpolant Calculus (`veripb_interpolant.py`, v0.2):** Performs logged `(1,1)`-chain unrolling, Pigeonhole-anchored $O(|V|\cdot \deg)$ primal vertex-cut discovery ($|S| \le 6$), guarded Chvátal–Gomory clique AMO induction + `PHP` guard derivation (`0` extension vars), guarded $\mathrm{MAJ}_3$ `red`-witness parity linearization with lazy $\mathbb{F}_2$ RREF and even-coefficient CG halving, and $2^{|S|}-1$ Boolean cube halving reassembly.
3. **Dual Annihilator Synthesis & Coupled Macaulay/CP (`veronese_annihilator.py` + `macaulay_cp.py`):** Projects local falsification sets to degree-$d$ Reed–Muller coordinates $\mathrm{RM}(d, n)$ with $O(|V|\cdot \dim^2)$ directional Boolean derivative isolation ($\Delta_u P \equiv 1$), coupled with width-3 diamond collisions, 4-variable petal ideals, sparse $\mathbb{F}_2$ RREF, and guarded cutting planes.
4. **Four-Tier Lean 4.36.0 Formalization (`proofs/`, 69 Verified Declarations, `0 sorryAx`):**
   * `proofs/rule_soundness.lean` (v0.1): 30 finite local rewrite rules (`decide +revert`, `0` axioms, `0 sorryAx`).
   * `proofs/disjunctive_interpolant_soundness.lean` (v0.2): 7 universal $\forall n$ theorem groups (17 `#print axioms`-checked declarations, `0 sorryAx`, kernel axioms only).
   * `proofs/veronese_prg_soundness.lean` (v0.3): 6 universal $\forall n$ theorem groups (14 `#print axioms`-checked theorems covering Veronese `red` product soundness, polarity invariance, $\mathbb{F}_2$-simplicial 2-cycle vanishing $\partial^2 = 0$, homological expander UNSAT, and the mechanical `RM(2, 6)` degree-2 barrier on `XOR-MAJ₅`, `0 sorryAx`).
   * `proofs/higher_veronese_rm_d_soundness.lean` (v0.4): 4 universal $\forall d, \forall n$ theorem groups (8 `#print axioms`-checked theorems covering arbitrary-degree `List Bool` Veronese `red` soundness, Lucas majority collapse `MAJ₅ = e₃ ⊕ e₄` / `MAJ₇ = e₄`, inductive $\forall n$ simplicial 3-cycle vanishing $\partial_3 \partial_4 = 0$, and `RM(4, 5)` uniqueness across $2^{31}$ polynomials on `AND₅`, `0 sorryAx`).
5. **Zero-Dependency Native Rust `VeriPB 3.0` Engine (`rust_core/`, v0.4):** Escalates $d = 1..4$ in $\mathrm{RM}(d, n)$ with `6.99×–11.61×` faster `.pbp` emission than Python, certifying `Cubic_XOR3_AND3`, $K_5$ Homological `XOR3_SYM3`, `Goldreich_XOR3_MAJ5` (up to `90,136` clauses / `344,216` `.pbp` lines), and external `Shifted_Cubic_Sponge_Miter_Scrambled.cnf` (`82.31 ms`).

---

## Quickstart

```bash
# 1. Verify all 15 standalone Lean 4.36.0 soundness suites (0 external imports, 0 sorryAx)
for f in proofs/*.lean; do lean "$f"; done

# 2. Build native Rust VeriPB 3.0 engines & verify the unified 11-benchmark corpus + SAT controls
cargo build --release --manifest-path rust_core/Cargo.toml
cargo build --release --manifest-path schoenebeck_rs/Cargo.toml
uv run --with-editable . cap-bench-v05

# 3. Reproduce Krajíček CF -> ≈ compilers (DAG, aligned SLP, non-aligned Jeż recompression) & Witt-Kneser labs
uv run --with-editable . cap-cf-compiler
uv run --with-editable . cap-slp-unifier
uv run --with-editable . cap-nonaligned-slp
uv run --with-editable . cap-witt-kneser
uv run --with-editable . cap-schoenebeck-rm4

# 4. Full end-to-end reproduction script
./scripts/reproduce.sh --timeout 300
```

---

## Key Verified Results

### Technical Note v0.3: Single-Expander Goldreich `TSA` & $\mathbb{F}_2$-Homological `XOR₃-MAJ₃` (`|S| = 0` & Hybrid)

> **Full 12-instance scaling table, `v0.2` vs `v0.3` ablation, degree-3/4 barrier controls, and SAT controls:** see [TECHNICAL_NOTE_VERONESE_HOMOLOGICAL_PRG.md](TECHNICAL_NOTE_VERONESE_HOMOLOGICAL_PRG.md) and [results/veronese_prg_benchmark_results.json](results/veronese_prg_benchmark_results.json).

* **Resolves Limitation #2 of v0.2 (`|S| = 0` single-component expanders):** Certifies `13/13` instances (`s VERIFIED UNSATISFIABLE` via pure `pol` + `red`, `0` `rup`), including single-expander `Goldreich_TSA_5Local` (`V = 28..96`) and `Homological_XOR3_MAJ3` over $K_4$ simplicial 2-cycles (**zero repeated `MAJ₃` triplets**), where `Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5` all hit `TIMEOUT_60s` starting at $V \ge 48$ (`1,608` vars / `2,304` clauses, ours `465.90 ms` on `TSA_V48` and `457.94 ms` on `Homological_XOR3_MAJ3_V52`).
* **3-Selector Hybrid Scaling (`PHP12_11_OR3_Homological_XOR3_MAJ3_V40`):** `31,715` vars / `41,160` clauses certified in **`9,438.63 ms`** (`TIMEOUT_60s` on all 3 C/C++ solvers).
* **Delimited Degree-3/4 Frontier (`v0.4`):** Cleanly rejects `Barrier_Cubic_XOR3_AND3_6Local_V36` (`deg = 3`) and `Barrier_Goldreich_XOR3_MAJ5_7Local_V36` (`deg = 4`, backed by Lean theorem `xor_maj5_no_deg2_annihilator`) plus `4/4` `SAT` controls with `0` false positives.

### Technical Note v0.2: Disjunctive Interpolants (`PHP_p^h OR_S Tseitin_G`)

> **Full 11-instance scaling table, `|S|=0` orthogonal ablation, and SAT soundness controls:** see [TECHNICAL_NOTE_DISJUNCTIVE_INTERPOLANTS.md](TECHNICAL_NOTE_DISJUNCTIVE_INTERPOLANTS.md) and [results/interpolant_benchmark_results.json](results/interpolant_benchmark_results.json).

* **13/13 `s VERIFIED UNSATISFIABLE`** across $|S| \in \{0, 2, 3\}$ (`11` scaling/multi-selector instances + `2` standalone $|S|=0$ ablations).
* **Largest instance (`PHP24_23_OR2_Tseitin52`):** `16,656` vars / `29,664` clauses certified in **`3,089.92 ms`** (`2,972.84 ms` Python emit + `117.08 ms` `veripb 3.0.2`) where `Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5` all hit `TIMEOUT_60s`.
* **Multi-selector 3-regular expanders (`|S|=3`):** `PHP14_13_OR3_Expander36` (`13,419` vars / `18,964` clauses) certified in **`1,353.55 ms`** (`TIMEOUT_60s` for all 3 C/C++ solvers).
* **Orthogonal `|S|=0` ablation:** `CryptoMiniSat 5` solves pure `Standalone_Tseitin140_Expander_Scrambled` (`1,854.25 ms`, ours `34.50 ms`) while `Kissat`/`CaDiCaL` time out, yet all three C/C++ solvers time out on `Standalone_PHP14_13_Scrambled` (ours `740.52 ms`) and on the wire-eliminated disjunction.
* **4/4 SAT controls rejected** with `0` false positives (all 4 verified `SAT` by `CaDiCaL 1.9.5`).

### Technical Note v0.1: Arithmetic Adder Miters (`Schoolbook vs Wallace`)

> **Full experimental methodology, limitations, and citations:** see [TECHNICAL_NOTE.md](TECHNICAL_NOTE.md).

### Table 1: End-to-End `VeriPB 3.0.2` Certification (`Schoolbook vs Wallace` Scrambled 3-CNF Miters)

| Instance | Vars | Clauses | `.pbp` Lines | Emit Time | `veripb 3.0.2` Check | Verdict |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `Scrambled_Miter_06x06` | `369` | `1,174` | `6,135` | `532.4 ms` | **`37.2 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_08x08` | `685` | `2,206` | `11,872` | `1,641.2 ms` | **`43.9 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_10x10` | `1,097` | `3,558` | `19,406` | `3,524.4 ms` | **`87.8 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_12x12` | `1,605` | `5,230` | `28,793` | `6,483.2 ms` | **`213.8 ms`** | `s VERIFIED UNSATISFIABLE` |
| `Scrambled_Miter_16x16` | `2,909` | `9,534` | `53,042` | `28,230.8 ms` | **`400.9 ms`** | `s VERIFIED UNSATISFIABLE` |

### Table 2: 300s Wall-Clock Comparison vs `Kissat 4.0.4` & `CryptoMiniSat 5`

| Scrambled Benchmark (`.cnf`) | Vars / Clauses | Ours (Python, 0-Branch) | `Kissat 4.0.4` (`-O3` C) | `CryptoMiniSat 5` (C++) |
| :--- | :---: | :---: | :---: | :---: |
| `Miter_Mult_12x12_Scrambled` | `1,605 / 5,230` | **`UNSAT` (`6,722.8 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` |
| `Miter_Mult_16x16_Scrambled` | `2,909 / 9,534` | **`UNSAT` (`12,999.4 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` |
| `Miter_Mult_20x20_Scrambled` | `4,597 / 15,118` | **`UNSAT` (`27,786.8 ms`)** | `TIMEOUT_300s` | `TIMEOUT_300s` |
| `WireElim_OR_s1s2_PHP13_12_Tseitin28` | `3,157 / 5,196` | **`UNSAT` (`2,874.7 ms`)** | `UNSAT` (`209,745.2 ms`) | `TIMEOUT_300s` |
| `Lifted_PHP65_o_Keccak4L_Scrambled` | `17,373 / 21,284` | `UNSAT` (`3,885.2 ms`) | **`UNSAT` (`151.6 ms`)** | `UNSAT` (`213.4 ms`) |
| `Shifted_Cubic_Sponge_Miter_Scrambled` | `2,615 / 3,264` | `UNSAT` (`235.3 ms`) | **`UNSAT` (`144.7 ms`)** | `UNSAT` (`252.7 ms`) |
| `Goldreich_XORMAJ3_n28_m36_Scrambled` | `1,180 / 1,728` | `FEASIBLE` *(var cap)* | **`UNSAT` (`51.5 ms`)** | `UNSAT` (`116.4 ms`) |

*Note:* `RoundingSat` was not built locally (`cmake` / `Boost >= 1.70` absent); `benchmark_solvers.py` supports `--roundingsat-bin` when available.

---

## Repository Layout

```text
certified-arith-preproc/
├── papers/                                      # Standalone publication-ready papers (v0.8.0)
│   ├── PAPER_1_VERIPB_BLIND_ARITH_VERONESE.md
│   ├── PAPER_2_KRAJICEK_CF_APPROX_COMPLETE_DICHOTOMY.md
│   └── PAPER_3_WITT_KNESER_2ADIC_TORSION_NC_IPS.md
├── proofs/                                      # 15 standalone Lean 4.36.0 suites (0 imports, 0 sorryAx)
├── rust_core/                                   # Native Rust VeriPB 3.0 engine (Zassenhaus, Macaulay, Z-adder)
├── schoenebeck_rs/                              # Native Rust RM(3,4)/RM(4,5) + VeriPB 3.0 Schoenebeck solver
├── src/certified_arith_preproc/                 # Python preprocessors, Krajíček SLP compilers & Witt-Kneser labs
├── scripts/reproduce.sh                         # One-command portable verification script
├── results/                                     # Verified JSON summaries
├── RUTAS_ATAQUE_P_VS_NP.md                      # 15/15 Attack Queue & Anti-Trap Audit Log
├── TECHNICAL_NOTE_V05_AND_FRONTIER_LABS.md      # Unified Technical Note (v0.8.0)
└── pyproject.toml
```
