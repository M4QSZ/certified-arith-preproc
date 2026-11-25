# certified-arith-preproc

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean%204.36.0-30%20theorems%20%C2%B7%200%20axioms-brightgreen.svg)](proofs/rule_soundness.lean)
[![VeriPB](https://img.shields.io/badge/VeriPB-3.0.2%20verified-brightgreen.svg)](results/veripb_results.json)
[![Python](https://img.shields.io/badge/Python-3.10%2B-blue.svg)](pyproject.toml)

A research prototype for **VeriPB-certified blind arithmetic adder extraction**, **dual Reed–Muller annihilator synthesis**, and **coupled sparse Macaulay / guarded cutting-planes preprocessing** on variable- and polarity-scrambled 3-CNF formulas.

---

## Architecture Overview (5 Lines)

1. **Blind Gate & Adder Extraction (`adder_extraction.py`):** Recovers 2-input boolean gates under arbitrary variable/polarity permutations, merges congruent outputs, and extracts $\mathbb{Z}$-linear half-adder ($u + w - s - 2c = 0$) and disjoint-carry full-adder ($c_1 + c_2 - c_{\mathrm{out}} = 0$) identities.
2. **Single Sparse Rational RREF + 2-Adic/GCD Peeling (`veripb_emitter.py`):** Eliminates internal carries over $\mathbb{Q}$, tracks exact integer multipliers, and emits polynomial-size `VeriPB 3.0` (`rup`, `pol`, `d`) certificates verified by `veripb 3.0.2`.
3. **Dual Annihilator Synthesis (`veronese_annihilator.py`):** Projects local falsification sets to degree-$d$ Reed–Muller coordinates $\mathrm{RM}(d, n)$ and isolates quasilinear extension definitions via directional Boolean derivatives ($\Delta_u P \equiv 1$) in $O(|V|\cdot \dim^2)$ time.
4. **Coupled Sparse Macaulay & Guarded Cutting Planes (`macaulay_cp.py`):** Combines width-3 diamond collisions, 4-variable petal ideals, sparse $\mathbb{F}_2$ RREF, modular hyperplanes, guarded clique LP cuts, and primal vertex-cut decomposition.
5. **Formal Rule Check (`proofs/rule_soundness.lean`):** 30 finite local rewrite identities mechanically verified in Lean 4.36.0 (`decide +revert`, `0` axioms).

---

## Quickstart (3 Commands)

```bash
# 1. Verify all 30 finite rewrite-rule theorems in Lean 4 (0 axioms)
lean proofs/rule_soundness.lean

# 2. Emit & verify VeriPB 3.0.2 proofs on scrambled 6x6..16x16 multiplier miters
uv run --with-editable . cap-veripb --bits 6 8 10 12 16

# 3. Full reproduction script (Lean 4 + VeriPB 3.0.2 + 300s solver benchmark)
./scripts/reproduce.sh --timeout 300
```

---

## Key Verified Results

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
├── proofs/rule_soundness.lean                 # 30 Lean 4.36.0 theorems (0 axioms)
├── src/certified_arith_preproc/
│   ├── cnf_utils.py                           # DIMACS I/O, scrambling, (1,1) unrolling, BCP/2-XOR
│   ├── benchmarks.py                          # Synthetic arithmetic, interpolant & PRG generators
│   ├── adder_extraction.py                    # Blind 2-input gate scan + Z-telescoping + 2-adic peel
│   ├── veripb_emitter.py                      # VeriPB 3.0 (.pbp) proof logger & checker CLI
│   ├── veronese_annihilator.py                # Dual RM(d, n) annihilators & derivative syzygy collapse
│   ├── macaulay_cp.py                         # Sparse degree-3 Macaulay <-> guarded cutting planes
│   └── benchmark_solvers.py                   # 300s wall-clock comparison harness
├── scripts/reproduce.sh                       # One-command portable verification script
├── results/                                   # Verified JSON summaries
├── TECHNICAL_NOTE.md                          # Preprint draft / Technical Note
└── pyproject.toml
```
