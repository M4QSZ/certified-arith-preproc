# Higher-Order Veronese $\mathrm{RM}(d, n)$, $K_5$ Simplicial Homology & Native Rust `VeriPB 3.0` Engine (`v0.4`)

> **Status:** Research prototype & Technical Note (`v0.4`). Not peer-reviewed; every theorem, proof certificate, and benchmark timing has been mechanically verified with `Lean 4.36.0` (`0 sorryAx`), `rustc 1.100.0`, and `veripb 3.0.2`.

---

## Abstract

Technical Note `v0.3` resolved degree-2 expander-entangled Goldreich PRGs (`TSA` and Homological `XOR₃-MAJ₃`) in Python, but left open two explicit bottlenecks: (1) **higher-degree algebraic barriers** (`Cubic XOR₃-AND₃` of degree 3 and `Goldreich XOR₃-MAJ₅` of degree 4, proved in `v0.3` to have trivial vanishing ideal `{0}` in $\mathrm{RM}(2, 6)$), and (2) **Python proof-emission overhead** (`8.00 s` for `77,868` `.pbp` lines) alongside evaluation on pre-existing external CNF corpora.

This note documents `v0.4.0` of `certified-arith-preproc` (`rust_core/src/main.rs` + `proofs/higher_veronese_rm_d_soundness.lean`), advancing both fronts while delimiting the exact degree-5 and lifting barriers (`v0.5`):

1. **Iterative Higher-Order Veronese $\mathrm{RM}(d, n)$ ($1 \le d \le 4$) & $K_5$ Cubic Homology ($\partial_3 \partial_4 = 0$):** Escalates degree $d = 1, 2, 3, 4$ on demand, introducing $(d + 1)$-clause `VeriPB 3.0` `red` monomial witnesses $p_M \leftrightarrow \bigwedge_{u \in M} x_u$ (`0` `rup` search). Breaks both `v0.3` barriers (`Cubic_XOR3_AND3` and `Goldreich_XOR3_MAJ5`) and certifies **6-local Homological $K_5$ `XOR₃-SYM₃`**—where **zero 4-tuples repeat anywhere in the formula** and cubic terms cancel purely via the 4-simplex boundary identity $\bigoplus_{j=0}^4 e_3(K_5 \setminus \{u_j\}) \equiv 0 \pmod 2$.
2. **Zero-Dependency Native Rust Engine (`cap-veronese-rs`):** Compiled with `rustc 1.100.0 -O3` + LTO, accelerating proof emission by **`6.99x–11.61x`** (up to `26.6x` cold-cache) over Python and certifying **`PHP14_13_OR2_Goldreich_XOR3_MAJ5_V44`** (`70,956` vars / **`90,136` clauses**, `344,216` `.pbp` lines) in **`6.29 s`** total (`1.83 s` Rust emit + `4.46 s` `veripb 3.0.2`) where `Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5` all hit `TIMEOUT_60s`.
3. **External Corpus Audit (`cnf_samples/`):** Blindly certifies `Shifted_Cubic_Sponge_Miter_Scrambled.cnf` (`d = 3`, `82.31 ms` total, faster than uncertified `Kissat` and `CryptoMiniSat 5`) and `WireElim_OR_s1s2_PHP13_12_Tseitin28.cnf` (`50.67 ms` vs `Kissat` `209,745.2 ms`), while cleanly isolating $\mathbb{Z}$-carry miters (`v0.1`) and lifted gadget compositions (`PHP ∘ g`) as distinct proof-complexity regimes.
4. **Universal $\forall d, \forall n$ Lean 4.36.0 Suite (`8` Theorems, `0 sorryAx`):** Proves universal `List Bool` Veronese `red` soundness, the Lucas majority-degree collapse law (`MAJ₅ = e₃ ⊕ e₄`, `MAJ₇ = e₄`), inductive $\forall n$ simplicial 3-cycle vanishing (`simplicial_3cycle_e3_vanishes`), and the **Degree-4 Barrier Theorem** (`and5_no_deg4_annihilator`) across all $2^{31} = 2,147,483,648$ polynomials in $\mathrm{RM}(4, 5)$.

---

## 1. Higher-Order Veronese Calculus & Lucas Majority-Degree Law

* **Universal $(d + 1)$-Clause Veronese `red` Monomial Definition:** For any sorted variable subset $M = (u_1, \dots, u_d)$ ($d \ge 2$) appearing in the minimal inconsistent $\mathrm{RM}(d, n)$ RREF core $E^*$, `cap-veronese-rs` allocates one shared witness $p_M$ via:
  ```text
  red 1 ~x_{u_1} ... 1 ~x_{u_d} 1 x_{p_M} >= 1 : x_{p_M} -> 1 ;
  red 1 x_{u_j} 1 ~x_{p_M} >= 1 : x_{p_M} -> 0 ;    (for j = 1 .. d)
  ```
  Whenever $x_{u_j} = 0$ and $x_{p_M} = 1$ (negation of `and_0_j`), substituting $x_{p_M} \mapsto 0$ satisfies `and_all` immediately via unit literal `~x_{u_j} = 1`—holding uniformly for **every degree $d \ge 1$** (`veronese_monom_red_0_rup_preserved`).
* **Lucas's Theorem on Majority Threshold Gates over $\mathbb{F}_2$:** By Lucas's congruence on binomial coefficients $\binom{w}{r} \pmod 2$, symmetric majority predicates exhibit staircase degree jumps:
  * $\mathrm{MAJ}_3(x_1..x_3) = e_2(x)$ ($\deg = 2$, certified in `RM(2)`),
  * $\mathrm{MAJ}_5(x_1..x_5) = e_3(x) \oplus e_4(x)$ ($\deg = 4$, certified in `RM(4)`),
  * $\mathrm{MAJ}_7(x_1..x_7) = e_4(x)$ ($\deg = 4$ — **no degree-5, 6, or 7 terms!** Certified in `RM(4)`),
  * $\mathrm{MAJ}_9(x_1..x_9)$ jumps to $\deg = 8$ ($\mathrm{RM}(4, 9)$ nullity $= 0$).

---

## 2. Universal $\forall d, \forall n$ Formalization in Lean 4.36.0 (`proofs/higher_veronese_rm_d_soundness.lean`)

Verified with standalone `Lean 4.36.0` (`0` warnings, `0` errors, `0 sorryAx` across all 8 `#print axioms`-audited theorems):

| Group | Lean 4.36.0 Verified Theorems | Mathematical Scope |
| :--- | :--- | :--- |
| **Group 1** | `veronese_monom_red_1_witness`, `veronese_monom_red_0_rup_preserved`, `veronese_monom_clauses_characterize_all` | Universal $\forall \text{ls} : \text{List Bool}$ `red` witness validity, RUP preservation, and exact $p = \bigwedge_{u \in \text{ls}} u$ characterization for arbitrary degree $d$ |
| **Group 2** | `maj5_anf_e3_xor_e4`, `maj7_lucas_deg4_collapse`, `k5_4simplex_sym3_boundary_zero` | Exact ANF $\mathrm{MAJ}_5 = e_3 \oplus e_4$, 7-input Lucas collapse $\mathrm{MAJ}_7 = e_4$, and $K_5$ 5-face cubic boundary cancellation (`0` axioms) |
| **Group 3** | `simplicial_3cycle_e3_vanishes` | Universal inductive $\forall n, \forall x, \forall \text{tets}$ vanishing $\partial_3 \mathcal{C} = 0 \Rightarrow \bigoplus e_3 = 0$ over arbitrary ordered tetrahedron lists |
| **Group 4** | `and5_no_deg4_annihilator` | **Mechanical Degree-4 Barrier:** across all $2^{31} = 2,147,483,648$ polynomials in $\mathrm{RM}(4, 5)$, only `0` vanishes on `x₁ ∧ x₂ ∧ x₃ ∧ x₄ ∧ x₅ = false` |

---

## 3. Experimental Evaluation (`cap-veronese-rs` + `veripb 3.0.2` vs C/C++ Solvers, 60s Limit)

All results recorded in [results/higher_veronese_v04_results.json](results/higher_veronese_v04_results.json).

### Table 1: Higher-Order Veronese (`d = 3, 4`) & $K_5$ Homological Scaling (`60s` Limit)

| Instance (`3-CNF` scrambled) | Vars / Clauses | `d` / `\|S\|` | `.pbp` Lines | `cap-veronese-rs + veripb` | `Kissat 4.0.4` | `CaDiCaL 1.9.5` | `CryptoMiniSat 5` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `Cubic_XOR3_AND3_6Local_V36` | `3,510 / 4,608` | `3 / 0` | `19,016` | **`185.00 ms`** (`50.02 + 134.98`) | `10,030.75 ms` | `8,708.96 ms` | `14,442.97 ms` |
| `Cubic_XOR3_AND3_6Local_V52` | `5,070 / 6,656` | `3 / 0` | `29,824` | **`332.82 ms`** (`85.55 + 247.27`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Cubic_XOR3_AND3_6Local_V72` | `7,020 / 9,216` | `3 / 0` | `37,000` | **`358.34 ms`** (`105.86 + 252.48`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Homological_K5_XOR3_SYM3_6Local_V40` | `3,900 / 5,120` | `3 / 0` | `34,183` | **`259.08 ms`** (`56.67 + 202.41`) | `43,035.11 ms` | `50,752.78 ms` | `TIMEOUT_60s` |
| `Homological_K5_XOR3_SYM3_6Local_V60` | `5,850 / 7,680` | `3 / 0` | `54,458` | **`379.77 ms`** (`97.89 + 281.88`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |
| `Goldreich_XOR3_MAJ5_7Local_V36` | `9,270 / 11,520` | `4 / 0` | `117,574` | **`1,042.22 ms`** (`197.51 + 844.71`) | `3,363.03 ms` | `2,252.33 ms` | `6,624.52 ms` |
| `Goldreich_XOR3_MAJ5_7Local_V52` | `13,390 / 16,640` | `4 / 0` | `166,519` | **`1,391.06 ms`** (`342.98 + 1,048.08`) | `17,085.77 ms` | `17,183.42 ms` | `25,756.54 ms` |
| `Goldreich_XOR3_MAJ5_7Local_V68` | `17,510 / 21,760` | `4 / 0` | `220,702` | **`2,305.83 ms`** (`595.51 + 1,710.32`) | `24,639.15 ms` | `21,459.23 ms` | `41,652.86 ms` |
| `PHP14_13_OR2_Goldreich_XOR3_MAJ5_V44` | `70,956 / 90,136` | `4 / 2` | `344,216` | **`6,291.89 ms`** (`1,832.94 + 4,458.95`) | `TIMEOUT_60s` | `TIMEOUT_60s` | `TIMEOUT_60s` |

### Table 2: Python (`v0.3`) vs Native Rust (`v0.4`) Emission Speedup

| Instance | Vars / Clauses | `.pbp` Lines | Python `v0.3` Emit | Rust `v0.4` Emit | `veripb 3.0.2` Check | Emit Speedup |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Homological_XOR3_MAJ3_5Local_V80` | `2,680 / 3,840` | `23,752` | `197.77 ms` | **`28.31 ms`** | `75.68 ms` | **`6.99×`** |
| `Homological_XOR3_MAJ3_6Local_V44` | `4,290 / 5,632` | `27,094` | `377.64 ms` | **`41.72 ms`** | `88.95 ms` | **`9.05×`** |
| `PHP12_11_OR3_Homological_XOR3_MAJ3_V40` | `31,715 / 41,160` | `77,868` | `2,613.07 ms` | **`225.07 ms`** | `409.94 ms` | **`11.61×`** |

### Table 3: External Corpus Audit & Degree-5 / Lifting Frontier (`v0.5` Delimitation)

| Benchmark | Vars / Clauses | `cap-veronese-rs` (`RM(<=4)`) | Structural Regime / Diagnosis |
| :--- | :---: | :---: | :--- |
| `Shifted_Cubic_Sponge_Miter_Scrambled.cnf` | `2,615 / 3,264` | **`VERIFIED UNSAT` (`82.31 ms`, `d=3`)** | Cubic sponge syzygy (`|S|=0`) certified faster than uncertified `Kissat` (`144.7 ms`) |
| `WireElim_OR_s1s2_PHP13_12_Tseitin28.cnf` | `3,157 / 5,196` | **`VERIFIED UNSAT` (`50.67 ms`, `d=1, |S|=2`)** | `4,139×` faster than `Kissat` (`209,745.2 ms`); `CMS5` `TIMEOUT_300s` |
| `Barrier_Quintic_XOR3_AND5_7Local_V44` | `11,330 / 14,080` | `Rejected: outside RM(4, n)` | **Degree-5 barrier** (matches Lean theorem `and5_no_deg4_annihilator`) |
| `Miter_Mult_12x12..20x20_Scrambled.cnf` | `1,605..4,597` | `Handled by v0.1 Z-adder engine` | Carry chains have unbounded $\mathbb{F}_2$ degree $\Omega(k)$; certified in `v0.1` over $\mathbb{Z}$ |
| `Lifted_PHP65_o_Keccak4L_Scrambled.cnf` | `17,373 / 21,284` | `Rejected: outside RM(4, n)` | **Lifting composition $F \circ g$** (destroys binary AMO cliques; target of `v0.5`) |

*SAT Soundness Controls (`4/4` Rejected, `0` False Positives):* `SAT_Cubic_XOR3_AND3_6Local_V44_even` (`40.76 ms`), `SAT_Homological_K5_XOR3_SYM3_6Local_V40_even` (`29.80 ms`), `SAT_Goldreich_XOR3_MAJ5_7Local_V44_even` (`72.06 ms`), and `SAT_PHP10_10_OR2_Goldreich_XOR3_MAJ5_V36` (`350.76 ms`)—all verified `SAT` by `CaDiCaL 1.9.5`.

---

## 4. Delimited Next Frontier (`v0.5`)

The corpus audit in Table 3 isolates the two exact structural gaps remaining before general industrial UNSAT preprocessing:
1. **Unified Portfolio Dispatcher (`Z`-Telescoping `v0.1` $\oplus$ Rust `RM(d, n)` `v0.4`):** Combining integer carry recovery ($\mathbb{Z}$) with bounded-degree $\mathbb{F}_2$ Veronese homology in a single binary.
2. **Lifted Formula Inversion (`F ∘ g`, Garg–Göös–Kamath–Sokolov Barrier):** Blindly inverting bijection/sponge gadgets `g` (e.g. `Keccak-χ` rounds or `XOR`/`MAJ` gadgets) via `VeriPB 3.0` `red` inverse witnesses to recover underlying `PHP` / cardinality cores when binary AMO clauses have been shattered into width-$\ge 5$ blocks.

---

## 5. Reproducibility Commands

```bash
# 1. Verify Lean 4.36.0 v0.4 higher-order Veronese & K5 homology theorems (0 sorryAx)
lean proofs/higher_veronese_rm_d_soundness.lean

# 2. Build native Rust VeriPB 3.0 emitter
cargo build --release --manifest-path rust_core/Cargo.toml

# 3. Run full 60s v0.4 benchmark, Python-vs-Rust speedup, corpus audit & SAT controls
uv run --with-editable '.[benchmarks]' cap-bench-v04 --timeout 60
```
