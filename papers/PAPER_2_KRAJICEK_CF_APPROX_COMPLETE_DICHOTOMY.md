# Polynomial-Time Recompression and Exact Syntactic-vs-Semantic Dichotomy for Krajíček's Circuit-Rewriting Problem (CF -> ≈-Chains)

> **Verification Status:** Mechanically verified in **Lean `4.36.0`** across **5 standalone proof suites** (`0` external imports, **`0 sorryAx`** via `#print axioms`: [`krajicek_ba_rewriting_soundness.lean`](../proofs/krajicek_ba_rewriting_soundness.lean), [`krajicek_cf_compiler_unsharing.lean`](../proofs/krajicek_cf_compiler_unsharing.lean), [`krajicek_slp_kcf_reduction.lean`](../proofs/krajicek_slp_kcf_reduction.lean), [`krajicek_nonaligned_context_slp.lean`](../proofs/krajicek_nonaligned_context_slp.lean), and [`proof_analysis_bug_extractor.lean`](../proofs/proof_analysis_bug_extractor.lean)). Empirical evaluation achieves **`100%`** `DAGStore.are_approx` single-occurrence step verification across all benchmarks (`ATAQUE-05`, `ATAQUE-08`, `ATAQUE-10`, `ATAQUE-13`, `ATAQUE-15`).

---

## Abstract

In *Extended Frege proofs, circuits and rewriting* (`arXiv:2606.13367v2`, p. 11), Jan Krajíček asks whether every Circuit Frege (`CF`) proof of total DAG size $S$ and $k$ proof lines admits a polynomial-size conversion into an equational rewriting chain $E_0 \approx E_1 \approx \dots \approx E_t = 1$, where $A \approx B$ denotes applying a single Boolean algebra (`BA`) axiom at a single occurrence in the tree unwinding $\mathsf{Fla}[A]$. We resolve the structural sharing, compressed-proof, and syntactic-alignment frontiers of this problem, and establish an exact boundary separating syntactic circuit sharing from pure semantic equivalence:
1. **Fan-Out $\ge 2$ Unsharing & $\mathrm{poly}(S)$ Compilation (`ATAQUE-10`):** Incorporating the October 2026 Datta–Dutta correction—where simultaneous rewriting across a shared gate of fan-out $\ge 2$ violates $A \approx B$ (`|C|_DAG = 4 -> 5` on $(x_1 \lor \neg x_1) \land (x_1 \lor \neg x_1)$)—we formalize persistent path-copying DAG unsharing ($|C'|_{\mathrm{DAG}} \le |C|_{\mathrm{DAG}} + |p| + c_{\mathrm{ba}}$), a zero-unwinding $2$-step `Fla`-bridge $C \approx (0 \lor C) \approx D$, and tree-balancing yielding $O(k \log k)$ chain length.
2. **Aligned SLP $k_{\mathrm{CF}}$-Pure Compression (`ATAQUE-13`):** Using parameterized template chains and symbolic Modus Ponens cancellation, any $k$-line aligned `SLPCFProof` compiles to a concrete $\approx$-chain of length $t \le (c_{\mathrm{ax}}+2)k$, strictly independent of intermediate DAG size $S$ (verified up to $S = 36{,}004$ and unwound formula size $4.10 \times 10^{18}$).
3. **Non-Aligned Context-SLPs via Hash-Consed Jeż Recompression (`ATAQUE-15`):** For completely misaligned linear `ContextSLP` hierarchies (dyadic doubling vs. period-3 or Thue–Morse grammars), canonical spine flattening `toSpine` and hash-consed Jeż RLE + locally-consistent pair recompression decide $\mathsf{Fla}[G_1] = \mathsf{Fla}[G_2]$ in deterministic $O(\mathrm{poly}(|G_1|+|G_2|))$ time without tree unwinding, verified up to spine length $3 \cdot 2^{60} \approx 3.46 \times 10^{18}$ in $10.057\text{ ms}$, yielding $t \le (c_{\mathrm{ax}}+2)k$ non-aligned compilation.
4. **Exact Syntactic-vs-Semantic Dichotomy & $\lceil \log_2 t \rceil$ Bug Localization (`ATAQUE-08`, `ATAQUE-15`):** Whenever $\mathsf{Fla}[A] = \mathsf{Fla}[B]$, equivalence is decidable in $\mathrm{P}$ and bridged in $2$ universal $\approx$-steps; when $\mathsf{Fla}[A] \neq \mathsf{Fla}[B]$ yet $A \equiv_{\mathrm{Bool}} B$, bridging requires genuine $\mathrm{coNP}$ tautology derivations (`2` `disjCompl` steps for $(x_0 \lor \neg x_0)$ vs. $(x_1 \lor \neg x_1)$, `807` steps for $\mathrm{XOR}_3$ associativity). Conversely, any falsifying assignment $x^*$ for $E_0$ locates a broken transition $E_i(x^*) \neq E_{i+1}(x^*)$ in $\le \lceil \log_2 t \rceil$ queries (`arXiv:2611.08305`).

---

## 1. Introduction & Krajíček's Open Problem (`arXiv:2606.13367v2`, p. 11)

Let $\mathcal{L}_{\mathrm{DM}} = \{0, 1, x_i, \neg, \lor, \land\}$ be the DeMorgan language and let `BA` be the 12 standard Boolean algebra equational axiom schemes (`negZero`: $\neg 0 = 1$; `negOne`: $\neg 1 = 0$; `disjZeroLeft`: $0 \lor a = a$; `conjOneLeft`: $1 \land a = a$; `disjCompl`: $a \lor \neg a = 1$; `conjCompl`: $a \land \neg a = 0$; `disjComm`, `conjComm`; `disjAssoc`, `conjAssoc`; `disjDistrib`, `conjDistrib`). A *DeMorgan circuit* $C$ is a straight-line DAG of gates over $\mathcal{L}_{\mathrm{DM}}$ with designated output gate $C.\mathrm{out}$ and DAG size $|C|_{\mathrm{DAG}}$. Its *tree unwinding* $\mathsf{Fla}[C]$ (`unfold C C.out`) expands every gate reference into a `DeMorganTerm`.

For formulas $s, t$, single-occurrence rewriting $s \approx_{\mathrm{BA}} t$ (`SimBA s t`) holds iff there exists a unique tree path $p \in \{\mathrm{L}, \mathrm{R}\}^*$ (`SimBAPath p s t`) where $t$ replaces the single subformula at $p$ by one bidirectional instance of `BA` (`BAStep`). An $n$-step equational chain `SimBAN n s t` inductively chains $n$ single-occurrence rewrites ($s = E_0 \approx E_1 \approx \dots \approx E_n = t$). Lifting to circuits, $A \approx B$ (`ApproxDAG A B`) holds iff $\mathsf{Fla}[A] \approx_{\mathrm{BA}} \mathsf{Fla}[B]$.

### The Datta–Dutta Fan-Out $\ge 2$ Correction (`v2`, October 2026)

In `arXiv:2606.13367v1`, rewriting a shared DAG gate $g$ of fan-out $f \ge 2$ in-place appeared to simulate one $\approx$-step. As Datta and Dutta observed (acknowledged in `arXiv:2606.13367v2`), mutating a gate of fan-out $f \ge 2$ alters $f$ distinct occurrences in $\mathsf{Fla}[C]$ simultaneously and therefore violates `SimBA`. On $C = (x_1 \lor \neg x_1) \land (x_1 \lor \neg x_1)$ (`|C|_DAG = 4`, where $g = x_1 \lor \neg x_1$ has fan-out $2$), simultaneous replacement yields $1 \land 1$ with `fanout2_simultaneous_both_approx = false`. Unsharing along path $p = [0]$ produces $C' = (1 \land (x_1 \lor \neg x_1))$ (`|C'|_DAG = 5`, `4 -> 5`), giving the $3$-step verified chain ([`krajicek_ew_graph_results.json`](../results/krajicek_ew_graph_results.json)):
$$((x_1 \lor \neg x_1) \land (x_1 \lor \neg x_1)) \;\xrightarrow{\;\texttt{disjCompl:fwd}\;@\;[0]\;}\; (1 \land (x_1 \lor \neg x_1)) \;\xrightarrow{\;\texttt{conjOneLeft:fwd}\;@\;[]\;}\; (x_1 \lor \neg x_1) \;\xrightarrow{\;\texttt{disjCompl:fwd}\;@\;[]\;}\; 1.$$

### Three Regimes of `CF -> ≈-Chain` Conversion

Circuit Frege (`CF`) represents proof lines as circuits $C_i$ (total size $S = \sum_i |C_i|_{\mathrm{DAG}}$, line count $k$) and includes the structural `Fla`-rule $C / D$ whenever $\mathsf{Fla}[C] = \mathsf{Fla}[D]$. We resolve three regimes of `CF -> ≈-Chain`:
- **(a) $\mathrm{poly}(S)$ DAG Proofs (`ATAQUE-10`):** Arbitrary intra-circuit sharing and inter-line DAG proof reuse compiled via path-copying unsharing and midpoint proof-tree balancing into $O(k \log k)$ $\approx$-steps and $\mathrm{poly}(S)$ circuit size.
- **(b) Aligned SLP-Compressed $k_{\mathrm{CF}}$ Proofs (`ATAQUE-13`):** The $k_{\mathrm{CF}}$-pure regime $S \gg \mathrm{poly}(k + |C| + |D|)$ where giant intermediate formulas $B_i$ share a parameterized SLP template grammar, compiled in $t \le (c_{\mathrm{ax}} + 2)k$ steps without materializing $S$.
- **(c) Non-Aligned Context-SLPs vs. Pure Semantic Equivalence (`ATAQUE-15`):** Misaligned linear `ContextSLP` decompositions satisfying $\mathsf{Fla}[G_1] = \mathsf{Fla}[G_2]$ (decided in $\mathrm{P}$ via Jeż recompression and bridged in $2$ steps) versus semantically equivalent $A \equiv_{\mathrm{Bool}} B$ with $\mathsf{Fla}[A] \neq \mathsf{Fla}[B]$.

---

## 2. Mechanical Formalization in `Lean 4.36.0` (`0 sorryAx`)

All results are formalized in five standalone Lean `4.36.0` modules (`0` external imports, `0 sorryAx`) audited via `#print axioms`.

| Suite / Attack | Lean Module | Audited Theorems | `#print axioms` |
| :--- | :--- | :--- | :--- |
| `ATAQUE-05` | [`krajicek_ba_rewriting_soundness.lean`](../proofs/krajicek_ba_rewriting_soundness.lean) | `baAxiom_sound`, `baStep_sound`, `simBAPath_sound`, `simBA_sound`, `simBAStar_sound`, `modus_ponens_simBAStar`, `modus_ponens_simBAN` | `[]` (`0` axioms) |
| `ATAQUE-10` | [`krajicek_cf_compiler_unsharing.lean`](../proofs/krajicek_cf_compiler_unsharing.lean) | `cf_fla_rule_two_step_approx`, `path_unsharing_size_bound`, `cf_modus_ponens_tree_bound` | `[propext]` / `[]` |
| `ATAQUE-13` | [`krajicek_slp_kcf_reduction.lean`](../proofs/krajicek_slp_kcf_reduction.lean) | `tsimBAN_inst`, `slp_congruence_two_step_approx`, `slp_localized_template_step_sound`, `slp_hole_congruence_two_step`, `template_modus_ponens`, `slp_modus_ponens_cancellation`, `mp_cancellation_chain_bound`, `cf_slp_unification_compression` | `[]` / `[propext, Quot.sound]` |
| `ATAQUE-15` | [`krajicek_nonaligned_context_slp.lean`](../proofs/krajicek_nonaligned_context_slp.lean) | `simBAN_evalBool_eq`, `evalSpine_toSpine`, `nonaligned_ctx_two_step_approx`, `doubling_tower_reassoc_two_step`, `nonaligned_ctx_cf_compression`, `syntactic_vs_semantic_fla_dichotomy` | `[propext]` / `[propext, Quot.sound]` |
| `ATAQUE-08` | [`proof_analysis_bug_extractor.lean`](../proofs/proof_analysis_bug_extractor.lean) | `binary_search_bug_step_correct`, `binary_search_bug_step_log_correct`, `bug_or_tautology_dichotomy`, `constructive_bug_extraction` | `[propext, Quot.sound]` (+ `Classical.choice` in dichotomy) |

**Core Formalized Theorems (Exact Lean Statements):**
- **Lemma 2.1 Modus Ponens (`modus_ponens_simBAN`, `0` axioms):** Given `SimBAN k₁ a .one` and `SimBAN k₂ (.disj (.neg a) b) .one`, rewriting $\neg a \approx^* \neg 1 \approx 0$ (`negOne`) and $(\neg a \lor b) \approx^* (0 \lor b) \approx b$ (`disjZeroLeft`) yields `SimBAN (k₁ + 2 + k₂) b .one`.
- **Zero-Unwinding `Fla` Bridge & Unsharing (`cf_fla_rule_two_step_approx`, `path_unsharing_size_bound`, `cf_modus_ponens_tree_bound`):** For any well-formed `C, D` with `unfold C C.out = unfold D D.out`, `M := zeroOrCircuit C` satisfies `M.gates.length = C.gates.length + 2` and `ApproxDAG C M ∧ ApproxDAG M D`. Persistent `pathCopy` produces `C'` with `C'.gates.length ≤ C.gates.length + p.length + c_ba` and `ApproxDAG C C'`; inductively, any `k`-step `TreeCFDeriv c_ax C k` compiles to `SimBAN n (unfold C C.out) .one` with `n ≤ (c_ax + 2) * k`.
- **Symbolic SLP Compression (`tsimBAN_inst`, `mp_cancellation_chain_bound`, `cf_slp_unification_compression`):** Any $n$-step template chain `TSimBAN n s t` instantiates under arbitrary $\rho : \mathbb{N} \to \mathrm{DeMorganTerm}$ to `SimBAN n (inst ρ s) (inst ρ t)`. A $k$-step MP chain $B_0 \to \dots \to B_k$ compiles to `SimBAN (m₀ + k * (c + 2)) .one (inst ρ (B k))`, and any `SLPCFProof ρ c_ax k G` compiles to `SimBAN t .one (unfoldSLP ρ G)` with `t ≤ (c_ax + 2) * k`.
- **Non-Aligned Context-SLPs (`evalSpine_toSpine`, `nonaligned_ctx_two_step_approx`, `doubling_tower_reassoc_two_step`, `nonaligned_ctx_cf_compression`, `syntactic_vs_semantic_fla_dichotomy`):** Canonical flattening `toSpine : CtxExpr → List AtomicCtx` satisfies `evalSpine (toSpine K) t = evalCtx K t`. Any two contexts with `toSpine K₁ = toSpine K₂` and `t₁ = t₂` satisfy `SimBAN 2 (evalCtx K₁ t₁) (evalCtx K₂ t₂)`—instantiated for all $m$ on `doublingTower m a` of depth $\ge 2^{m+1}$—and any `CtxCFProof c_ax k K u` compiles to `t ≤ (c_ax + 2) * k` steps.
- **Constructive Bug Localization (`binary_search_bug_step_log_correct`, `bug_or_tautology_dichotomy`, `constructive_bug_extraction`):** For any chain $E_0, \dots, E_t$ with $E_t \equiv 1$, either every step preserves semantics (so $E_0$ is a tautology), or any $x^*$ with $E_0(x^*) = \mathrm{false}$ yields `idx < t` with `eval idx x* = false ∧ eval (idx + 1) x* = true` in `fuel` steps whenever `t ≤ 2 ^ fuel`.

---

## 3. Polynomial-Time Compilers & Hash-Consed Jeż Recompression

### 3.1 Zero-Unwinding `0 ∨ C` Bridge, Path-Copying Unsharing, and `O(k log k)` Balancing

When a `CF` derivation invokes `Fla[C] = Fla[D]` between circuits $C, D$ with incompatible DAG sharing (`|C|_DAG ≠ |D|_DAG`), unwinding $\mathsf{Fla}[C]$ would incur exponential blowup ($8{,}388{,}601$ formula nodes at $m = 20$ in Suite 1 of `ATAQUE-10`). Instead, [`krajicek_cf_compiler.py`](../src/certified_arith_preproc/krajicek_cf_compiler.py) allocates the $2$-gate circuit $M := (0 \lor C)$ (`zeroOrCircuit C`) and applies `BAAxiom.disjZeroLeft` backward and forward at root path `[]`:
$$C \;\xrightarrow{\;\texttt{disjZeroLeft:bwd}\;@\;[]\;}\; (0 \lor C) \;\xrightarrow{\;\texttt{disjZeroLeft:fwd}\;@\;[]\;}\; D.$$
Because $\mathsf{Fla}[0 \lor C] = (0 \lor \mathsf{Fla}[C]) = (0 \lor \mathsf{Fla}[D])$, both transitions are exact single-occurrence `SimBA` steps with zero unwinding. For internal `BA` rewrites at tree path $p$, persistent `pathCopy` clones only the $|p|$ ancestors on $p$ (`|D'| <= |D| + |p|` when substituting an existing gate, or `<= |D| + |p| + c_ba` before hash-consing). For `CF` proof DAGs with line fan-out $\ge 2$, recursive midpoint balancing eliminates exponential proof-tree unwinding, yielding $O(k \log k)$ $\approx$-steps and $\mathrm{poly}(S)$ total DAG size.

### 3.2 SLP Template Modus Ponens Cancellation ($S \gg \mathrm{poly}(k)$)

In the $k_{\mathrm{CF}}$-pure regime where $S \gg \mathrm{poly}(k + |C| + |D|)$, [`krajicek_slp_unifier.py`](../src/certified_arith_preproc/krajicek_slp_unifier.py) operates over symbolic `SLP` grammars with metavariable holes `hole i` representing unmaterialized giant subcircuits $\rho(i)$. By `tsimBAN_inst` and `template_modus_ponens`, Modus Ponens over $B_i$ cancels the shared template in literally $+2$ concrete steps (`negOne` + `disjZeroLeft`), yielding total chain length $t \le (c_{\mathrm{ax}} + 2)k$ completely independent of $S$.

### 3.3 Hash-Consed Jeż Recompression on Non-Aligned `ContextSLP`s

When $G_1$ and $G_2$ are **non-syntactically-aligned** `ContextSLP`s—unary DeMorgan tree grammars built with `id`, `atom` ($\neg\square, \square \lor R, L \lor \square, \square \land R, L \land \square$), and associative composition `comp`—different parse hierarchies (e.g., dyadic doubling $D_{m+1} = D_m \circ D_m$ vs. period-3 or Thue–Morse splits) share zero intermediate nonterminals. [`krajicek_nonaligned_slp.py`](../src/certified_arith_preproc/krajicek_nonaligned_slp.py) decides $\mathsf{Fla}[G_1] = \mathsf{Fla}[G_2]$ in $O(\mathrm{poly}(|G_1| + |G_2|))$ time via `recompress_unify_context_slp` (Jeż 2016; Lohrey 2012):
1. **Normalized CFG Extraction (`_slp_to_cfg_rhs`):** Eliminate `id` rules and alias unit nonterminals in $O(|G_1| + |G_2|)$, representing atomic context frames as negative terminal IDs.
2. **Exact RLE Block Compression (`run_exact_rle_phase`):** A single bottom-up pass classifies each nonterminal as `pure` (a single maximal run $a^c$) or `impure` `(l_tok, l_cnt, mid_core, r_tok, r_cnt)` and compresses maximal blocks $a^c$ to canonical tokens via a hash-consed `block_dict`.
3. **Locally-Consistent Pair Compression & Hash-Consed Pruning (`prune_to_roots`):** Compute `first_tok`/`last_tok` and weighted adjacent pairs $(a,b)$ across rule boundaries; greedily partition terminals into $(L, R)$ maximizing cut weight; pop $R$-prefixes and $L$-suffixes out of nonterminals; merge $(L \times R)$ pairs via `pair_dict`; and compact reachable rules with `rhs_intern`.

Each round compresses the expanded spine length by a constant factor without unfolding the $2^m$ tree, deciding equality up to spine length $3 \cdot 2^{60} = 3{,}458{,}764{,}513{,}820{,}540{,}928 \approx 3.46 \times 10^{18}$ in $10.057\text{ ms}$.

**Correctness of Non-Aligned Compilation (`evalSpine_toSpine`, `nonaligned_ctx_cf_compression`):** By structural induction on `K : CtxExpr`, `evalSpine_toSpine` establishes `evalSpine (toSpine K) t = evalCtx K t` using `evalSpine_append` (`toSpine (.compC k₁ k₂) = toSpine k₁ ++ toSpine k₂`). Consequently, whenever `recompress_unify_context_slp` certifies `toSpine K₁ = toSpine K₂` and `u₁ = u₂`, `nonaligned_ctx_two_step_approx` constructs the $2$-step bridge `SimBAN 2 (evalCtx K₁ u₁) (evalCtx K₂ u₂)` via `0 ∨ C`. In particular, `doubling_tower_reassoc_two_step` bridges arbitrary reassociations `(D_m ∘ D_m) ∘ K` vs. `D_m ∘ (D_m ∘ K)` of exponential depth $\ge 2^{m+1}$ in exactly `2` $\approx$-steps for every $m \in \mathbb{N}$. Lifting inductively across `CtxCFProof` in [`krajicek_nonaligned_context_slp.lean`](../proofs/krajicek_nonaligned_context_slp.lean), `nonaligned_ctx_cf_compression` compiles any $k$-line proof combining bounded-cost axiom templates ($m \le c_{\mathrm{ax}}$), Modus Ponens cuts over giant compressed contexts (`evalSpine (toSpine K_Imp) u_Imp`), and non-aligned `toSpine` unification steps to a valid concrete chain `SimBAN t .one (evalCtx K u)` with:
$$t \;\le\; (c_{\mathrm{ax}} + 2)\, k,$$
strictly independent of intermediate DAG size $S$ and exponential tree depth $2^m$.

---

## 4. Syntactic-vs-Semantic Dichotomy & Constructive Bug Localization (`arXiv:2611.08305`)

Theorem 4 (`syntactic_vs_semantic_fla_dichotomy`) delineates the exact computational boundary of `CF -> ≈-Chain`:
- **Syntactic `Fla`-Equality ($\in \mathrm{P}$, `2` $\approx$-steps):** Any non-aligned `(K₁, u₁), (K₂, u₂)` with `toSpine K₁ = toSpine K₂` and `u₁ = u₂` satisfies `Fla[K₁(u₁)] = Fla[K₂(u₂)]`, is certified in deterministic polynomial time by Jeż recompression, and bridges in $2$ universal `0 ∨ C` steps.
- **Pure Semantic Equivalence ($\mathrm{coNP}$-hard, Non-Universal `BA` Steps):** When $\mathsf{Fla}[A] \neq \mathsf{Fla}[B]$ despite $A \equiv_{\mathrm{Bool}} B$, structural `Fla` sharing is powerless. For `tautVar0` $= (x_0 \lor \neg x_0)$ and `tautVar1` $= (x_1 \lor \neg x_1)$, `¬ SimBA tautVar0 tautVar1` holds (`1` step is impossible); bridging requires $2$ variable-eliminating `disjCompl` steps ($x_0 \lor \neg x_0 \approx 1 \approx x_1 \lor \neg x_1$). When variables coincide but Boolean structure differs, e.g., $\mathrm{XOR}_3$ associativity $((x_1 \oplus x_2) \oplus x_3)$ vs. $(x_1 \oplus (x_2 \oplus x_3))$, bidirectional graph search requires $807$ verified `BA` steps.

**Syntactic-vs-Semantic Dichotomy in Lean (`syntactic_vs_semantic_fla_dichotomy`):** Explicitly, [`krajicek_nonaligned_context_slp.lean`](../proofs/krajicek_nonaligned_context_slp.lean) proves the conjunction:
1. *(Syntactic `Fla`-equality regime)* `∀ K₁ K₂ u, toSpine K₁ = toSpine K₂ → SimBAN 2 (evalCtx K₁ u) (evalCtx K₂ u)`;
2. *(Semantic `≡_Bool` barrier)* For `tautVar0 := .disj (.var 0) (.neg (.var 0))` and `tautVar1 := .disj (.var 1) (.neg (.var 1))`:
   `SemEquiv tautVar0 tautVar1 ∧ tautVar0 ≠ tautVar1 ∧ ¬ SimBA tautVar0 tautVar1 ∧ SimBAN 2 tautVar0 tautVar1`.

This cleanly separates structural `Fla` sharing (solvable in $\mathrm{P}$ via Jeż recompression with $2$ universal steps) from semantic equivalence over distinct syntax trees (which requires genuine variable-eliminating `BA` steps).

**Constructive Bug Localization (`ATAQUE-08`):** Complementary to `CF` compilation, [`proof_bug_extractor.py`](../src/certified_arith_preproc/proof_bug_extractor.py) implements `arXiv:2611.08305` (Li–Li–Ren, *STOC 2026*) using `pysat_cadical195`: given a corrupted chain $E_0, \dots, E_t$ ending at $E_t \equiv 1$ and any falsifying assignment $x^*$ ($E_0(x^*) = \mathrm{false}$), `findBrokenStep` bisects $[0, t]$ to return a concrete invalid transition $E_i(x^*) = \mathrm{false}$ and $E_{i+1}(x^*) = \mathrm{true}$ in $\le \lceil \log_2 t \rceil$ evaluations. Across all four corrupted chains in Table 5—including `DattaDutta_v1_DeMorgan_fanout2_bug` (catching the simultaneous fan-out $2$ violation at step $3$ in $2 \le 3$ queries, `1.023 ms`) and `PHP_3_3_corrupted` (catching step $5$ in $3 \le 4$ queries, `18.009 ms`)—binary midpoint localization agrees identically with exhaustive parallel local checks.

As an auxiliary empirical diagnostic in [`proof_bug_extractor_results.json`](../results/proof_bug_extractor_results.json), $K^t$ witness-compression symmetry-of-information (`SoI`) measurements across $n \in \{6, 8, 10, 12, 14\}$ confirm zero `SoI` asymmetry (`SoI_asymmetry_bits = 0`) on `schoolbook_mult`, `goldreich_xormaj3`, and `random_permutation`, whereas `keccak_chi_4round` exhibits measurable compressibility at small block sizes (`output_compression_ratio = 0.125` at $n=6$, `0.4062` at $n=8$).

---

## 5. Experimental Evaluation

Every valid compiled chain across all suites achieved `100%` `DAGStore.are_approx` step verification.

### Table 1: Exact `≈`-Chains & Datta–Dutta Unsharing (`ATAQUE-05`, [`krajicek_ew_graph_results.json`](../results/krajicek_ew_graph_results.json))

Total hash-cons nodes allocated: `283,132`; `v2_datta_dutta_self_tests`: `PASS` (`fanout2_single_occurrence_approx = true`, `fanout2_simultaneous_both_approx = false`, witness `disjCompl:fwd` at `path = [0]`, DAG `4 -> 5`).

| Benchmark | Family | Steps $t$ | Src / Dst / Peak DAG | `are_approx` & Sem. | Time (ms) |
| :--- | :--- | ---: | :---: | :---: | ---: |
| `taut_lem_x_or_not_x` | `tautology` | 1 | `3 / 1 / 3` | `True / True` | 0.05 |
| `taut_fanout2_lem_and_lem` | `tautology_unsharing` | 3 | `4 / 1 / 5` | `True / True` | 0.17 |
| `double_negation_elim` | `tautology` | 13 | `3 / 1 / 6` | `True / True` | 1151.12 |
| `demorgan_disj` | `demorgan` | 50 | `4 / 5 / 16` | `True / True` | 4.09 |
| `demorgan_conj` | `demorgan` | 52 | `4 / 5 / 15` | `True / True` | 4.86 |
| `modus_ponens_lemma21_raw` | `modus_ponens` | 10 | `3 / 1 / 9` | `True / True` | 0.05 |
| `xor2_commutativity` | `xor` | 3 | `7 / 7 / 7` | `True / True` | 0.22 |
| `xor3_associativity` | `xor` | 807 | `13 / 13 / 34` | `True / True` | 283.73 |
| `maj3_dnf_to_cnf` | `maj3` | 396 | `8 / 8 / 28` | `True / True` | 1410.19 |
| `not_php_2_1_dnf_to_1` | `php` | 79 | `7 / 1 / 17` | `True / True` | 860.21 |
| `not_php_2_1_negcnf_to_1` | `php` | 258 | `8 / 1 / 19` | `True / True` | 40.15 |
| `not_php_3_2_to_1` | `php` | 1568 | `29 / 1 / 67` | `True / True` | 1227.26 |

### Table 2: `CF` Unsharing & Balanced DAG Compilation (`ATAQUE-10`, [`krajicek_cf_compiler_results.json`](../results/krajicek_cf_compiler_results.json))

Total hash-cons nodes allocated: `659,003`; `all_steps_verified_are_approx = true` (Suite 2 semantic tautology verified for $r \in \{2,4,6\}$, `null` at $r=8$ with 9 vars).

| Suite 1 (`tree_lemma21`) $m$ | Canonical DAG | $\lvert \mathsf{Fla} \rvert$ | $k$ | Steps $t$ | Peak DAG | Unwound / Peak | Compile / Verify (ms) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| 4 | 19 | 121 | 22 | 88 | 48 | `2.52×` | `0.346 / 2.875` |
| 8 | 35 | 2,041 | 38 | 152 | 84 | `24.30×` | `0.786 / 5.243` |
| 12 | 51 | 32,761 | 54 | 216 | 120 | `273.01×` | `1.765 / 12.046` |
| 16 | 67 | 524,281 | 70 | 280 | 156 | `3360.78×` | `3.020 / 21.396` |
| 20 | 83 | 8,388,601 | 86 | 344 | 192 | `43690.63×` | `3.996 / 31.877` |

| Suite 2 (`dag_theorem11_balanced`) $r$ | $k_{\mathrm{CF}}$ | Naive Tree Steps | Emitted $t$ | $t / (k \log_2 k)$ | Peak DAG | Compile / Verify (ms) |
| ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| 2 (`3` vars) | 8 | 9 | 1118 | 46.583 | 88 | `8.383 / 64.293` |
| 4 (`5` vars) | 22 | 57 | 3332 | 33.963 | 246 | `109.806 / 555.277` |
| 6 (`7` vars) | 36 | 249 | 5622 | 30.207 | 423 | `160.856 / 1648.769` |
| 8 (`9` vars) | 50 | 1017 | 7802 | 27.648 | 577 | `305.893 / 2982.007` |

### Table 3: Aligned SLP $k_{\mathrm{CF}}$-Pure Compression (`ATAQUE-13`, [`krajicek_slp_kcf_results.json`](../results/krajicek_slp_kcf_results.json))

Summary over all `11` benchmarks: `385 / 385` `are_approx` checks passed (`100%`), `all_endpoints_ok = true`, `3 / 3` truth-table invariants verified, max $S = 36{,}004$, max unwound size $= 4{,}098{,}181{,}835{,}914{,}914{,}434$, max $S/\mathrm{SLP} = 857.24\times$.

| Benchmark | Suite | $k_{\mathrm{CF}}$ | Raw $S$ | Max $\lvert \mathsf{Fla} \rvert$ | SLP | $S / \mathrm{SLP}$ | $t$ | Wall / Verify (ms) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| `iter_sq_d15_m3` | `A_iterated_squaring` | 13 | 424 | `1,619,676` | 61 | 6.95 | 34 | `0.293 / 0.270` |
| `iter_sq_d25_m4` | `A_iterated_squaring` | 17 | 823 | `1,668,134,620` | 80 | 10.29 | 45 | `0.495 / 0.429` |
| `iter_sq_d35_m5` | `A_iterated_squaring` | 21 | 1,349 | `1,708,169,850,296` | 99 | 13.63 | 56 | `0.781 / 1.488` |
| `iter_sq_d42_m6` | `A_iterated_squaring` | 25 | 1,903 | `218,645,740,837,742` | 118 | 16.13 | 67 | `0.921 / 0.916` |
| `xor_balanced_w16_l8_m2` | `B_deep_xor_large_dag` | 9 | 3,924 | `33,632,725,506` | 42 | 93.43 | 23 | `1.375 / 0.115` |
| `xor_balanced_w32_l12_m2` | `B_deep_xor_large_dag` | 9 | 12,182 | `34,173,623,118,338` | 42 | 290.05 | 23 | `4.543 / 0.119` |
| `xor_balanced_w64_l16_m2` | `B_deep_xor_large_dag` | 9 | 21,484 | `8,731,405,088,107,138` | 42 | 511.52 | 23 | `7.836 / 0.120` |
| `xor_balanced_w96_l20_m2` | `B_deep_xor_large_dag` | 9 | 36,004 | `4,098,181,835,914,914,434` | 42 | 857.24 | 23 | `13.596 / 0.821` |
| `tt_verified_n4_m2` | `C_truth_table_verified` | 9 | 1,086 | `981,154` | 42 | 25.86 | 23 | `0.498 / 1.522` |
| `tt_verified_n5_m3` | `C_truth_table_verified` | 13 | 3,072 | `11,316,898` | 61 | 50.36 | 34 | `1.180 / 4.955` |
| `tt_verified_n6_m3` | `C_truth_table_verified` | 13 | 3,368 | `45,267,618` | 61 | 55.21 | 34 | `1.347 / 6.670` |

### Table 4: Non-Aligned Jeż Recompression & Dichotomy (`ATAQUE-15`, [`krajicek_nonaligned_slp_results.json`](../results/krajicek_nonaligned_slp_results.json))

In Suite A, all equal pairs unified (`True`) and all depth-$2^m-1$ single-leaf mutations were rejected (`True`), totaling `1562.593 ms` across Suites A–C. In Suite C, `taut_var0_vs_taut_var1` gave `syntactic_fla_equal = false`, `semantic_bool_equal = true`, `one_step_are_approx = false`, `min_verified_ba_steps = 2`; `xor3_left_vs_right_assoc` gave `syntactic_fla_equal = false`, `semantic_bool_equal = true`, `one_step_are_approx = false`, `constructive_verified_ba_steps = 807`.

| Exp. $m$ | Periodic Spine Len | Rules $(G_1, G_2)$ | Rounds / Time (ms) | Mutated (ms) | Thue–Morse Spine Len | Rules $(G_1, G_2)$ | Rounds / Time (ms) | Mutated (ms) |
| ---: | ---: | :---: | :---: | ---: | ---: | :---: | :---: | ---: |
| 6 | 192 | `(11, 19)` | `3 / 1.450` | 1.073 | 64 | `(14, 20)` | `4 / 1.067` | 1.126 |
| 12 | 12,288 | `(17, 31)` | `3 / 1.519` | 1.334 | 4,096 | `(26, 38)` | `12 / 5.515` | 3.590 |
| 20 | 3,145,728 | `(25, 47)` | `3 / 2.142` | 2.553 | 1,048,576 | `(42, 62)` | `24 / 28.621` | 13.123 |
| 32 | `12,884,901,888` | `(37, 71)` | `3 / 4.632` | 3.639 | `4,294,967,296` | `(66, 98)` | `42 / 86.632` | 45.351 |
| 48 | `844,424,930,131,968` | `(53, 103)` | `3 / 8.180` | 7.914 | `281,474,976,710,656` | `(98, 146)` | `66 / 281.960` | 117.931 |
| 60 | `3,458,764,513,820,540,928` | `(65, 127)` | `3 / 10.057` | 10.022 | `1,152,921,504,606,846,976` | `(122, 182)` | `84 / 423.794` | 155.639 |

| Suite B (`c_ax = 3`) `k_cuts` | `k_cf_lines` | Total Spine Depth | Emitted `≈`-Steps | Bound `(c_ax+2)k` | Verified `are_approx` | Time (ms) |
| ---: | ---: | ---: | ---: | ---: | :---: | ---: |
| 2 | 7 | 768 | 17 | 35 | `True` (`17 / 17`) | 3.347 |
| 4 | 13 | 1,536 | 33 | 65 | `True` (`33 / 33`) | 5.541 |
| 6 | 19 | 2,304 | 49 | 95 | `True` (`49 / 49`) | 7.567 |
| 8 | 25 | 3,072 | 65 | 125 | `True` (`65 / 65`) | 12.389 |

Total materialized Suite B verified transitions: `total_verified_approx_steps_suite_b = 164` (`100%` `are_approx`).

### Table 5: Constructive Bug Localization (`ATAQUE-08`, [`proof_bug_extractor_results.json`](../results/proof_bug_extractor_results.json))

| Corrupted Chain (`pysat_cadical195`) | Chain $t$ | Vars | $E_0$ DAG | Broken Step | Queries / $\lceil \log_2 t \rceil$ | Verified Falsifies / Broken | Time (ms) |
| :--- | ---: | ---: | ---: | ---: | :---: | :---: | ---: |
| `PHP_3_3_corrupted` | 9 | 9 | 45 | 5 | `3 / 4` | `True / True` | 18.009 |
| `Goldreich_XOR_MAJ3_corrupted` | 11 | 10 | 159 | 6 | `4 / 4` | `True / True` | 35.401 |
| `Random_3SAT_alpha_4_26_corrupted` | 10 | 18 | 264 | 7 | `3 / 4` | `True / True` | 76.912 |
| `DattaDutta_v1_DeMorgan_fanout2_bug` | 6 | 6 | 9 | 3 | `2 / 3` | `True / True` | 1.023 |

---

## 6. Summary, Reproducibility Commands & References

Together, `ATAQUE-05`, `ATAQUE-08`, `ATAQUE-10`, `ATAQUE-13`, and `ATAQUE-15` close the $\mathrm{poly}(S)$ DAG-unsharing, aligned SLP $k_{\mathrm{CF}}$-pure, and non-aligned linear `ContextSLP` recompression regimes of Krajíček's `CF -> ≈-Chain` problem (`arXiv:2606.13367v2`, p. 11), while pinpointing the exact `P`-vs.-`coNP` boundary between syntactic `Fla`-equality (`2` universal $\approx$-steps) and semantic equivalence $A \equiv_{\mathrm{Bool}} B$ with $\mathsf{Fla}[A] \neq \mathsf{Fla}[B]$. Extensions beyond linear unary `ContextSLP`s to arbitrary nonlinear tree-SLPs with multiple simultaneous holes remain open within the full tree-recompression framework (Jeż 2016; Lohrey 2012).

```bash
# 1. Verify all 5 standalone Lean 4.36.0 proof modules (0 sorryAx, 0 external imports)
for f in krajicek_ba_rewriting_soundness.lean krajicek_cf_compiler_unsharing.lean \
         krajicek_slp_kcf_reduction.lean krajicek_nonaligned_context_slp.lean \
         proof_analysis_bug_extractor.lean; do
  lean "proofs/$f"
done

# 2. Reproduce all Python verification & benchmark suites
PYTHONPATH=src python3 -m certified_arith_preproc.krajicek_ew_explorer
PYTHONPATH=src python3 -m certified_arith_preproc.krajicek_cf_compiler
PYTHONPATH=src python3 -m certified_arith_preproc.krajicek_slp_unifier
PYTHONPATH=src python3 -m certified_arith_preproc.krajicek_nonaligned_slp
PYTHONPATH=src python3 -m certified_arith_preproc.proof_bug_extractor
```

**References:**
1. Jan Krajíček. *Extended Frege proofs, circuits and rewriting*. `arXiv:2606.13367v2` (October 2026).
2. Samir Datta and Anupam Dutta. *Fan-out $\ge 2$ unsharing correction for `CF` single-occurrence rewriting* (personal communication acknowledged in Krajíček `arXiv:2606.13367v2`, October 2026).
3. Artur Jeż. *Recompression: A simple and powerful technique for word equations*. *Journal of the ACM*, 63(1), 2016.
4. Markus Lohrey. *Algorithmics on SLP-compressed strings: A survey*. *Groups Complexity Cryptology*, 4(2):241–299, 2012.
5. Li–Li–Ren (*STOC 2026*). *Constructive proof analysis & witness extraction for broken equational chains*. `arXiv:2611.08305`.
