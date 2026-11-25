#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TIMEOUT="${1:-300}"
if [[ "${1:-}" == "--timeout" && -n "${2:-}" ]]; then
  TIMEOUT="$2"
fi

# Fallback PATH additions for standard user installations if not already on PATH
for p in "$HOME/.elan/bin" "$HOME/.local/bin" "$HOME/.cargo/bin"; do
  if [[ -d "$p" && ":$PATH:" != *":$p:"* ]]; then
    export PATH="$p:$PATH"
  fi
done

cd "$REPO_ROOT"

echo "[1/3] Checking Lean 4 local rewrite-rule soundness (proofs/rule_soundness.lean)..."
lean_out="$(lean proofs/rule_soundness.lean)"
echo "$lean_out" | tail -n 10
if echo "$lean_out" | grep -q "sorryAx"; then
  echo "ERROR: sorryAx detected in Lean output!" >&2
  exit 1
fi

echo "[2/3] Emitting and checking VeriPB 3.0.2 proofs (6x6..16x16 scrambled miters)..."
uv run --with-editable . python -m certified_arith_preproc.veripb_emitter \
  --bits 6 8 10 12 16 \
  --out-dir results/veripb_proofs \
  --json-out results/veripb_results.json

echo "[3/3] Running wall-clock solver comparison (timeout=${TIMEOUT}s)..."
uv run --with-editable '.[benchmarks]' python -m certified_arith_preproc.benchmark_solvers \
  --timeout "$TIMEOUT" \
  --cnf-dir cnf_samples \
  --json-out results/benchmark_results.json

echo "All reproducibility checks completed."
