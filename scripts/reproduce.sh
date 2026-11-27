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

echo "[1/3] Checking all 15 standalone Lean 4.36.0 soundness suites (0 sorryAx)..."
for lf in proofs/*.lean; do
  echo "  -> $lf"
  l_out="$(lean "$lf")"
  if echo "$l_out" | grep -q "sorryAx"; then
    echo "ERROR: sorryAx detected in $lf!" >&2
    exit 1
  fi
done

echo "[2/3] Building native Rust engines (rust_core/cap-veronese-rs & schoenebeck_rs)..."
cargo build --release --manifest-path rust_core/Cargo.toml
cargo build --release --manifest-path schoenebeck_rs/Cargo.toml

echo "[3/3] Verifying unified corpus (11 UNSAT + 4 SAT controls) & Fase I-III frontier labs..."
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.benchmark_v05_unified
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.krajicek_ew_explorer
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.krajicek_cf_compiler
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.krajicek_slp_unifier
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.krajicek_nonaligned_slp
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.witt_noncomm_ips_explorer
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.witt_higher_torsion_snf
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.witt_kneser_nc_separation
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.proof_bug_extractor
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.schoenebeck_rm3_tetrahedral_bench
PYTHONPATH="$REPO_ROOT/src" .venv/bin/python -m certified_arith_preproc.schoenebeck_rm4_veripb_bench

echo "All reproducibility checks completed."
