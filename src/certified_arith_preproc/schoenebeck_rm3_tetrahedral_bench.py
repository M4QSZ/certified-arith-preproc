"""ATAQUE-11: Crossing/Testing the n*=75 Schoenebeck Random 3-SAT Threshold
via Native Rust Tetrahedral RM(3, 4) Collisions + Fast Witt Pairwise Cutting Planes.

Re-generates the exact 30 verified-UNSAT random 3-SAT instances from
`results/protocol_xxi_schoenebeck_results.json` (n in [64, 75, 90, 105, 120],
6 seeds each at alpha=6.2), runs `schoenebeck_rs` on all 30 instances,
and compares against v0.5 Python RM(2,3) (+) CG-Witt.
"""

from __future__ import annotations

import json
import subprocess
import time
from pathlib import Path
from typing import Any

import numpy as np
from pysat.solvers import Cadical195

ROOT = Path(__file__).resolve().parents[2]
BASELINE_JSON = ROOT / "results" / "protocol_xxi_schoenebeck_results.json"
OUT_JSON = ROOT / "results" / "ataque11_tetrahedral_schoenebeck_results.json"
RUST_BIN = ROOT / "schoenebeck_rs" / "target" / "release" / "schoenebeck_rs"


def generate_verified_unsat_3sat(n_vars: int, seed: int, alpha: float = 6.2) -> tuple[int, list[list[int]], int]:
    """Deterministically sample random 3-SAT at density `alpha` until CaDiCaL195 certifies UNSAT."""
    m_clauses = int(round(alpha * n_vars))
    rng = np.random.default_rng(seed)
    vars_pool = np.arange(1, n_vars + 1)
    attempts = 0
    while True:
        attempts += 1
        clauses = [
            [
                int(v * s)
                for v, s in zip(
                    rng.choice(vars_pool, size=3, replace=False),
                    rng.choice([-1, 1], size=3),
                )
            ]
            for _ in range(m_clauses)
        ]
        with Cadical195(bootstrap_with=clauses) as solver:
            if not solver.solve():
                return m_clauses, clauses, attempts


def to_dimacs(n_vars: int, clauses: list[list[int]]) -> str:
    lines = [f"p cnf {n_vars} {len(clauses)}"]
    for cl in clauses:
        lines.append(" ".join(map(str, cl)) + " 0")
    return "\n".join(lines) + "\n"


def run_schoenebeck_rs(n_vars: int, clauses: list[list[int]]) -> dict[str, Any]:
    dimacs = to_dimacs(n_vars, clauses)
    t0 = time.perf_counter()
    out = subprocess.check_output([str(RUST_BIN), "-"], input=dimacs, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    data = json.loads(out.strip())
    data["wall_ms_including_spawn"] = round(wall_ms, 3)
    return data


def verify_sat_soundness(n_trials: int = 20) -> int:
    false_unsat = 0
    for idx in range(n_trials):
        rng = np.random.default_rng(777000 + idx)
        n_vars = 64
        m_clauses = int(round(3.8 * n_vars))
        vars_pool = np.arange(1, n_vars + 1)
        while True:
            clauses = [
                [
                    int(v * s)
                    for v, s in zip(
                        rng.choice(vars_pool, size=3, replace=False),
                        rng.choice([-1, 1], size=3),
                    )
                ]
                for _ in range(m_clauses)
            ]
            with Cadical195(bootstrap_with=clauses) as s:
                if s.solve():
                    break
        res = run_schoenebeck_rs(n_vars, clauses)
        if res["unsat"]:
            false_unsat += 1
    return false_unsat


def main() -> None:
    if not RUST_BIN.exists():
        raise FileNotFoundError(f"Rust binary not found: {RUST_BIN}")

    baseline = json.loads(BASELINE_JSON.read_text())
    alpha = float(baseline["alpha"])
    base_summary_by_n = {row["n"]: row for row in baseline["summary_by_n"]}
    base_instances = baseline["instances"]

    sat_false_unsat = verify_sat_soundness(20)
    print(f"SAT Soundness Check (20 verified-SAT instances): false_unsat={sat_false_unsat}")
    if sat_false_unsat != 0:
        raise RuntimeError(f"Soundness failure: {sat_false_unsat} false UNSATs detected!")

    t_total0 = time.perf_counter()
    results_instances: list[dict[str, Any]] = []
    by_n: dict[int, list[dict[str, Any]]] = {}

    for inst in base_instances:
        n_vars = int(inst["n"])
        seed_idx = int(inst["seed_idx"])
        seed = int(inst["seed"])
        m_clauses, clauses, attempts = generate_verified_unsat_3sat(n_vars, seed, alpha)
        rs_res = run_schoenebeck_rs(n_vars, clauses)

        entry = {
            "n": n_vars,
            "m": m_clauses,
            "seed_idx": seed_idx,
            "seed": seed,
            "sampling_attempts": attempts,
            "v05_python_rm2_cg": inst["adelic_coupled"],
            "v06_rust_rm3_witt": rs_res,
        }
        results_instances.append(entry)
        by_n.setdefault(n_vars, []).append(entry)
        print(
            f"n={n_vars:3d} seed_idx={seed_idx} seed={seed} | "
            f"v0.5={'UNSAT' if inst['adelic_coupled']['unsat'] else 'FAIL ':5s} ({inst['adelic_coupled']['ms']:9.2f} ms) | "
            f"v0.6={'UNSAT' if rs_res['unsat'] else 'FAIL ':5s} ({rs_res['ms']:7.2f} ms, {rs_res['status']})"
        )

    summary_by_n = []
    print("\n=== SUMMARY BY n (alpha=6.2, 6 seeds per n) ===")
    print(f"{'n':>4} | {'v0.5 Py Rate':>12} | {'v0.6 Rs Rate':>12} | {'v0.5 Mean ms':>12} | {'v0.6 Mean ms':>12} | {'Speedup':>9}")
    print("-" * 76)
    for n_vars in sorted(by_n.keys()):
        items = by_n[n_vars]
        trials = len(items)
        v06_unsat = sum(1 for x in items if x["v06_rust_rm3_witt"]["unsat"])
        v06_rate = round(v06_unsat / trials, 4)
        v06_mean_ms = round(sum(x["v06_rust_rm3_witt"]["ms"] for x in items) / trials, 2)

        b_row = base_summary_by_n[n_vars]
        v05_unsat = int(b_row["adelic_coupled_unsat_count"])
        v05_rate = float(b_row["adelic_coupled_unsat_rate"])
        v05_mean_ms = float(b_row["adelic_coupled_mean_ms"])
        speedup = round(v05_mean_ms / max(v06_mean_ms, 0.001), 1)

        summary_by_n.append({
            "n": n_vars,
            "m": items[0]["m"],
            "alpha": alpha,
            "trials": trials,
            "v05_python_unsat_count": v05_unsat,
            "v05_python_unsat_rate": v05_rate,
            "v05_python_mean_ms": v05_mean_ms,
            "v06_rust_unsat_count": v06_unsat,
            "v06_rust_unsat_rate": v06_rate,
            "v06_rust_mean_ms": v06_mean_ms,
            "speedup_x": speedup,
        })
        print(
            f"{n_vars:4d} | {v05_unsat}/{trials} ({v05_rate*100:5.1f}%) | "
            f"{v06_unsat}/{trials} ({v06_rate*100:5.1f}%) | "
            f"{v05_mean_ms:12.2f} | {v06_mean_ms:12.2f} | {speedup:8.1f}x"
        )

    out_payload = {
        "protocol": "ATAQUE-11",
        "description": "Schoenebeck Random 3-SAT Threshold: v0.5 Python RM(2,3)(+)CG-Witt vs v0.6 Native Rust Tetrahedral RM(3,4)(+)Witt",
        "alpha": alpha,
        "total_instances": len(results_instances),
        "sat_soundness_check_false_unsat": sat_false_unsat,
        "total_wall_s": round(time.perf_counter() - t_total0, 2),
        "summary_by_n": summary_by_n,
        "instances": results_instances,
    }
    OUT_JSON.write_text(json.dumps(out_payload, indent=2))
    print(f"\nSaved results to {OUT_JSON}")


if __name__ == "__main__":
    main()
