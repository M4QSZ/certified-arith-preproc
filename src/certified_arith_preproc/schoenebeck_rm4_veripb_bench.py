"""ATAQUE-14: Native VeriPB 3.0.2 .pbp Emission in schoenebeck_rs + RM(4,5) 5-Local Simplices
on Schoenebeck Random 3-SAT (n in [64, 75, 90, 105], alpha=6.2).

Compares `schoenebeck_rs --rm3` (RM(3,4) tetrahedral collisions) vs `schoenebeck_rs --rm4`
(RM(4,5) 5-local simplices & 5-local collisions), emits native VeriPB 3.0.2 `.pbp` proofs into
`results/ataque14_pbp/` for solved instances (including n=64, n=75, and n=90 seed=0), verifies
every emitted proof with `veripb --cnf` (requiring exit 0 + `s VERIFIED UNSATISFIABLE`), and
checks 0/20 false UNSATs on alpha=3.5 SAT controls in both modes.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any

import numpy as np
from pysat.solvers import Cadical195

ROOT = Path(__file__).resolve().parents[2]
RUST_BIN = ROOT / "schoenebeck_rs" / "target" / "release" / "schoenebeck_rs"
OUT_JSON = ROOT / "results" / "ataque14_schoenebeck_veripb_results.json"
PBP_DIR = ROOT / "results" / "ataque14_pbp"

NS = [64, 75, 90, 105]
ALPHA = 6.2
SEEDS_PER_N = 6
BASE_SEED = 2026112600
SAT_CONTROL_ALPHA = 3.5
SAT_CONTROL_TRIALS = 20


def generate_verified_unsat_3sat(
    n_vars: int, seed: int, alpha: float = ALPHA
) -> tuple[int, list[list[int]], int]:
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


def generate_verified_sat_3sat(
    n_vars: int, seed: int, alpha: float = SAT_CONTROL_ALPHA
) -> tuple[int, list[list[int]]]:
    """Deterministically sample random 3-SAT at density `alpha` until CaDiCaL195 certifies SAT."""
    m_clauses = int(round(alpha * n_vars))
    rng = np.random.default_rng(seed)
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
        with Cadical195(bootstrap_with=clauses) as solver:
            if solver.solve():
                return m_clauses, clauses


def to_dimacs(n_vars: int, clauses: list[list[int]]) -> str:
    lines = [f"p cnf {n_vars} {len(clauses)}"]
    for cl in clauses:
        lines.append(" ".join(map(str, cl)) + " 0")
    return "\n".join(lines) + "\n"


def run_schoenebeck_rs(
    n_vars: int,
    clauses: list[list[int]],
    mode: str = "rm3",
    cnf_path: Path | None = None,
    pbp_path: Path | None = None,
) -> dict[str, Any]:
    flag = "--rm4" if mode == "rm4" else "--rm3"
    cmd = [str(RUST_BIN), flag]
    if pbp_path is not None:
        cmd.extend(["--emit-pbp", str(pbp_path)])
    t0 = time.perf_counter()
    if cnf_path is not None:
        cmd.append(str(cnf_path))
        out = subprocess.check_output(cmd, text=True)
    else:
        cmd.append("-")
        dimacs = to_dimacs(n_vars, clauses)
        out = subprocess.check_output(cmd, input=dimacs, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    data = json.loads(out.strip())
    data["wall_ms_including_spawn"] = round(wall_ms, 3)
    return data


def verify_veripb(cnf_path: Path, pbp_path: Path, veripb_bin: str) -> dict[str, Any]:
    t0 = time.perf_counter()
    proc = subprocess.run(
        [veripb_bin, "--cnf", str(cnf_path), str(pbp_path)],
        capture_output=True,
        text=True,
        timeout=180,
    )
    check_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    verified = proc.returncode == 0 and ("s VERIFIED UNSATISFIABLE" in proc.stdout)
    return {
        "verified": verified,
        "returncode": proc.returncode,
        "veripb_check_ms": check_ms,
        "status_line": "s VERIFIED UNSATISFIABLE" if verified else (proc.stdout + proc.stderr).strip()[:300],
    }


def run_sat_controls(n_trials: int = SAT_CONTROL_TRIALS) -> dict[str, int]:
    false_rm3 = 0
    false_rm4 = 0
    for idx in range(n_trials):
        n_vars = 64
        _, clauses = generate_verified_sat_3sat(n_vars, 888000 + idx, SAT_CONTROL_ALPHA)
        r3 = run_schoenebeck_rs(n_vars, clauses, mode="rm3")
        r4 = run_schoenebeck_rs(n_vars, clauses, mode="rm4")
        if r3["unsat"]:
            false_rm3 += 1
        if r4["unsat"]:
            false_rm4 += 1
    return {
        "trials": n_trials,
        "alpha": SAT_CONTROL_ALPHA,
        "rm3_false_unsat": false_rm3,
        "rm4_false_unsat": false_rm4,
    }


def main() -> None:
    if not RUST_BIN.exists():
        raise FileNotFoundError(f"Rust binary not found: {RUST_BIN}")
    veripb_bin = shutil.which("veripb") or "/home/miguel/.local/bin/veripb"
    if not Path(veripb_bin).exists():
        raise FileNotFoundError(f"veripb binary not found: {veripb_bin}")

    PBP_DIR.mkdir(parents=True, exist_ok=True)
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)

    t_total0 = time.perf_counter()

    # 1) SAT Controls (20 verified-SAT instances at alpha=3.5)
    sat_ctrl = run_sat_controls(SAT_CONTROL_TRIALS)
    print(
        f"SAT Controls ({sat_ctrl['trials']} instances, alpha={SAT_CONTROL_ALPHA}): "
        f"rm3_false_unsat={sat_ctrl['rm3_false_unsat']}, rm4_false_unsat={sat_ctrl['rm4_false_unsat']}",
        flush=True,
    )
    if sat_ctrl["rm3_false_unsat"] != 0 or sat_ctrl["rm4_false_unsat"] != 0:
        raise RuntimeError(f"Soundness failure on SAT controls: {sat_ctrl}")

    # 2) Schoenebeck UNSAT benchmark: n in [64, 75, 90, 105], 6 seeds each, --rm3 vs --rm4 + VeriPB 3.0.2
    instances: list[dict[str, Any]] = []
    pbp_proofs: list[dict[str, Any]] = []
    by_n: dict[int, list[dict[str, Any]]] = {}

    for n_vars in NS:
        for seed_idx in range(SEEDS_PER_N):
            seed = BASE_SEED + 1000 * n_vars + seed_idx
            m_clauses, clauses, attempts = generate_verified_unsat_3sat(n_vars, seed, ALPHA)

            cnf_path = PBP_DIR / f"schoenebeck_n{n_vars}_seed{seed_idx}.cnf"
            cnf_path.write_text(to_dimacs(n_vars, clauses), encoding="utf-8")

            pbp_rm3 = PBP_DIR / f"schoenebeck_n{n_vars}_seed{seed_idx}_rm3.pbp"
            pbp_rm4 = PBP_DIR / f"schoenebeck_n{n_vars}_seed{seed_idx}_rm4.pbp"

            res_rm3 = run_schoenebeck_rs(n_vars, clauses, mode="rm3", cnf_path=cnf_path, pbp_path=pbp_rm3)
            res_rm4 = run_schoenebeck_rs(n_vars, clauses, mode="rm4", cnf_path=cnf_path, pbp_path=pbp_rm4)

            ver_rm3: dict[str, Any] | None = None
            ver_rm4: dict[str, Any] | None = None

            if res_rm3["unsat"] and pbp_rm3.exists():
                ver_rm3 = verify_veripb(cnf_path, pbp_rm3, veripb_bin)
                pbp_proofs.append(
                    {
                        "n": n_vars,
                        "m": m_clauses,
                        "seed_idx": seed_idx,
                        "seed": seed,
                        "mode": "rm3",
                        "status": res_rm3["status"],
                        "pbp_lines": res_rm3["pbp_lines"],
                        "cnf_path": str(cnf_path),
                        "pbp_path": str(pbp_rm3),
                        **ver_rm3,
                    }
                )
            elif pbp_rm3.exists():
                pbp_rm3.unlink()

            if res_rm4["unsat"] and pbp_rm4.exists():
                ver_rm4 = verify_veripb(cnf_path, pbp_rm4, veripb_bin)
                pbp_proofs.append(
                    {
                        "n": n_vars,
                        "m": m_clauses,
                        "seed_idx": seed_idx,
                        "seed": seed,
                        "mode": "rm4",
                        "status": res_rm4["status"],
                        "pbp_lines": res_rm4["pbp_lines"],
                        "cnf_path": str(cnf_path),
                        "pbp_path": str(pbp_rm4),
                        **ver_rm4,
                    }
                )
            elif pbp_rm4.exists():
                pbp_rm4.unlink()

            if not res_rm3["unsat"] and not res_rm4["unsat"] and cnf_path.exists():
                cnf_path.unlink()

            entry = {
                "n": n_vars,
                "m": m_clauses,
                "seed_idx": seed_idx,
                "seed": seed,
                "sampling_attempts": attempts,
                "rm3": {**res_rm3, "veripb": ver_rm3},
                "rm4": {**res_rm4, "veripb": ver_rm4},
            }
            instances.append(entry)
            by_n.setdefault(n_vars, []).append(entry)

            v3_tag = f"VERIFIED({ver_rm3['veripb_check_ms']}ms)" if ver_rm3 and ver_rm3["verified"] else ("FAIL_PBP" if ver_rm3 else "-")
            v4_tag = f"VERIFIED({ver_rm4['veripb_check_ms']}ms)" if ver_rm4 and ver_rm4["verified"] else ("FAIL_PBP" if ver_rm4 else "-")
            print(
                f"n={n_vars:3d} s={seed_idx} | "
                f"RM3={'UNSAT' if res_rm3['unsat'] else 'FAIL ':5s} ({res_rm3['ms']:7.2f}ms, {res_rm3['status']:19s}, pbp={v3_tag:17s}) | "
                f"RM4={'UNSAT' if res_rm4['unsat'] else 'FAIL ':5s} ({res_rm4['ms']:7.2f}ms, {res_rm4['status']:19s}, pbp={v4_tag})",
                flush=True,
            )

    summary_by_n = []
    print("\n=== ATAQUE-14 SUMMARY BY n (alpha=6.2, 6 seeds per n) ===")
    print(f"{'n':>4} | {'RM3 Solved':>12} | {'RM4 Solved':>12} | {'RM3 Mean ms':>11} | {'RM4 Mean ms':>11} | {'VeriPB Verified':>15}")
    print("-" * 80)
    for n_vars in NS:
        items = by_n[n_vars]
        k = len(items)
        rm3_cnt = sum(1 for x in items if x["rm3"]["unsat"])
        rm4_cnt = sum(1 for x in items if x["rm4"]["unsat"])
        rm3_ms = round(sum(x["rm3"]["ms"] for x in items) / k, 2)
        rm4_ms = round(sum(x["rm4"]["ms"] for x in items) / k, 2)
        pbp_n = [p for p in pbp_proofs if p["n"] == n_vars]
        pbp_ok = sum(1 for p in pbp_n if p["verified"])
        summary_by_n.append(
            {
                "n": n_vars,
                "m": items[0]["m"],
                "alpha": ALPHA,
                "trials": k,
                "rm3_unsat_count": rm3_cnt,
                "rm3_unsat_rate": round(rm3_cnt / k, 4),
                "rm3_mean_ms": rm3_ms,
                "rm4_unsat_count": rm4_cnt,
                "rm4_unsat_rate": round(rm4_cnt / k, 4),
                "rm4_mean_ms": rm4_ms,
                "veripb_emitted": len(pbp_n),
                "veripb_verified": pbp_ok,
            }
        )
        print(
            f"{n_vars:4d} | {rm3_cnt}/{k} ({rm3_cnt/k*100:5.1f}%) | "
            f"{rm4_cnt}/{k} ({rm4_cnt/k*100:5.1f}%) | "
            f"{rm3_ms:11.2f} | {rm4_ms:11.2f} | {pbp_ok:>7d}/{len(pbp_n):<7d}"
        )

    total_emitted = len(pbp_proofs)
    total_verified = sum(1 for p in pbp_proofs if p["verified"])
    print(f"\nTotal VeriPB 3.0.2 proofs verified: {total_verified}/{total_emitted}")

    payload = {
        "protocol": "ATAQUE-14",
        "description": "Native VeriPB 3.0.2 .pbp Emission in schoenebeck_rs + RM(4,5) 5-Local Simplices on Schoenebeck n=64..105",
        "alpha": ALPHA,
        "ns": NS,
        "seeds_per_n": SEEDS_PER_N,
        "sat_controls": sat_ctrl,
        "veripb_total_emitted": total_emitted,
        "veripb_total_verified": total_verified,
        "total_wall_s": round(time.perf_counter() - t_total0, 2),
        "summary_by_n": summary_by_n,
        "veripb_proofs": pbp_proofs,
        "instances": instances,
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Saved results to {OUT_JSON}")

    if total_verified != total_emitted:
        raise RuntimeError(f"VeriPB verification failed on {total_emitted - total_verified} proofs!")


if __name__ == "__main__":
    main()
