"""Wall-clock solver comparison harness against Kissat, CryptoMiniSat 5, and optional RoundingSat."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

from .benchmarks import (
    gen_deep_keccak_chi_sponge_php,
    gen_goldreich_prg_3cnf,
    gen_schoolbook_vs_wallace_miter_3cnf,
    gen_shifted_cubic_sponge_miter,
    gen_wire_eliminated_php_tseitin,
)
from .cnf_utils import read_dimacs, scramble_cnf, write_dimacs
from .macaulay_cp import solve_hybrid_preproc


def run_kissat_wallclock(kissat_bin: str, cnf_path: Path, timeout_s: float) -> tuple[str, float]:
    if not kissat_bin or not Path(kissat_bin).exists():
        return "NOT_AVAILABLE", 0.0
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [kissat_bin, "-n", str(cnf_path)],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        dt_ms = (time.perf_counter() - t0) * 1000.0
        if proc.returncode == 20:
            return "UNSAT", round(dt_ms, 2)
        if proc.returncode == 10:
            return "SAT", round(dt_ms, 2)
        return f"EXIT_{proc.returncode}", round(dt_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)


def run_cryptominisat_wallclock(cnf_path: Path, timeout_s: float) -> tuple[str, float]:
    code = f"""
import pycryptosat
s = pycryptosat.Solver()
with open({str(cnf_path)!r}) as f:
    for line in f:
        if line.startswith('p') or line.startswith('c') or not line.strip():
            continue
        lits = [int(x) for x in line.split() if x != '0']
        if lits:
            s.add_clause(lits)
sat, _ = s.solve()
print('SAT' if sat else 'UNSAT')
"""
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, "-c", code],
            capture_output=True,
            text=True,
            timeout=timeout_s,
            env=os.environ.copy(),
        )
        dt_ms = (time.perf_counter() - t0) * 1000.0
        out = proc.stdout.strip()
        if out in ("UNSAT", "SAT"):
            return out, round(dt_ms, 2)
        if "No module named 'pycryptosat'" in proc.stderr:
            return "NOT_AVAILABLE", 0.0
        return f"ERR:{proc.stderr.strip()[:40]}", round(dt_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)


def cnf_to_opb(cnf_path: Path, opb_path: Path) -> None:
    n_vars, clauses = read_dimacs(cnf_path)
    with opb_path.open("w", encoding="utf-8") as f:
        f.write(f"* #variable= {n_vars} #constraint= {len(clauses)}\n")
        for c in clauses:
            terms = " ".join(f"+1 x{l}" if l > 0 else f"+1 ~x{-l}" for l in c)
            f.write(f"{terms} >= 1 ;\n")


def run_roundingsat_wallclock(roundingsat_bin: str, cnf_path: Path, timeout_s: float) -> tuple[str, float]:
    if not roundingsat_bin or not Path(roundingsat_bin).exists():
        return "NOT_AVAILABLE", 0.0
    opb_path = cnf_path.with_suffix(".opb")
    cnf_to_opb(cnf_path, opb_path)
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [roundingsat_bin, str(opb_path)],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        dt_ms = (time.perf_counter() - t0) * 1000.0
        if "s UNSATISFIABLE" in proc.stdout or proc.returncode == 20:
            return "UNSAT", round(dt_ms, 2)
        if "s SATISFIABLE" in proc.stdout or proc.returncode == 10:
            return "SAT", round(dt_ms, 2)
        return f"EXIT_{proc.returncode}", round(dt_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)
    finally:
        if opb_path.exists():
            opb_path.unlink()


def run_hybrid_subprocess(cnf_path: Path, rmd: int, timeout_s: float) -> tuple[str, str, float]:
    """Run `solve_hybrid_preproc` in an isolated subprocess with hard wall-clock timeout."""
    code = f"""
import json, time
from pathlib import Path
from certified_arith_preproc.cnf_utils import read_dimacs
from certified_arith_preproc.macaulay_cp import solve_hybrid_preproc

n_v, cls = read_dimacs(Path({str(cnf_path)!r}))
t0 = time.perf_counter()
verd, lvl, _ = solve_hybrid_preproc(n_v, cls, max_rm_deg={rmd}, max_mac_deg=3, allow_lift1=False)
ms = round((time.perf_counter() - t0) * 1000.0, 2)
print(json.dumps({{"verdict": verd, "level": lvl, "ms": ms}}))
"""
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, "-c", code],
            capture_output=True,
            text=True,
            timeout=timeout_s,
            env=os.environ.copy(),
        )
        if proc.returncode == 0 and proc.stdout.strip():
            data = json.loads(proc.stdout.strip().splitlines()[-1])
            verd = data["verdict"]
            st = "FEASIBLE" if verd.startswith("FEASIBLE") else "UNSAT"
            return st, verd, float(data["ms"])
        dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
        return f"ERR:{proc.stderr.strip()[:40]}", "ERR", dt_ms
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", "TIMEOUT", round(timeout_s * 1000.0, 2)


def benchmark_instance(
    item: tuple[int, str, tuple[int, list[list[int]]], int],
    cnf_dir: Path,
    timeout_s: float,
    kissat_bin: str,
    roundingsat_bin: str,
    workers: int,
) -> dict[str, object]:
    idx, name, (nv0, cl0), rmd = item
    snv, scl = scramble_cnf(nv0, cl0, seed=5500 + idx)
    cnf_path = cnf_dir / f"{name}.cnf"
    write_dimacs(cnf_path, snv, scl)

    if workers > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            f_ours = pool.submit(run_hybrid_subprocess, cnf_path, rmd, timeout_s)
            f_kis = pool.submit(run_kissat_wallclock, kissat_bin, cnf_path, timeout_s)
            f_cms = pool.submit(run_cryptominisat_wallclock, cnf_path, timeout_s)
            f_rs = (
                pool.submit(run_roundingsat_wallclock, roundingsat_bin, cnf_path, timeout_s)
                if roundingsat_bin and Path(roundingsat_bin).exists()
                else None
            )
            st_ours, verd_ours, ms_ours = f_ours.result()
            st_kis, ms_kis = f_kis.result()
            st_cms, ms_cms = f_cms.result()
            st_rs, ms_rs = f_rs.result() if f_rs is not None else ("NOT_AVAILABLE", 0.0)
    else:
        st_ours, verd_ours, ms_ours = run_hybrid_subprocess(cnf_path, rmd, timeout_s)
        st_kis, ms_kis = run_kissat_wallclock(kissat_bin, cnf_path, timeout_s)
        st_cms, ms_cms = run_cryptominisat_wallclock(cnf_path, timeout_s)
        st_rs, ms_rs = run_roundingsat_wallclock(roundingsat_bin, cnf_path, timeout_s)

    return {
        "instance": name,
        "cnf_path": str(cnf_path),
        "vars": snv,
        "clauses": len(scl),
        "ours_status": st_ours,
        "ours_detail": verd_ours,
        "ours_ms": ms_ours,
        "kissat": st_kis,
        "kissat_ms": ms_kis,
        "cryptominisat": st_cms,
        "cryptominisat_ms": ms_cms,
        "roundingsat": st_rs,
        "roundingsat_ms": ms_rs,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Wall-clock solver comparison on scrambled arithmetic & hybrid 3-CNF benchmarks."
    )
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--cnf-dir", type=Path, default=Path("cnf_samples"))
    parser.add_argument("--json-out", type=Path, default=Path("results/benchmark_results.json"))
    parser.add_argument("--kissat-bin", type=str, default=shutil.which("kissat") or "")
    parser.add_argument("--roundingsat-bin", type=str, default=shutil.which("roundingsat") or "")
    default_workers = 3 if (os.cpu_count() or 1) >= 4 else 1
    parser.add_argument("--workers", type=int, default=default_workers)
    args = parser.parse_args(argv)

    args.cnf_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    suite = [
        (0, "Miter_Mult_12x12_Scrambled", gen_schoolbook_vs_wallace_miter_3cnf(12, True, 112), 2),
        (1, "Miter_Mult_16x16_Scrambled", gen_schoolbook_vs_wallace_miter_3cnf(16, True, 116), 2),
        (2, "Miter_Mult_20x20_Scrambled", gen_schoolbook_vs_wallace_miter_3cnf(20, True, 120), 2),
        (3, "WireElim_OR_s1s2_PHP13_12_Tseitin28", gen_wire_eliminated_php_tseitin(13, 12, 28), 2),
        (4, "Lifted_PHP65_o_Keccak4L_Scrambled", gen_deep_keccak_chi_sponge_php(6, 5, 4), 2),
        (5, "Shifted_Cubic_Sponge_Miter_Scrambled", gen_shifted_cubic_sponge_miter(True), 3),
        (6, "Goldreich_XORMAJ3_n28_m36_Scrambled", gen_goldreich_prg_3cnf(28, 36, "XOR_MAJ3", False, 9128)[:2], 3),
    ]

    print("=" * 116)
    print(
        f"Wall-Clock Benchmark (timeout={int(args.timeout)}s, workers={args.workers}) | "
        f"kissat={args.kissat_bin or 'N/A'} | roundingsat={args.roundingsat_bin or 'N/A'}"
    )
    print("=" * 116)

    results = []
    for item in suite:
        row = benchmark_instance(
            item,
            args.cnf_dir,
            args.timeout,
            args.kissat_bin,
            args.roundingsat_bin,
            args.workers,
        )
        print(
            f"  {row['instance']:36s} (v={row['vars']:5d}, m={row['clauses']:5d}) | "
            f"Ours={row['ours_status']:8s} ({row['ours_ms']:8.1f}ms) | "
            f"Kissat={row['kissat']:12s} ({row['kissat_ms']:8.1f}ms) | "
            f"CMS5={row['cryptominisat']:12s} ({row['cryptominisat_ms']:8.1f}ms) | "
            f"RS={row['roundingsat']}"
        )
        results.append(row)

    args.json_out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
