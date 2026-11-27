"""Wall-clock 4-solver benchmark harness for VeriPB 3.0.2 Veronese & Homological PRG certification (v0.3).

Compares `certify_veronese_prg_veripb` + `veripb 3.0.2` against `Kissat 4.0.4`, `CaDiCaL 1.9.5`,
and `CryptoMiniSat 5` across:
  1. Single-expander (`|S| = 0`) 5-local Goldreich `TSA` and 5/6-local Homological `XOR_3 + MAJ_3`
     scaling suites (`K_4` simplicial 2-cycles, zero repeated triplets), plus `|S| in {2, 3}`
     hybrid `PHP OR_S Homological_XOR3_MAJ3` disjunctive interpolants.
  2. Engine ablation (`v0.2` vs `v0.3`) + degree-3/4 barrier controls (`Cubic XOR_3-AND_3` and
     `Goldreich XOR-MAJ_5`, mechanically outside `RM(2, n)`).
  3. SAT soundness controls (`4/4` rejected with zero false positives).
"""

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

from .benchmark_interpolants import (
    run_cadical_wallclock,
    run_cryptominisat_wallclock,
    run_kissat_wallclock,
)
from .cnf_utils import scramble_cnf, write_dimacs
from .veripb_interpolant import certify_disjunctive_interpolant_veripb
from .veripb_veronese_prg import (
    certify_veronese_prg_veripb,
    gen_cubic_xor3_and3_barrier_3cnf,
    gen_goldreich_tsa_expander_3cnf,
    gen_homological_xormaj3_expander_3cnf,
    gen_hybrid_php_homological_xormaj3_3cnf,
    gen_xor_maj5_barrier_3cnf,
)


def run_ours_veronese_wallclock(
    cnf_path: Path,
    pbp_path: Path,
    veripb_bin: str,
    timeout_s: float,
    max_block_arity: int = 7,
) -> dict[str, object]:
    """Run `certify_veronese_prg_veripb` + `veripb --cnf` in an isolated subprocess."""
    if not veripb_bin or not Path(veripb_bin).exists():
        return {
            "status": "NOT_AVAILABLE",
            "emit_ms": 0.0,
            "veripb_ms": 0.0,
            "total_ms": 0.0,
            "pbp_lines": 0,
            "witness_vars": 0,
            "cut_size": -1,
        }

    ours_cnf_path = pbp_path.with_suffix(".veripb.cnf")
    code = f"""
import json, subprocess, time
from pathlib import Path
from certified_arith_preproc.cnf_utils import read_dimacs
from certified_arith_preproc.veripb_veronese_prg import certify_veronese_prg_veripb

src_cnf_p = Path({str(cnf_path)!r})
ours_cnf_p = Path({str(ours_cnf_path)!r})
pbp_p = Path({str(pbp_path)!r})
n_v, cls = read_dimacs(src_cnf_p)

t0 = time.perf_counter()
stats = certify_veronese_prg_veripb(n_v, cls, ours_cnf_p, pbp_p, max_block_arity={max_block_arity})
emit_ms = round((time.perf_counter() - t0) * 1000.0, 2)

t1 = time.perf_counter()
proc = subprocess.run(
    [{veripb_bin!r}, "--cnf", str(ours_cnf_p), str(pbp_p)],
    capture_output=True,
    text=True,
)
veripb_ms = round((time.perf_counter() - t1) * 1000.0, 2)
assert proc.returncode == 0 and "VERIFIED UNSATISFIABLE" in proc.stdout, (
    f"VeriPB failed (rc={{proc.returncode}}): {{proc.stdout}} {{proc.stderr}}"
)
total_ms = round(emit_ms + veripb_ms, 2)
print(json.dumps({{
    "status": "VERIFIED UNSATISFIABLE",
    "emit_ms": emit_ms,
    "veripb_ms": veripb_ms,
    "total_ms": total_ms,
    "pbp_lines": stats["pbp_lines"],
    "witness_vars": stats["n_extension_vars"],
    "cut_size": stats["separator_size"],
}}))
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
            return json.loads(proc.stdout.strip().splitlines()[-1])
        dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
        err_msg = (
            (proc.stderr or proc.stdout).strip().splitlines()[-1]
            if (proc.stderr or proc.stdout).strip()
            else f"RC_{proc.returncode}"
        )
        return {
            "status": f"REJECTED:{err_msg[:72]}",
            "emit_ms": dt_ms,
            "veripb_ms": 0.0,
            "total_ms": dt_ms,
            "pbp_lines": 0,
            "witness_vars": 0,
            "cut_size": -1,
        }
    except subprocess.TimeoutExpired:
        t_ms = round(timeout_s * 1000.0, 2)
        return {
            "status": f"TIMEOUT_{int(timeout_s)}s",
            "emit_ms": t_ms,
            "veripb_ms": 0.0,
            "total_ms": t_ms,
            "pbp_lines": 0,
            "witness_vars": 0,
            "cut_size": -1,
        }


def benchmark_prg_instance(
    name: str,
    raw_cnf: tuple[int, list[list[int]]],
    seed: int,
    cnf_dir: Path,
    pbp_dir: Path,
    timeout_s: float,
    veripb_bin: str,
    kissat_bin: str,
    workers: int,
) -> dict[str, object]:
    nv0, cl0 = raw_cnf
    snv, scl = scramble_cnf(nv0, cl0, seed=seed)
    cnf_path = cnf_dir / f"{name}.cnf"
    pbp_path = pbp_dir / f"{name}.pbp"
    write_dimacs(cnf_path, snv, scl)

    if workers > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            f_ours = pool.submit(run_ours_veronese_wallclock, cnf_path, pbp_path, veripb_bin, timeout_s)
            f_kis = pool.submit(run_kissat_wallclock, kissat_bin, cnf_path, timeout_s)
            f_cad = pool.submit(run_cadical_wallclock, cnf_path, timeout_s)
            f_cms = pool.submit(run_cryptominisat_wallclock, cnf_path, timeout_s)
            ours = f_ours.result()
            st_kis, ms_kis = f_kis.result()
            st_cad, ms_cad = f_cad.result()
            st_cms, ms_cms = f_cms.result()
    else:
        ours = run_ours_veronese_wallclock(cnf_path, pbp_path, veripb_bin, timeout_s)
        st_kis, ms_kis = run_kissat_wallclock(kissat_bin, cnf_path, timeout_s)
        st_cad, ms_cad = run_cadical_wallclock(cnf_path, timeout_s)
        st_cms, ms_cms = run_cryptominisat_wallclock(cnf_path, timeout_s)

    return {
        "instance": name,
        "seed": seed,
        "vars": snv,
        "clauses": len(scl),
        "ours_status": ours["status"],
        "emit_ms": ours["emit_ms"],
        "veripb_ms": ours["veripb_ms"],
        "total_ms": ours["total_ms"],
        "pbp_lines": ours["pbp_lines"],
        "witness_vars": ours["witness_vars"],
        "cut_size": ours["cut_size"],
        "kissat": st_kis,
        "kissat_ms": ms_kis,
        "cadical": st_cad,
        "cadical_ms": ms_cad,
        "cryptominisat": st_cms,
        "cryptominisat_ms": ms_cms,
    }


def run_sat_control_prg(
    name: str,
    raw_cnf: tuple[int, list[list[int]]],
    seed: int,
    cnf_dir: Path,
    pbp_dir: Path,
    timeout_s: float,
) -> dict[str, object]:
    nv0, cl0 = raw_cnf
    snv, scl = scramble_cnf(nv0, cl0, seed=seed)
    cnf_path = cnf_dir / f"{name}.cnf"
    pbp_path = pbp_dir / f"{name}.pbp"
    write_dimacs(cnf_path, snv, scl)

    st_cad, ms_cad = run_cadical_wallclock(cnf_path, timeout_s)
    if st_cad != "SAT":
        raise AssertionError(f"SAT control {name} returned {st_cad!r} instead of SAT!")

    t0 = time.perf_counter()
    rejected = False
    msg = ""
    try:
        certify_veronese_prg_veripb(snv, scl, cnf_path, pbp_path, max_block_arity=7)
    except RuntimeError as exc:
        rejected = True
        msg = str(exc)
    ours_ms = round((time.perf_counter() - t0) * 1000.0, 2)

    if not rejected:
        raise AssertionError(f"FALSE UNSAT PROOF emitted on SAT control {name}!")

    return {
        "instance": name,
        "seed": seed,
        "vars": snv,
        "clauses": len(scl),
        "cadical": st_cad,
        "cadical_ms": ms_cad,
        "ours_rejected_sat": rejected,
        "ours_ms": ours_ms,
        "diagnostic": msg,
    }


def run_barrier_ablation_suite(
    cnf_dir: Path,
    pbp_dir: Path,
    timeout_s: float,
    veripb_bin: str,
    kissat_bin: str,
    workers: int,
) -> list[dict[str, object]]:
    """
    Compare v0.2 (`veripb_interpolant`) vs v0.3 (`veripb_veronese_prg`) on:
      1. `Homological_XOR3_MAJ3_5Local_V44` (v0.2 rejects; v0.3 certifies in <200ms)
      2. `Barrier_Cubic_XOR3_AND3_6Local_V36` (deg=3 antipodal expander; outside RM(2, n))
      3. `Barrier_Goldreich_XOR_MAJ5_7Local_V24` (deg=4 MAJ_5 cycle; zero RM(2) annihilators)
    """
    specs = [
        (
            0,
            "Ablation_v02_vs_v03_Homological_XOR3_MAJ3_V44",
            gen_homological_xormaj3_expander_3cnf(44, True, True, 3001),
        ),
        (
            1,
            "Barrier_Cubic_XOR3_AND3_6Local_V36",
            gen_cubic_xor3_and3_barrier_3cnf(36, True, 3002),
        ),
        (
            2,
            "Barrier_Goldreich_XOR3_MAJ5_7Local_V36",
            gen_xor_maj5_barrier_3cnf(36, True, 3003),
        ),
    ]
    rows: list[dict[str, object]] = []
    for idx, name, raw_cnf in specs:
        row = benchmark_prg_instance(
            name=name,
            raw_cnf=raw_cnf,
            seed=5200 + idx,
            cnf_dir=cnf_dir,
            pbp_dir=pbp_dir,
            timeout_s=timeout_s,
            veripb_bin=veripb_bin,
            kissat_bin=kissat_bin,
            workers=workers,
        )
        # Also test v0.2 directly to record exact v0.2 diagnostic
        cnf_path = cnf_dir / f"{name}.cnf"
        v02_pbp = pbp_dir / f"{name}.v02.pbp"
        nv0, cl0 = raw_cnf
        snv, scl = scramble_cnf(nv0, cl0, seed=5200 + idx)
        t_v02 = time.perf_counter()
        try:
            certify_disjunctive_interpolant_veripb(snv, scl, cnf_path, v02_pbp)
            v02_status = "CERTIFIED"
        except RuntimeError as exc:
            v02_status = f"REJECTED ({exc})"
        row["v02_status"] = v02_status
        row["v02_ms"] = round((time.perf_counter() - t_v02) * 1000.0, 2)
        rows.append(row)
    return rows


def build_scaling_suite() -> list[tuple[int, str, tuple[int, list[list[int]]]]]:
    specs = [
        ("Goldreich_TSA_5Local_V28", lambda: gen_goldreich_tsa_expander_3cnf(28, True, 2101)),
        ("Goldreich_TSA_5Local_V36", lambda: gen_goldreich_tsa_expander_3cnf(36, True, 2102)),
        ("Goldreich_TSA_5Local_V48", lambda: gen_goldreich_tsa_expander_3cnf(48, True, 2103)),
        ("Goldreich_TSA_5Local_V64", lambda: gen_goldreich_tsa_expander_3cnf(64, True, 2104)),
        ("Goldreich_TSA_5Local_V96", lambda: gen_goldreich_tsa_expander_3cnf(96, True, 2105)),
        (
            "Homological_XOR3_MAJ3_5Local_V28",
            lambda: gen_homological_xormaj3_expander_3cnf(28, True, True, 2201),
        ),
        (
            "Homological_XOR3_MAJ3_5Local_V36",
            lambda: gen_homological_xormaj3_expander_3cnf(36, True, True, 2202),
        ),
        (
            "Homological_XOR3_MAJ3_5Local_V52",
            lambda: gen_homological_xormaj3_expander_3cnf(52, True, True, 2203),
        ),
        (
            "Homological_XOR3_MAJ3_5Local_V80",
            lambda: gen_homological_xormaj3_expander_3cnf(80, True, True, 2204),
        ),
        (
            "Homological_XOR3_MAJ3_6Local_V44",
            lambda: gen_homological_xormaj3_expander_3cnf(44, False, True, 2301),
        ),
        (
            "PHP12_11_OR2_Homological_XOR3_MAJ3_V44",
            lambda: gen_hybrid_php_homological_xormaj3_3cnf(12, 11, 44, 2, True, True, 2401),
        ),
        (
            "PHP12_11_OR3_Homological_XOR3_MAJ3_V40",
            lambda: gen_hybrid_php_homological_xormaj3_3cnf(12, 11, 40, 3, True, True, 2402),
        ),
    ]
    return [(idx, name, fn()) for idx, (name, fn) in enumerate(specs)]


def build_sat_controls_suite() -> list[tuple[int, str, tuple[int, list[list[int]]]]]:
    return [
        (
            0,
            "SAT_Goldreich_TSA_5Local_V44_even",
            gen_goldreich_tsa_expander_3cnf(44, unsat=False, seed=2501),
        ),
        (
            1,
            "SAT_Homological_XOR3_MAJ3_5Local_V44_even",
            gen_homological_xormaj3_expander_3cnf(44, True, unsat=False, seed=2502),
        ),
        (
            2,
            "SAT_Homological_XOR3_MAJ3_6Local_V36_even",
            gen_homological_xormaj3_expander_3cnf(36, False, unsat=False, seed=2503),
        ),
        (
            3,
            "SAT_PHP10_10_OR2_Homological_XOR3_MAJ3_V36",
            gen_hybrid_php_homological_xormaj3_3cnf(
                10, 10, 36, 2, unsat_php=False, unsat_prg=True, seed=2504
            ),
        ),
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--cnf-dir", type=Path, default=Path("results/veronese_prg_bench_cnf"))
    parser.add_argument("--pbp-dir", type=Path, default=Path("results/veronese_prg_bench_pbp"))
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path("results/veronese_prg_benchmark_results.json"),
    )
    parser.add_argument(
        "--veripb-bin",
        type=str,
        default=shutil.which("veripb") or "/home/miguel/.local/bin/veripb",
    )
    parser.add_argument(
        "--kissat-bin",
        type=str,
        default=shutil.which("kissat") or "/home/miguel/.local/bin/kissat",
    )
    default_workers = 4 if (os.cpu_count() or 1) >= 4 else 1
    parser.add_argument("--workers", type=int, default=default_workers)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args(argv)

    args.cnf_dir.mkdir(parents=True, exist_ok=True)
    args.pbp_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    scaling_items = build_scaling_suite()
    if args.quick:
        scaling_items = scaling_items[:3]
    sat_items = build_sat_controls_suite()

    print("=" * 132)
    print(
        f"Veronese & Homological PRG Benchmark v0.3 (timeout={args.timeout:.1f}s, workers={args.workers})"
    )
    print("=" * 132)

    scaling_results: list[dict[str, object]] = []
    print("\n[1/3] Scaling Suite (Single-Expander PRGs |S|=0 + Hybrid |S| in {2,3})")
    for idx, name, raw_cnf in scaling_items:
        row = benchmark_prg_instance(
            name=name,
            raw_cnf=raw_cnf,
            seed=5100 + idx,
            cnf_dir=args.cnf_dir,
            pbp_dir=args.pbp_dir,
            timeout_s=args.timeout,
            veripb_bin=args.veripb_bin,
            kissat_bin=args.kissat_bin,
            workers=args.workers,
        )
        print(
            f"  {name:42s} (v={row['vars']:5d}, m={row['clauses']:5d}, |S|={row['cut_size']}) | "
            f"Ours={row['ours_status']:22s} ({row['total_ms']:7.2f}ms: emit={row['emit_ms']:.2f}, chk={row['veripb_ms']:.2f}, pbp={row['pbp_lines']}, w={row['witness_vars']}) | "
            f"Kissat={row['kissat']:11s} ({row['kissat_ms']:8.2f}ms) | "
            f"CaDiCaL={row['cadical']:11s} ({row['cadical_ms']:8.2f}ms) | "
            f"CMS5={row['cryptominisat']:11s} ({row['cryptominisat_ms']:8.2f}ms)",
            flush=True,
        )
        scaling_results.append(row)

    print("\n[2/3] Engine Ablation (v0.2 vs v0.3) & Degree-3/4 Frontier Controls")
    barrier_results = run_barrier_ablation_suite(
        cnf_dir=args.cnf_dir,
        pbp_dir=args.pbp_dir,
        timeout_s=args.timeout,
        veripb_bin=args.veripb_bin,
        kissat_bin=args.kissat_bin,
        workers=args.workers,
    )
    for row in barrier_results:
        print(
            f"  {str(row['instance']):45s} | v0.2={str(row['v02_status'])[:24]:24s} | "
            f"v0.3={str(row['ours_status'])[:28]:28s} ({row['total_ms']:6.2f}ms) | "
            f"Kissat={row['kissat']} ({row['kissat_ms']:.1f}ms) | CMS5={row['cryptominisat']} ({row['cryptominisat_ms']:.1f}ms)",
            flush=True,
        )

    print("\n[3/3] SAT Soundness Controls (4/4 Rejected, Zero False Positives)")
    sat_results: list[dict[str, object]] = []
    for idx, name, raw_cnf in sat_items:
        srow = run_sat_control_prg(
            name=name,
            raw_cnf=raw_cnf,
            seed=5300 + idx,
            cnf_dir=args.cnf_dir,
            pbp_dir=args.pbp_dir,
            timeout_s=args.timeout,
        )
        print(
            f"  {name:45s} (v={srow['vars']:5d}, m={srow['clauses']:5d}) | "
            f"CaDiCaL={srow['cadical']} ({srow['cadical_ms']:6.2f}ms) | "
            f"Ours_Rejected={srow['ours_rejected_sat']} ({srow['ours_ms']:6.2f}ms)",
            flush=True,
        )
        sat_results.append(srow)

    payload = {
        "timeout_s": args.timeout,
        "scaling_suite": scaling_results,
        "ablation_and_barriers": barrier_results,
        "sat_controls": sat_results,
    }
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
