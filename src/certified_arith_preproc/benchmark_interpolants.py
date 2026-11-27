"""Wall-clock benchmark harness for VeriPB 3.0.2 disjunctive interpolant certification vs CDCL solvers."""

from __future__ import annotations

import argparse
import concurrent.futures
import itertools
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

from .benchmarks import gen_php, gen_wire_eliminated_php_tseitin
from .cnf_utils import scramble_cnf, write_dimacs
from .veripb_interpolant import (
    certify_disjunctive_interpolant_veripb,
    gen_multiguard_php_tseitin_3cnf,
)


def gen_standalone_tseitin_3reg(
    tseitin_verts: int = 44,
    odd_charge: bool = True,
    seed: int = 77,
) -> tuple[int, list[list[int]]]:
    """Generate a standalone random 3-regular expander Tseitin 3-CNF (no selector guards)."""
    assert tseitin_verts % 2 == 0 and tseitin_verts >= 6
    rng = np.random.default_rng(seed)
    inc: list[list[int]] = [[] for _ in range(tseitin_verts)]
    edges: list[tuple[int, int]] = []

    perm_cycle = list(rng.permutation(tseitin_verts))
    adj_set: set[tuple[int, int]] = set()
    for idx in range(tseitin_verts):
        u, v = int(perm_cycle[idx]), int(perm_cycle[(idx + 1) % tseitin_verts])
        a, b = (u, v) if u < v else (v, u)
        adj_set.add((a, b))
        eid = len(edges) + 1
        edges.append((a, b))
        inc[a].append(eid)
        inc[b].append(eid)

    for _attempt in range(500):
        order = list(rng.permutation(tseitin_verts))
        pairs: list[tuple[int, int]] = []
        ok = True
        for idx in range(0, tseitin_verts, 2):
            u, v = int(order[idx]), int(order[idx + 1])
            a, b = (u, v) if u < v else (v, u)
            if (a, b) in adj_set:
                ok = False
                break
            pairs.append((a, b))
        if ok:
            for a, b in pairs:
                eid = len(edges) + 1
                edges.append((a, b))
                inc[a].append(eid)
                inc[b].append(eid)
            break
    else:
        raise RuntimeError("Failed to sample simple 3-regular matching")

    cls: list[list[int]] = []
    for v_idx in range(tseitin_verts):
        e1, e2, e3 = inc[v_idx]
        ch = 1 if (v_idx == 0 and odd_charge) else 0
        for b1, b2, b3 in itertools.product((0, 1), repeat=3):
            if (b1 ^ b2 ^ b3) != ch:
                cls.append([-e1 if b1 else e1, -e2 if b2 else e2, -e3 if b3 else e3])

    return len(edges), cls


def _gen_or_php_tseitin_custom(
    pigeons: int,
    holes: int,
    tseitin_verts: int,
    num_selectors: int = 2,
    random_3reg: bool = False,
    odd_charge: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """Generate OR_{s_1 ^ ... ^ s_k}(PHP_{p}^{h}, Tseitin_{V, charge}) with independent branch control."""
    n1, c1 = gen_php(pigeons, holes)
    if random_3reg:
        n2, c2 = gen_standalone_tseitin_3reg(tseitin_verts, odd_charge=odd_charge, seed=seed)
    else:
        assert tseitin_verts % 2 == 0 and tseitin_verts >= 6
        edges: list[tuple[int, int]] = []
        inc: list[list[int]] = [[] for _ in range(tseitin_verts)]
        for i in range(tseitin_verts):
            u, v = i, (i + 1) % tseitin_verts
            eid = len(edges) + 1
            edges.append((u, v))
            inc[u].append(eid)
            inc[v].append(eid)
        for i in range(tseitin_verts // 2):
            u, v = i, i + tseitin_verts // 2
            eid = len(edges) + 1
            edges.append((u, v))
            inc[u].append(eid)
            inc[v].append(eid)
        c2 = []
        for v_idx in range(tseitin_verts):
            e1, e2, e3 = inc[v_idx]
            ch = 1 if (v_idx == 0 and odd_charge) else 0
            for b1, b2, b3 in itertools.product((0, 1), repeat=3):
                if (b1 ^ b2 ^ b3) != ch:
                    c2.append([-e1 if b1 else e1, -e2 if b2 else e2, -e3 if b3 else e3])
        n2 = len(edges)

    s_vars = [n1 + n2 + 1 + t for t in range(num_selectors)]
    top = s_vars[-1]
    c2_shifted = [[(x + n1 if x > 0 else x - n1) for x in cl] for cl in c2]

    cls: list[list[int]] = []
    for bits in itertools.product((0, 1), repeat=num_selectors):
        gd = [-sv if b == 1 else sv for sv, b in zip(s_vars, bits)]
        parity = sum(bits) & 1
        target = c1 if parity == 0 else c2_shifted
        for c in target:
            lits = gd + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls


def run_ours_veripb_wallclock(
    cnf_path: Path,
    pbp_path: Path,
    veripb_bin: str,
    timeout_s: float,
) -> dict[str, object]:
    """Run `certify_disjunctive_interpolant_veripb` + `veripb --cnf` in an isolated subprocess."""
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
from certified_arith_preproc.veripb_interpolant import certify_disjunctive_interpolant_veripb

src_cnf_p = Path({str(cnf_path)!r})
ours_cnf_p = Path({str(ours_cnf_path)!r})
pbp_p = Path({str(pbp_path)!r})
n_v, cls = read_dimacs(src_cnf_p)

t0 = time.perf_counter()
stats = certify_disjunctive_interpolant_veripb(n_v, cls, ours_cnf_p, pbp_p)
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
    "witness_vars": stats["witness_vars"],
    "cut_size": stats["cut_size"],
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
        err_msg = (proc.stderr or proc.stdout).strip().splitlines()[-1] if (proc.stderr or proc.stdout).strip() else f"RC_{proc.returncode}"
        return {
            "status": f"ERR:{err_msg[:80]}",
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


def run_cadical_wallclock(cnf_path: Path, timeout_s: float) -> tuple[str, float]:
    """Run CaDiCaL 1.9.5 (`pysat.solvers.Cadical195`) in an isolated subprocess."""
    code = f"""
from pysat.solvers import Cadical195
clauses = []
with open({str(cnf_path)!r}, encoding="utf-8") as f:
    for line in f:
        if line.startswith("p") or line.startswith("c") or not line.strip():
            continue
        lits = [int(x) for x in line.split() if x != "0"]
        if lits:
            clauses.append(lits)
with Cadical195(bootstrap_with=clauses) as solver:
    sat = solver.solve()
print("SAT" if sat else "UNSAT")
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
        if "No module named 'pysat'" in proc.stderr:
            return "NOT_AVAILABLE", 0.0
        return f"ERR:{proc.stderr.strip()[:60]}", round(dt_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)


def run_cryptominisat_wallclock(cnf_path: Path, timeout_s: float) -> tuple[str, float]:
    """Run CryptoMiniSat 5 (`pycryptosat.Solver`) in an isolated subprocess."""
    code = f"""
import pycryptosat
s = pycryptosat.Solver()
with open({str(cnf_path)!r}, encoding="utf-8") as f:
    for line in f:
        if line.startswith("p") or line.startswith("c") or not line.strip():
            continue
        lits = [int(x) for x in line.split() if x != "0"]
        if lits:
            s.add_clause(lits)
sat, _ = s.solve()
print("SAT" if sat else "UNSAT")
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
        return f"ERR:{proc.stderr.strip()[:60]}", round(dt_ms, 2)
    except subprocess.TimeoutExpired:
        return f"TIMEOUT_{int(timeout_s)}s", round(timeout_s * 1000.0, 2)


def benchmark_unsat_instance(
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
            f_ours = pool.submit(run_ours_veripb_wallclock, cnf_path, pbp_path, veripb_bin, timeout_s)
            f_kis = pool.submit(run_kissat_wallclock, kissat_bin, cnf_path, timeout_s)
            f_cad = pool.submit(run_cadical_wallclock, cnf_path, timeout_s)
            f_cms = pool.submit(run_cryptominisat_wallclock, cnf_path, timeout_s)
            ours = f_ours.result()
            st_kis, ms_kis = f_kis.result()
            st_cad, ms_cad = f_cad.result()
            st_cms, ms_cms = f_cms.result()
    else:
        ours = run_ours_veripb_wallclock(cnf_path, pbp_path, veripb_bin, timeout_s)
        st_kis, ms_kis = run_kissat_wallclock(kissat_bin, cnf_path, timeout_s)
        st_cad, ms_cad = run_cadical_wallclock(cnf_path, timeout_s)
        st_cms, ms_cms = run_cryptominisat_wallclock(cnf_path, timeout_s)

    return {
        "instance": name,
        "seed": seed,
        "cnf_path": str(cnf_path),
        "pbp_path": str(pbp_path),
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


def run_sat_control_instance(
    name: str,
    raw_cnf: tuple[int, list[list[int]]],
    seed: int,
    cnf_dir: Path,
    pbp_dir: Path,
    timeout_s: float,
) -> dict[str, object]:
    """Verify SAT control: CaDiCaL 1.9.5 returns SAT and our certifier raises RuntimeError."""
    nv0, cl0 = raw_cnf
    snv, scl = scramble_cnf(nv0, cl0, seed=seed)
    cnf_path = cnf_dir / f"{name}.cnf"
    pbp_path = pbp_dir / f"{name}.pbp"
    write_dimacs(cnf_path, snv, scl)

    st_cad, ms_cad = run_cadical_wallclock(cnf_path, timeout_s)
    if st_cad != "SAT":
        raise AssertionError(f"SAT control {name} did not return SAT under CaDiCaL195 (got {st_cad!r})")

    t0 = time.perf_counter()
    rejected = False
    error_msg = ""
    try:
        certify_disjunctive_interpolant_veripb(snv, scl, cnf_path, pbp_path)
    except RuntimeError as exc:
        rejected = True
        error_msg = str(exc)
    ours_ms = round((time.perf_counter() - t0) * 1000.0, 2)

    if not rejected:
        raise AssertionError(f"FALSE UNSAT PROOF on SAT control {name}!")

    return {
        "instance": name,
        "seed": seed,
        "cnf_path": str(cnf_path),
        "vars": snv,
        "clauses": len(scl),
        "cadical": st_cad,
        "cadical_ms": ms_cad,
        "ours_rejected_sat": rejected,
        "ours_ms": ours_ms,
        "ours_message": error_msg,
    }


def build_scaling_suite() -> list[tuple[int, str, tuple[int, list[list[int]]]]]:
    specs = [
        ("PHP07_06_OR2_Tseitin14", lambda: gen_wire_eliminated_php_tseitin(7, 6, 14)),
        ("PHP08_07_OR2_Tseitin16", lambda: gen_wire_eliminated_php_tseitin(8, 7, 16)),
        ("PHP10_09_OR2_Tseitin20", lambda: gen_wire_eliminated_php_tseitin(10, 9, 20)),
        ("PHP11_10_OR2_Tseitin22", lambda: gen_wire_eliminated_php_tseitin(11, 10, 22)),
        ("PHP12_11_OR2_Tseitin24", lambda: gen_wire_eliminated_php_tseitin(12, 11, 24)),
        ("PHP13_12_OR2_Tseitin28", lambda: gen_wire_eliminated_php_tseitin(13, 12, 28)),
        ("PHP16_15_OR2_Tseitin36", lambda: gen_wire_eliminated_php_tseitin(16, 15, 36)),
        ("PHP20_19_OR2_Tseitin44", lambda: gen_wire_eliminated_php_tseitin(20, 19, 44)),
        ("PHP24_23_OR2_Tseitin52", lambda: gen_wire_eliminated_php_tseitin(24, 23, 52)),
        ("PHP12_11_OR3_Expander30", lambda: gen_multiguard_php_tseitin_3cnf(12, 11, 30, 3, True, True, 41)),
        ("PHP14_13_OR3_Expander36", lambda: gen_multiguard_php_tseitin_3cnf(14, 13, 36, 3, True, True, 42)),
    ]
    return [(idx, name, fn()) for idx, (name, fn) in enumerate(specs)]


def build_ablation_suite() -> list[tuple[int, str, tuple[int, list[list[int]]]]]:
    return [
        (0, "Standalone_PHP14_13_Scrambled", gen_php(14, 13)),
        (1, "Standalone_Tseitin140_Expander_Scrambled", gen_standalone_tseitin_3reg(140, odd_charge=True, seed=77)),
    ]


def build_sat_controls_suite() -> list[tuple[int, str, tuple[int, list[list[int]]]]]:
    return [
        (
            0,
            "SAT_PHP08_08_OR2_Tseitin16_odd",
            _gen_or_php_tseitin_custom(8, 8, 16, num_selectors=2, random_3reg=False, odd_charge=True, seed=51),
        ),
        (
            1,
            "SAT_PHP08_07_OR2_Tseitin16_even",
            _gen_or_php_tseitin_custom(8, 7, 16, num_selectors=2, random_3reg=False, odd_charge=False, seed=52),
        ),
        (
            2,
            "SAT_PHP10_10_OR3_Expander24_odd",
            _gen_or_php_tseitin_custom(10, 10, 24, num_selectors=3, random_3reg=True, odd_charge=True, seed=53),
        ),
        (
            3,
            "SAT_Standalone_Tseitin24_even",
            gen_standalone_tseitin_3reg(24, odd_charge=False, seed=54),
        ),
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Wall-clock benchmark for VeriPB 3.0.2 disjunctive interpolants vs Kissat, CaDiCaL, and CryptoMiniSat 5."
    )
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--cnf-dir", type=Path, default=Path("results/interpolant_bench_cnf"))
    parser.add_argument("--pbp-dir", type=Path, default=Path("results/interpolant_bench_pbp"))
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path("results/interpolant_benchmark_results.json"),
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
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Run a fast smoke-test subset (first 2 scaling instances, both ablations, all 4 SAT controls).",
    )
    parser.add_argument(
        "--suite-filter",
        type=str,
        default="",
        help="Optional substring filter on instance names across scaling/ablation/sat_controls.",
    )
    args = parser.parse_args(argv)

    args.cnf_dir.mkdir(parents=True, exist_ok=True)
    args.pbp_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    scaling_items = build_scaling_suite()
    ablation_items = build_ablation_suite()
    sat_items = build_sat_controls_suite()

    if args.quick:
        scaling_items = scaling_items[:2]

    if args.suite_filter:
        needle = args.suite_filter.lower()
        scaling_items = [it for it in scaling_items if needle in it[1].lower()]
        ablation_items = [it for it in ablation_items if needle in it[1].lower()]
        sat_items = [it for it in sat_items if needle in it[1].lower()]

    print("=" * 132)
    print(
        f"Interpolant Wall-Clock Benchmark (timeout={args.timeout:.1f}s, workers={args.workers}) | "
        f"veripb={args.veripb_bin or 'N/A'} | kissat={args.kissat_bin or 'N/A'}"
    )
    print("=" * 132)

    scaling_results: list[dict[str, object]] = []
    if scaling_items:
        print("\n[1/3] Scaling Suite (Disjunctive Interpolants)")
        for idx, name, raw_cnf in scaling_items:
            row = benchmark_unsat_instance(
                name=name,
                raw_cnf=raw_cnf,
                seed=4100 + idx,
                cnf_dir=args.cnf_dir,
                pbp_dir=args.pbp_dir,
                timeout_s=args.timeout,
                veripb_bin=args.veripb_bin,
                kissat_bin=args.kissat_bin,
                workers=args.workers,
            )
            print(
                f"  {name:34s} (v={row['vars']:5d}, m={row['clauses']:5d}, |S|={row['cut_size']}) | "
                f"Ours={row['ours_status']:22s} ({row['total_ms']:7.1f}ms: emit={row['emit_ms']:.1f}, chk={row['veripb_ms']:.1f}, pbp={row['pbp_lines']}, w={row['witness_vars']}) | "
                f"Kissat={row['kissat']:10s} ({row['kissat_ms']:7.1f}ms) | "
                f"CaDiCaL={row['cadical']:10s} ({row['cadical_ms']:7.1f}ms) | "
                f"CMS5={row['cryptominisat']:10s} ({row['cryptominisat_ms']:7.1f}ms)"
            )
            scaling_results.append(row)

    ablation_results: list[dict[str, object]] = []
    if ablation_items:
        print("\n[2/3] Ablation Standalone (|S|=0 Pure Components)")
        for idx, name, raw_cnf in ablation_items:
            row = benchmark_unsat_instance(
                name=name,
                raw_cnf=raw_cnf,
                seed=4200 + idx,
                cnf_dir=args.cnf_dir,
                pbp_dir=args.pbp_dir,
                timeout_s=args.timeout,
                veripb_bin=args.veripb_bin,
                kissat_bin=args.kissat_bin,
                workers=args.workers,
            )
            print(
                f"  {name:40s} (v={row['vars']:5d}, m={row['clauses']:5d}, |S|={row['cut_size']}) | "
                f"Ours={row['ours_status']:22s} ({row['total_ms']:7.1f}ms: emit={row['emit_ms']:.1f}, chk={row['veripb_ms']:.1f}, pbp={row['pbp_lines']}, w={row['witness_vars']}) | "
                f"Kissat={row['kissat']:10s} ({row['kissat_ms']:7.1f}ms) | "
                f"CaDiCaL={row['cadical']:10s} ({row['cadical_ms']:7.1f}ms) | "
                f"CMS5={row['cryptominisat']:10s} ({row['cryptominisat_ms']:7.1f}ms)"
            )
            ablation_results.append(row)

    sat_results: list[dict[str, object]] = []
    if sat_items:
        print("\n[3/3] SAT Controls (Zero False UNSAT Verification)")
        for idx, name, raw_cnf in sat_items:
            row = run_sat_control_instance(
                name=name,
                raw_cnf=raw_cnf,
                seed=4300 + idx,
                cnf_dir=args.cnf_dir,
                pbp_dir=args.pbp_dir,
                timeout_s=args.timeout,
            )
            print(
                f"  {name:34s} (v={row['vars']:5d}, m={row['clauses']:5d}) | "
                f"CaDiCaL={row['cadical']} ({row['cadical_ms']:6.1f}ms) | "
                f"Ours_Rejected={row['ours_rejected_sat']} ({row['ours_ms']:6.1f}ms)"
            )
            sat_results.append(row)

    payload = {
        "timeout_s": args.timeout,
        "scaling_suite": scaling_results,
        "ablation_standalone": ablation_results,
        "sat_controls": sat_results,
    }
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
