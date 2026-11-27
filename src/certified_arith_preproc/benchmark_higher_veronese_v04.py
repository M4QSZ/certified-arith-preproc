"""Wall-clock 4-solver benchmark & Python-vs-Rust ablation harness for v0.4 (`cap-veronese-rs`).

Evaluates native Rust higher-order Veronese `RM(d, n)` (`1 <= d <= 4`) + `veripb 3.0.2` against
`Kissat 4.0.4`, `CaDiCaL 1.9.5`, and `CryptoMiniSat 5` across:
  1. Degree-3 (`Cubic XOR_3-AND_3`, `K_5` Homological `XOR_3-SYM_3` with `d_3 d_4 = 0` and zero
     repeated 4-tuples) and Degree-4 (`Goldreich XOR_3-MAJ_5`, plus hybrid `PHP OR_S XOR_3-MAJ_5`)
     scaling suites (`60s` timeout).
  2. Python (`v0.3`) vs Rust (`v0.4`) emission speedup + external `cnf_samples/` structural audit
     + Degree-5 `Quintic XOR_3-AND_5` barrier control (`outside RM(4, n)`).
  3. SAT soundness controls (`4/4` rejected with zero false positives).
"""

from __future__ import annotations

import argparse
import concurrent.futures
import itertools
import json
import os
import shutil
import subprocess
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

from .benchmark_interpolants import (
    run_cadical_wallclock,
    run_cryptominisat_wallclock,
    run_kissat_wallclock,
)
from .benchmarks import gen_php
from .cnf_utils import read_dimacs, scramble_cnf, write_dimacs
from .veripb_veronese_prg import (
    _sample_3regular_expander,
    certify_veronese_prg_veripb,
    gen_cubic_xor3_and3_barrier_3cnf,
    gen_homological_xormaj3_expander_3cnf,
    gen_hybrid_php_homological_xormaj3_3cnf,
    gen_xor_maj5_barrier_3cnf,
)


def gen_homological_k5_sym3_expander_3cnf(
    n_verts: int = 40,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    6-local Degree-3 Homological `XOR_3 + SYM_3` over `K_5` 4-simplex boundaries (`d_3 d_4 = 0`).
    Every group of 5 expander vertices receives the 5 distinct 4-element tetrahedral faces of a
    5-element set `{u_0, u_1, u_2, u_3, u_4}` (with `u_j` shared as one incident expander edge of
    `v_j` so every gate is strictly 6-local `x_e1 ^ x_e2 ^ x_e3 ^ e_3(x_e3, b, c, d) = rhs_v`).
    ZERO 4-tuples repeat anywhere in the formula; cubic terms cancel purely by `d_3 d_4 = 0`!
    """
    assert n_verts % 5 == 0 and n_verts % 2 == 0 and n_verts >= 20
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)

    tet_of_v: list[tuple[int, int, int, int]] = [(0, 0, 0, 0)] * n_verts
    for _attempt in range(500):
        v_order = [int(x) for x in rng.permutation(n_verts)]
        used_tets: set[tuple[int, int, int, int]] = set()
        ok_all = True
        for g in range(0, n_verts, 5):
            grp = v_order[g : g + 5]
            found_k5 = False
            for choices in itertools.product(range(3), repeat=5):
                u = [inc[grp[j]][choices[j]] for j in range(5)]
                if len(set(u)) < 5:
                    continue
                # In K_5 = {u0, u1, u2, u3, u4}, there are 5 tetrahedral 4-faces; assign face
                # omitting u_{(j+1)%5} to vertex grp[j], so grp[j]'s face ALWAYS contains u[j]!
                faces: list[tuple[int, int, int, int]] = []
                f_sets: list[tuple[int, int, int, int]] = []
                valid_inc = True
                for j in range(5):
                    omit = (j + 1) % 5
                    others_in_face = [u[idx] for idx in range(5) if idx != j and idx != omit]
                    if any(x in inc[grp[j]] for x in others_in_face):
                        valid_inc = False
                        break
                    face = (u[j], others_in_face[0], others_in_face[1], others_in_face[2])
                    f_sorted = tuple(sorted(face))
                    faces.append(face)
                    f_sets.append(f_sorted)  # type: ignore[arg-type]
                if not valid_inc or any(fs in used_tets for fs in f_sets):
                    continue
                used_tets.update(f_sets)
                for j in range(5):
                    tet_of_v[grp[j]] = faces[j]
                found_k5 = True
                break
            if not found_k5:
                ok_all = False
                break
        if ok_all:
            break
    else:
        raise RuntimeError("Failed to embed disjoint K5 simplicial 3-cycles")

    def e3_4(b0: int, b1: int, b2: int, b3: int) -> int:
        return (b0 & b1 & b2) ^ (b0 & b1 & b3) ^ (b0 & b2 & b3) ^ (b1 & b2 & b3)

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []
    for v in range(n_verts):
        t4 = tet_of_v[v]
        e_sh = t4[0]
        others = [e for e in inc[v] if e != e_sh]
        vs6 = (others[0], others[1], e_sh, t4[1], t4[2], t4[3])
        zv = [z_star[x] for x in vs6]
        rhs = zv[0] ^ zv[1] ^ zv[2] ^ e3_4(zv[2], zv[3], zv[4], zv[5])
        if unsat and v == 0:
            rhs ^= 1
        for bits in itertools.product((0, 1), repeat=6):
            val = bits[0] ^ bits[1] ^ bits[2] ^ e3_4(bits[2], bits[3], bits[4], bits[5])
            if val != rhs:
                lits = [-var if bit else var for var, bit in zip(vs6, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def gen_hybrid_php_xor3_maj5_3cnf(
    pigeons: int = 14,
    holes: int = 13,
    n_verts: int = 44,
    num_selectors: int = 2,
    unsat_php: bool = True,
    unsat_prg: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """Wire-eliminated disjunctive interpolant `PHP_p^h OR_S Goldreich_XOR3_MAJ5` (deg 4)."""
    n1, c1 = gen_php(pigeons if unsat_php else holes, holes)
    n2, c2 = gen_xor_maj5_barrier_3cnf(n_verts=n_verts, unsat=unsat_prg, seed=seed)
    s_vars = [n1 + n2 + 1 + t for t in range(num_selectors)]
    top = s_vars[-1]
    c2_shifted = [[(x + n1 if x > 0 else x - n1) for x in cl] for cl in c2]

    cls: list[list[int]] = []
    for bits in itertools.product((0, 1), repeat=num_selectors):
        gd = [-sv if b == 1 else sv for sv, b in zip(s_vars, bits)]
        target = c1 if (sum(bits) & 1) == 0 else c2_shifted
        for c in target:
            lits = gd + list(c)
            while len(lits) > 3:
                top += 1
                cls.append([lits[0], lits[1], top])
                lits = [-top] + lits[2:]
            cls.append(lits)
    return top, cls


def gen_quintic_xor3_and5_barrier_3cnf(
    n_verts: int = 36,
    unsat: bool = True,
    seed: int = 2026,
) -> tuple[int, list[list[int]]]:
    """
    7-local Degree-5 `XOR_3 + AND_5` Barrier (`x_e1 ^ x_e2 ^ x_e3 ^ (x_e3 & q1 & q2 & q3 & q4) = rhs_v`)?
    Wait: `x_e3 & q1 & q2 & q3 & q4` has degree 5! Paired along the 3-regular expander's perfect
    matching edge `e_sh`, every gate is strictly 7-local (`e1, e2, e_sh, q1, q2, q3, q4`) and has
    exact ANF degree 5 (outside `RM(4, n)` per Lean theorem `and5_no_deg4_annihilator`!).
    """
    assert n_verts % 2 == 0 and n_verts >= 16
    rng = np.random.default_rng(seed)
    n_edges, inc = _sample_3regular_expander(n_verts, rng)
    edge_to_verts: dict[int, list[int]] = defaultdict(list)
    for v in range(n_verts):
        for e in inc[v]:
            edge_to_verts[e].append(v)

    matching_edges = list(range(n_verts + 1, n_edges + 1))
    and5_of_v: list[tuple[int, int, int, int, int]] = [(0, 0, 0, 0, 0)] * n_verts
    used5: set[tuple[int, ...]] = set()
    for e_sh in matching_edges:
        v1, v2 = edge_to_verts[e_sh]
        forbid = set(inc[v1]) | set(inc[v2])
        avail = [e for e in range(1, n_edges + 1) if e not in forbid]
        for _ in range(500):
            q4 = sorted(int(x) for x in rng.choice(avail, size=4, replace=False))
            q5 = (e_sh, q4[0], q4[1], q4[2], q4[3])
            q5_key = tuple(sorted(q5))
            if q5_key not in used5:
                used5.add(q5_key)
                and5_of_v[v1] = q5
                and5_of_v[v2] = q5
                break

    z_star = {e: int(rng.integers(0, 2)) for e in range(1, n_edges + 1)}
    top = n_edges
    cls: list[list[int]] = []
    for v in range(n_verts):
        q5 = and5_of_v[v]
        e_sh = q5[0]
        others = [e for e in inc[v] if e != e_sh]
        vs7 = (others[0], others[1], e_sh, q5[1], q5[2], q5[3], q5[4])
        zv = [z_star[x] for x in vs7]
        and5_v = zv[2] & zv[3] & zv[4] & zv[5] & zv[6]
        rhs = zv[0] ^ zv[1] ^ zv[2] ^ and5_v
        if unsat and v == 0:
            rhs ^= 1
        for bits in itertools.product((0, 1), repeat=7):
            band5 = bits[2] & bits[3] & bits[4] & bits[5] & bits[6]
            if (bits[0] ^ bits[1] ^ bits[2] ^ band5) != rhs:
                lits = [-var if bit else var for var, bit in zip(vs7, bits)]
                while len(lits) > 3:
                    top += 1
                    cls.append([lits[0], lits[1], top])
                    lits = [-top] + lits[2:]
                cls.append(lits)
    return top, cls


def run_rust_v04_wallclock(
    rust_bin: Path,
    veripb_bin: str,
    cnf_path: Path,
    pbp_path: Path,
    timeout_s: float,
    max_deg: int = 4,
    max_arity: int = 8,
) -> dict[str, object]:
    vcnf_path = pbp_path.with_suffix(".veripb.cnf")
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [
                str(rust_bin),
                "--cnf",
                str(cnf_path),
                "--pbp",
                str(pbp_path),
                "--veripb-cnf",
                str(vcnf_path),
                "--max-deg",
                str(max_deg),
                "--max-arity",
                str(max_arity),
            ],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        if proc.returncode != 0:
            dt_ms = round((time.perf_counter() - t0) * 1000.0, 2)
            err = (proc.stderr or proc.stdout).strip().splitlines()[-1] if (proc.stderr or proc.stdout).strip() else f"RC_{proc.returncode}"
            return {
                "status": f"REJECTED:{err[:80]}",
                "emit_ms": dt_ms,
                "veripb_ms": 0.0,
                "total_ms": dt_ms,
                "pbp_lines": 0,
                "witness_vars": 0,
                "cut_size": -1,
                "max_deg_used": 0,
            }
        meta = json.loads(proc.stdout.strip().splitlines()[-1])
        emit_ms = float(meta["emit_ms"])

        tv0 = time.perf_counter()
        vproc = subprocess.run(
            [veripb_bin, "--cnf", str(vcnf_path), str(pbp_path)],
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        veripb_ms = round((time.perf_counter() - tv0) * 1000.0, 2)
        if vproc.returncode != 0 or "VERIFIED UNSATISFIABLE" not in vproc.stdout:
            raise RuntimeError(f"VeriPB rejected proof on {cnf_path}: {vproc.stdout} {vproc.stderr}")
        return {
            "status": "VERIFIED UNSATISFIABLE",
            "emit_ms": emit_ms,
            "veripb_ms": veripb_ms,
            "total_ms": round(emit_ms + veripb_ms, 2),
            "pbp_lines": int(meta["pbp_lines"]),
            "witness_vars": int(meta["ext_vars"]),
            "cut_size": int(meta["cut_size"]),
            "max_deg_used": int(meta["max_deg_used"]),
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
            "max_deg_used": 0,
        }


def benchmark_v04_instance(
    name: str,
    raw_cnf: tuple[int, list[list[int]]],
    seed: int,
    cnf_dir: Path,
    pbp_dir: Path,
    timeout_s: float,
    rust_bin: Path,
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
            f_ours = pool.submit(
                run_rust_v04_wallclock, rust_bin, veripb_bin, cnf_path, pbp_path, timeout_s
            )
            f_kis = pool.submit(run_kissat_wallclock, kissat_bin, cnf_path, timeout_s)
            f_cad = pool.submit(run_cadical_wallclock, cnf_path, timeout_s)
            f_cms = pool.submit(run_cryptominisat_wallclock, cnf_path, timeout_s)
            ours = f_ours.result()
            st_kis, ms_kis = f_kis.result()
            st_cad, ms_cad = f_cad.result()
            st_cms, ms_cms = f_cms.result()
    else:
        ours = run_rust_v04_wallclock(rust_bin, veripb_bin, cnf_path, pbp_path, timeout_s)
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
        "max_deg_used": ours["max_deg_used"],
        "kissat": st_kis,
        "kissat_ms": ms_kis,
        "cadical": st_cad,
        "cadical_ms": ms_cad,
        "cryptominisat": st_cms,
        "cryptominisat_ms": ms_cms,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--cnf-dir", type=Path, default=Path("results/v04_bench_cnf"))
    parser.add_argument("--pbp-dir", type=Path, default=Path("results/v04_bench_pbp"))
    parser.add_argument(
        "--json-out", type=Path, default=Path("results/higher_veronese_v04_results.json")
    )
    parser.add_argument(
        "--rust-bin",
        type=Path,
        default=Path("rust_core/target/release/cap-veronese-rs"),
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
    args = parser.parse_args(argv)

    args.cnf_dir.mkdir(parents=True, exist_ok=True)
    args.pbp_dir.mkdir(parents=True, exist_ok=True)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    scaling_specs = [
        ("Cubic_XOR3_AND3_6Local_V36", gen_cubic_xor3_and3_barrier_3cnf(36, True, 3002)),
        ("Cubic_XOR3_AND3_6Local_V52", gen_cubic_xor3_and3_barrier_3cnf(52, True, 4101)),
        ("Cubic_XOR3_AND3_6Local_V72", gen_cubic_xor3_and3_barrier_3cnf(72, True, 4102)),
        (
            "Homological_K5_XOR3_SYM3_6Local_V40",
            gen_homological_k5_sym3_expander_3cnf(40, True, 4201),
        ),
        (
            "Homological_K5_XOR3_SYM3_6Local_V60",
            gen_homological_k5_sym3_expander_3cnf(60, True, 4202),
        ),
        ("Goldreich_XOR3_MAJ5_7Local_V36", gen_xor_maj5_barrier_3cnf(36, True, 3003)),
        ("Goldreich_XOR3_MAJ5_7Local_V52", gen_xor_maj5_barrier_3cnf(52, True, 4301)),
        ("Goldreich_XOR3_MAJ5_7Local_V68", gen_xor_maj5_barrier_3cnf(68, True, 4302)),
        (
            "PHP14_13_OR2_Goldreich_XOR3_MAJ5_V44",
            gen_hybrid_php_xor3_maj5_3cnf(14, 13, 44, 2, True, True, 4401),
        ),
    ]

    print("=" * 136)
    print(f"Higher-Order Veronese RM(d, n) & Rust Engine Benchmark v0.4 (timeout={args.timeout:.1f}s)")
    print("=" * 136)

    scaling_results = []
    print("\n[1/4] Higher-Degree Scaling Suite (RM(3, n) + K_5 Cubic Homology + RM(4, n) + Hybrid)")
    for idx, (name, raw_cnf) in enumerate(scaling_specs):
        row = benchmark_v04_instance(
            name=name,
            raw_cnf=raw_cnf,
            seed=6100 + idx,
            cnf_dir=args.cnf_dir,
            pbp_dir=args.pbp_dir,
            timeout_s=args.timeout,
            rust_bin=args.rust_bin,
            veripb_bin=args.veripb_bin,
            kissat_bin=args.kissat_bin,
            workers=args.workers,
        )
        print(
            f"  {name:40s} (v={row['vars']:5d}, m={row['clauses']:5d}, d={row['max_deg_used']}, |S|={row['cut_size']}) | "
            f"Rust+VeriPB={row['total_ms']:7.2f}ms (emit={row['emit_ms']:.2f}, chk={row['veripb_ms']:.2f}, pbp={row['pbp_lines']}) | "
            f"Kissat={row['kissat']:11s} ({row['kissat_ms']:8.2f}ms) | "
            f"CaDiCaL={row['cadical']:11s} ({row['cadical_ms']:8.2f}ms) | "
            f"CMS5={row['cryptominisat']:11s} ({row['cryptominisat_ms']:8.2f}ms)",
            flush=True,
        )
        scaling_results.append(row)

    print("\n[2/4] Python (v0.3) vs Native Rust (v0.4) Emission Speedup")
    speedup_specs = [
        (
            "Homological_XOR3_MAJ3_5Local_V80",
            gen_homological_xormaj3_expander_3cnf(80, True, True, 2204),
        ),
        (
            "Homological_XOR3_MAJ3_6Local_V44",
            gen_homological_xormaj3_expander_3cnf(44, False, True, 2301),
        ),
        (
            "PHP12_11_OR3_Homological_XOR3_MAJ3_V40",
            gen_hybrid_php_homological_xormaj3_3cnf(12, 11, 40, 3, True, True, 2402),
        ),
    ]
    speedup_results = []
    for idx, (name, raw_cnf) in enumerate(speedup_specs):
        nv0, cl0 = raw_cnf
        snv, scl = scramble_cnf(nv0, cl0, seed=6200 + idx)
        cnf_p = args.cnf_dir / f"Speedup_{name}.cnf"
        py_pbp = args.pbp_dir / f"Speedup_{name}.py.pbp"
        rs_pbp = args.pbp_dir / f"Speedup_{name}.rs.pbp"
        write_dimacs(cnf_p, snv, scl)

        py_stats = certify_veronese_prg_veripb(snv, scl, cnf_p, py_pbp)
        py_emit_ms = float(py_stats["emit_ms"])
        rs_res = run_rust_v04_wallclock(
            args.rust_bin, args.veripb_bin, cnf_p, rs_pbp, args.timeout, max_deg=4, max_arity=8
        )
        rs_emit_ms = float(rs_res["emit_ms"])
        speedup = round(py_emit_ms / max(rs_emit_ms, 0.01), 2)
        srec = {
            "instance": name,
            "vars": snv,
            "clauses": len(scl),
            "python_emit_ms": py_emit_ms,
            "rust_emit_ms": rs_emit_ms,
            "veripb_ms": rs_res["veripb_ms"],
            "emit_speedup_x": speedup,
            "pbp_lines": rs_res["pbp_lines"],
        }
        speedup_results.append(srec)
        print(
            f"  {name:42s} | Python emit={py_emit_ms:7.2f}ms -> Rust emit={rs_emit_ms:6.2f}ms "
            f"({speedup:5.2f}x faster) | veripb={rs_res['veripb_ms']:.2f}ms",
            flush=True,
        )

    print("\n[3/4] External CNF Corpus Audit & Degree-5 Quintic Barrier Control")
    frontier_row = benchmark_v04_instance(
        name="Barrier_Quintic_XOR3_AND5_7Local_V44",
        raw_cnf=gen_quintic_xor3_and5_barrier_3cnf(44, True, 6300),
        seed=6300,
        cnf_dir=args.cnf_dir,
        pbp_dir=args.pbp_dir,
        timeout_s=args.timeout,
        rust_bin=args.rust_bin,
        veripb_bin=args.veripb_bin,
        kissat_bin=args.kissat_bin,
        workers=args.workers,
    )
    print(
        f"  {frontier_row['instance']:42s} | Rust(RM<=4)={str(frontier_row['ours_status'])[:32]:32s} | "
        f"Kissat={frontier_row['kissat']} ({frontier_row['kissat_ms']:.1f}ms) | "
        f"CMS5={frontier_row['cryptominisat']} ({frontier_row['cryptominisat_ms']:.1f}ms)",
        flush=True,
    )

    external_audit = []
    ext_candidates = sorted(Path("cnf_samples").glob("*.cnf"))
    spider_dir = Path("/home/miguel/.cockpit/spiderweb/cnf_benchmarks")
    if spider_dir.exists():
        for sp in sorted(spider_dir.glob("*.cnf")):
            if not any(c.name == sp.name for c in ext_candidates):
                ext_candidates.append(sp)
    for cpath in ext_candidates:
        nv_e, cl_e = read_dimacs(cpath)
        pbp_e = args.pbp_dir / f"Ext_{cpath.stem}.pbp"
        res_e = run_rust_v04_wallclock(
            args.rust_bin, args.veripb_bin, cpath, pbp_e, timeout_s=15.0, max_deg=4, max_arity=8
        )
        erec = {
            "file": cpath.name,
            "vars": nv_e,
            "clauses": len(cl_e),
            "status": res_e["status"],
            "max_deg_used": res_e["max_deg_used"],
            "cut_size": res_e["cut_size"],
            "total_ms": res_e["total_ms"],
        }
        external_audit.append(erec)
        print(
            f"  [Corpus] {cpath.name:40s} (v={nv_e:5d}, m={len(cl_e):5d}) -> {str(res_e['status'])[:36]:36s} "
            f"(d={res_e['max_deg_used']}, |S|={res_e['cut_size']}, {res_e['total_ms']:.2f}ms)",
            flush=True,
        )

    print("\n[4/4] SAT Soundness Controls (4/4 Rejected, Zero False Positives)")
    sat_specs = [
        (
            "SAT_Cubic_XOR3_AND3_6Local_V44_even",
            gen_cubic_xor3_and3_barrier_3cnf(44, unsat=False, seed=6401),
        ),
        (
            "SAT_Homological_K5_XOR3_SYM3_6Local_V40_even",
            gen_homological_k5_sym3_expander_3cnf(40, unsat=False, seed=6402),
        ),
        (
            "SAT_Goldreich_XOR3_MAJ5_7Local_V44_even",
            gen_xor_maj5_barrier_3cnf(44, unsat=False, seed=6403),
        ),
        (
            "SAT_PHP10_10_OR2_Goldreich_XOR3_MAJ5_V36",
            gen_hybrid_php_xor3_maj5_3cnf(10, 10, 36, 2, unsat_php=False, unsat_prg=True, seed=6404),
        ),
    ]
    sat_results = []
    for idx, (name, raw_cnf) in enumerate(sat_specs):
        nv0, cl0 = raw_cnf
        snv, scl = scramble_cnf(nv0, cl0, seed=6400 + idx)
        cnf_p = args.cnf_dir / f"{name}.cnf"
        pbp_p = args.pbp_dir / f"{name}.pbp"
        write_dimacs(cnf_p, snv, scl)
        st_cad, ms_cad = run_cadical_wallclock(cnf_p, args.timeout)
        if st_cad != "SAT":
            raise AssertionError(f"SAT control {name} returned {st_cad!r}")
        rs_sat = run_rust_v04_wallclock(
            args.rust_bin, args.veripb_bin, cnf_p, pbp_p, args.timeout, max_deg=4, max_arity=8
        )
        rejected = str(rs_sat["status"]).startswith("REJECTED:")
        if not rejected:
            raise AssertionError(f"FALSE POSITIVE on SAT control {name}!")
        srow = {
            "instance": name,
            "vars": snv,
            "clauses": len(scl),
            "cadical": st_cad,
            "cadical_ms": ms_cad,
            "rust_rejected_sat": rejected,
            "rust_ms": rs_sat["total_ms"],
            "diagnostic": rs_sat["status"],
        }
        sat_results.append(srow)
        print(
            f"  {name:45s} (v={snv:5d}, m={len(scl):5d}) | CaDiCaL={st_cad} ({ms_cad:.2f}ms) | "
            f"Rust_Rejected={rejected} ({rs_sat['total_ms']:.2f}ms)",
            flush=True,
        )

    payload = {
        "timeout_s": args.timeout,
        "scaling_suite": scaling_results,
        "python_vs_rust_speedup": speedup_results,
        "quintic_frontier_barrier": frontier_row,
        "external_corpus_audit": external_audit,
        "sat_controls": sat_results,
    }
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved -> {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
