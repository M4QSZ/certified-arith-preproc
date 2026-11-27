"""Unified v0.5.0 benchmark & VeriPB 3.0.2 verification harness (ATAQUE-01, 02, 04 + SAT controls)."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import time
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description="Run cap-veronese-rs v0.5.0 unified VeriPB 3.0.2 suite.")
    parser.add_argument(
        "--bin",
        type=Path,
        default=Path("/home/miguel/certified-arith-preproc/rust_core/target/release/cap-veronese-rs"),
    )
    parser.add_argument(
        "--veripb-bin",
        type=str,
        default=shutil.which("veripb") or "/home/miguel/.local/bin/veripb",
    )
    parser.add_argument(
        "--pbp-dir",
        type=Path,
        default=Path("/tmp/v05_release_pbp"),
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path("/home/miguel/certified-arith-preproc/results/v05_unified_rust_results.json"),
    )
    args = parser.parse_args()

    bin_p = str(args.bin)
    pbp_dir = args.pbp_dir
    pbp_dir.mkdir(parents=True, exist_ok=True)

    trunc_cnf = pbp_dir / "Trunc_Miter_12x12_low12.cnf"
    subprocess.run(
        [bin_p, "--gen-trunc-miter", "12", "12", "2026", str(trunc_cnf)],
        check=True,
        capture_output=True,
    )

    unsat_suite = [
        ("ATAQUE-01", "Lifted_PHP12_11_OverlappingXOR3", "/home/miguel/.cockpit/spiderweb/cnf_benchmarks/Lifted_PHP12_11_OverlappingXOR3.cnf"),
        ("ATAQUE-01", "Lifted_PHP11_10_Deg2Sponge_MAJ3", "/home/miguel/.cockpit/spiderweb/cnf_benchmarks/Lifted_PHP11_10_Deg2Sponge_MAJ3.cnf"),
        ("ATAQUE-01", "Lifted_PHP65_o_Keccak4L_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Lifted_PHP65_o_Keccak4L_Scrambled.cnf"),
        ("ATAQUE-02", "Goldreich_XORMAJ3_n28_m36_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Goldreich_XORMAJ3_n28_m36_Scrambled.cnf"),
        ("ATAQUE-02", "Interpolant_OR_s1s2_PHP_Goldreich", "/home/miguel/.cockpit/spiderweb/cnf_benchmarks/Interpolant_OR_s1s2_PHP_Goldreich.cnf"),
        ("ATAQUE-04", "Miter_Mult_12x12_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Miter_Mult_12x12_Scrambled.cnf"),
        ("ATAQUE-04", "Miter_Mult_16x16_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Miter_Mult_16x16_Scrambled.cnf"),
        ("ATAQUE-04", "Miter_Mult_20x20_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Miter_Mult_20x20_Scrambled.cnf"),
        ("ATAQUE-04", "Trunc_Miter_12x12_low12", str(trunc_cnf)),
        ("v0.4-Reg", "Shifted_Cubic_Sponge_Miter_Scrambled", "/home/miguel/certified-arith-preproc/cnf_samples/Shifted_Cubic_Sponge_Miter_Scrambled.cnf"),
        ("v0.4-Reg", "WireElim_OR_s1s2_PHP13_12_Tseitin28", "/home/miguel/certified-arith-preproc/cnf_samples/WireElim_OR_s1s2_PHP13_12_Tseitin28.cnf"),
    ]

    unsat_rows = []
    for tag, name, cnf in unsat_suite:
        if not Path(cnf).exists():
            continue
        pbp = pbp_dir / f"{name}.pbp"
        p_emit = subprocess.run([bin_p, "--cnf", cnf, "--pbp", str(pbp)], capture_output=True, text=True, check=True)
        meta = json.loads(p_emit.stdout.strip().splitlines()[-1])
        t1 = time.perf_counter()
        p_chk = subprocess.run([args.veripb_bin, "--cnf", cnf, str(pbp)], capture_output=True, text=True, check=True)
        chk_ms = round((time.perf_counter() - t1) * 1000.0, 2)
        if "VERIFIED UNSATISFIABLE" not in p_chk.stdout:
            raise AssertionError(f"VeriPB failed on {name}:\n{p_chk.stdout}\n{p_chk.stderr}")
        emit_ms = float(meta["emit_ms"])
        lines_cnt = int(meta["pbp_lines"])
        row = {
            "attack_group": tag,
            "instance": name,
            "vars": meta["vars"],
            "clauses": meta["clauses"],
            "ext_vars": meta["ext_vars"],
            "cut_size": meta["cut_size"],
            "max_deg_used": meta["max_deg_used"],
            "pbp_lines": lines_cnt,
            "rust_emit_ms": emit_ms,
            "veripb_check_ms": chk_ms,
            "total_ms": round(emit_ms + chk_ms, 2),
            "veripb_status": "s VERIFIED UNSATISFIABLE",
        }
        unsat_rows.append(row)
        print(f"OK {name:38s} | emit={emit_ms:8.2f}ms | veripb={chk_ms:8.2f}ms | lines={lines_cnt}")

    sat_controls = []
    sat_dir = Path("/home/miguel/certified-arith-preproc/results/v04_bench_cnf")
    if sat_dir.exists():
        for scnf in sorted(sat_dir.glob("SAT_*.cnf")):
            t0 = time.perf_counter()
            pr = subprocess.run(
                [bin_p, "--cnf", str(scnf), "--pbp", str(pbp_dir / f"{scnf.stem}.pbp")],
                capture_output=True,
                text=True,
            )
            dt = round((time.perf_counter() - t0) * 1000.0, 2)
            if pr.returncode != 10:
                raise AssertionError(f"SAT control {scnf} exited with {pr.returncode} instead of 10!")
            sat_controls.append({"instance": scnf.stem, "exit_code": pr.returncode, "rejected_cleanly": True, "ms": dt})
            print(f"SAT_OK {scnf.stem:40s} | exit=10 | {dt:.2f}ms")

    out = {
        "engine": "cap-veronese-rs v0.5.0",
        "veripb_version": "3.0.2",
        "unsat_verified_count": len(unsat_rows),
        "sat_controls_rejected_count": len(sat_controls),
        "false_positives": 0,
        "unsat_benchmarks": unsat_rows,
        "sat_soundness_controls": sat_controls,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(f"Saved {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
