#!/usr/bin/env python3
"""Run a charge sector in fresh Wolfram kernels, with explicit dependencies."""
import argparse
import itertools
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STAGES = ["singletrace", "singlegraviton", "multitrace", "multigraviton",
          "independentoperator", "exact", "independentexact", "independentgraviton",
          "cohomologyC", "countC", "reducedgrav", "reducedexact"]


def sector_plan(charges, degree):
    # All subcharges are needed: do not quotient these by permutations.
    subcharges = [q for q in itertools.product(*(range(v+1) for v in charges)) if sum(q) >= 2]
    subcharges.sort(key=lambda q: (sum(q), q))
    jobs = []
    for stage in ("singletrace", "singlegraviton"):
        for q in subcharges:
            for d in range(2, min(sum(q), degree)+1):
                jobs.append((stage, q, d))
    for d in (degree-1, degree):
        jobs.extend([("multitrace", charges, d), ("independentoperator", charges, d)])
    for d in (degree, degree+1):
        jobs.extend([("exact", charges, d), ("independentexact", charges, d)])
    jobs.extend([(s, charges, degree) for s in ("multigraviton", "independentgraviton", "cohomologyC")])
    return jobs


def find_kernel(requested):
    if requested:
        return shutil.which(requested) or (requested if Path(requested).is_file() else None)
    for candidate in ("WolframKernel", "math",
                      "/Applications/Wolfram.app/Contents/MacOS/WolframKernel", "wolframscript"):
        path = shutil.which(candidate)
        if path:
            return path
    return None


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--group", choices=["so", "sp"], required=True)
    p.add_argument("--N", type=int, required=True, help="Matrix size: 7 for SO(7), 6 for USp(6)")
    p.add_argument("--charges", type=int, nargs=5, required=True, metavar=("NZ1","NZ2","NT1","NT2","NT3"))
    p.add_argument("--degree", type=int, required=True)
    p.add_argument("--data-root", type=Path, required=True, help="Writable calculation directory; use a fresh directory")
    p.add_argument("--stage", choices=STAGES, help="Run one stage; omitted: generate its dependency pipeline")
    p.add_argument("--numerical", action="store_true", help="Use the author's Float64 Gram/QR method; default is exact RowReduce")
    p.add_argument("--kernel", default=os.environ.get("BPS_WOLFRAM"))
    p.add_argument("--julia", default=os.environ.get("BPS_JULIA", "julia"))
    p.add_argument("--kernels", type=int, default=0, help="Wolfram parallel subkernels; default is serial")
    p.add_argument("--time-limit", type=int, default=3600, help="Seconds per stage, plus 90 seconds for startup/cleanup")
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args()
    if args.N < 2 or (args.group == "sp" and args.N % 2):
        p.error("N must be >= 2 and even for USp")
    if min(args.charges) < 0 or max(args.charges[:2]) > 15 or not 2 <= args.degree <= sum(args.charges):
        p.error("Use nonnegative charges, z charges <= 15, and 2 <= degree <= sum(charges)")
    if args.kernels < 0 or args.time_limit <= 0:
        p.error("Invalid kernel count or time limit")
    q = tuple(args.charges)
    jobs = [(args.stage, q, args.degree)] if args.stage else sector_plan(q, args.degree)
    if args.dry_run:
        print(json.dumps([{"stage":s, "charges":q, "degree":d} for s,q,d in jobs], indent=2))
        return
    kernel = find_kernel(args.kernel)
    if kernel is None:
        p.error("No Wolfram kernel found; use --kernel /path/to/WolframKernel")
    julia = shutil.which(args.julia)
    if args.numerical and julia is None:
        p.error("Julia not found; use --julia /path/to/julia")
    destination = args.data_root.expanduser().resolve()
    # Never write generated calculations into the released, immutable raw dataset.
    if destination == ROOT or ROOT in destination.parents and not ROOT / "scratch" in destination.parents and destination != ROOT / "scratch":
        p.error("Use a calculation directory outside the release, or src/scratch")
    destination.mkdir(parents=True, exist_ok=True)
    logs = destination / "run_logs"
    logs.mkdir(exist_ok=True)
    for index, (stage, charges, degree) in enumerate(jobs, 1):
        cfg = {"stage":stage, "charges":charges, "degree":degree, "group":args.group,
               "N":args.N, "data_root":str(destination), "numerical":args.numerical,
               "kernels":args.kernels, "time_limit":args.time_limit,
               "julia":julia or args.julia, "python":sys.executable}
        label = f"{args.group}-{args.N}-{stage}-{'_'.join(map(str,charges))}-{degree}"
        script_flag = "-file" if Path(kernel).name == "wolframscript" else "-script"
        print(f"[{index}/{len(jobs)}] {label}", flush=True)
        with tempfile.TemporaryDirectory(prefix="bps-job-") as temp:
            config_path = Path(temp)/"job.json"
            config_path.write_text(json.dumps(cfg))
            command = [kernel, script_flag, str(ROOT/"wolfram/run.wls")]
            with (logs/(label+".log")).open("w") as log:
                try:
                    proc = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                            env={**os.environ,"BPS_JOB_CONFIG":str(config_path)},
                                            start_new_session=True)
                    proc.wait(timeout=args.time_limit+90)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid,signal.SIGTERM)
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid,signal.SIGKILL)
                        proc.wait()
                    raise SystemExit(f"Timeout: see {log.name}")
            if proc.returncode:
                raise SystemExit(f"Stage failed ({proc.returncode}): see {logs/(label+'.log')}")
    print(f"Completed. Results and logs: {destination}")


if __name__ == "__main__":
    main()
