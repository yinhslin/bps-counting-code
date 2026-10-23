#!/usr/bin/env bash
# Example only: choose partition, account, CPU and memory limits for your cluster.
# Export BPS_RELEASE, BPS_WORK and BPS_WOLFRAM before submitting this file.
# This script runs a small L=6 example, not a Table I production job.
#SBATCH --job-name=bps-small-example
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --time=00:30:00
set -euo pipefail
: "${BPS_RELEASE:?Set the release directory}"
: "${BPS_WORK:?Set a writable calculation directory}"
: "${BPS_WOLFRAM:?Set the Wolfram kernel executable}"
export JULIA_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
python3 "$BPS_RELEASE/tools/run.py" --group so --N 7 \
  --charges 0 0 1 1 1 --degree 2 --data-root "$BPS_WORK" --numerical
