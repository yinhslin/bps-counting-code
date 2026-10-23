# Computational companion: Violation of S-duality in classical Q-cohomology

Code and selected computational records for Chi-Ming Chang and Ying-Hsuan Lin,
[arXiv:2510.24008](https://arxiv.org/abs/2510.24008).
Version 1.0.0, prepared on 23 October 2026.
The [code](https://github.com/yinhslin/bps-counting-code/tree/2510.24008-v1.0.0/papers/2510.24008)
and [data](https://github.com/yinhslin/bps-counting/tree/2510.24008-v1.0.0/2510.24008)
continue the existing shared repositories. The paper release tag in both is
`2510.24008-v1.0.0`. A combined archive is provided with the
[code release](https://github.com/yinhslin/bps-counting-code/releases/tag/2510.24008-v1.0.0).

The Wolfram Language code constructs finite-rank trace operators, acts with Q,
and counts their cohomology and monotone subspace. Julia supplies the original
floating-point Gram/QR row-selection method when requested. The readable data
include the scan through L=18, the four Table I job logs, and the stored Cartan
image bases of the bosonic sector.

## Start with the results

Download and extract `bps_cohomology_code_data.zip` from the code release, then
open a terminal in its `bps-cohomology/` directory. Only Python 3.10 or later is
needed to check the included results:

```sh
python3 tools/verify_release.py
python3 tools/validate_results.py
```

The first command checks the complete release manifest. The second verifies
every included raw file against its SHA-256, checks all
938 symmetry-reduced sectors per group, compares the Table I counts with four
archived cluster logs, and computes the rank of each small Cartan image matrix
with exact rational arithmetic. It does **not** reconstruct the full large Q
complex or independently redo the original numerical rank calculations.

If using the repositories separately, run from `papers/2510.24008/` in the code
repository and specify the data directory:

```sh
export BPS_DATA_ROOT=/path/to/bps-counting/2510.24008/data
python3 tools/validate_results.py --data-root "$BPS_DATA_ROOT"
```

The Python tests and optional Wolfram Cartan-export tool also honor
`BPS_DATA_ROOT`. Leave it unset when using the combined archive's bundled data.

- [Table I, with source log for each column](https://github.com/yinhslin/bps-counting/blob/2510.24008-v1.0.0/2510.24008/data/derived/table_I.csv)
- [Complete cohomology scan, with headers](https://github.com/yinhslin/bps-counting/blob/2510.24008-v1.0.0/2510.24008/data/derived/cohomology_scan.csv)
- [Machine-readable verification record](https://github.com/yinhslin/bps-counting/blob/2510.24008-v1.0.0/2510.24008/data/derived/validation.json)
- [Data formats and the one missing per-sector filename](docs/DATA.md)

## Run a small calculation

Install a licensed 64-bit Wolfram kernel with the bundled Combinatorica package.
Set `BPS_WOLFRAM` to the kernel executable, or pass `--kernel /path/to/WolframKernel`.
On Linux the executable may be named `math`; `wolframscript` is also supported.
The local tests used Wolfram 14.2.1 and Julia 1.10.5; the original cluster
environment is described in [ENVIRONMENT.md](docs/ENVIRONMENT.md).

From this directory:

```sh
python3 tools/run.py --group so --N 7 --charges 0 0 0 0 2 --degree 2 \
  --data-root ../calculation-work/so-example
python3 tools/run.py --group sp --N 6 --charges 0 0 0 0 2 --degree 2 \
  --data-root ../calculation-work/sp-example
```

Both runs should give cohomology dimension 1 and monotone dimension 1 at L=4.
The runner constructs the required subcharges and dependencies in fresh kernels.
It uses exact `RowReduce` by default. Existing results are reused; change the
working directory to rerun a calculation with different arithmetic or software.

For the original numerical route, install the pinned Julia environment once:

```sh
julia --project=julia -e 'using Pkg; Pkg.instantiate()'
python3 tools/run.py --group so --N 7 --charges 0 0 1 1 1 --degree 2 \
  --data-root ../calculation-work/numerical-so --numerical
```

`--N` means the matrix dimension (7 or 6), not the rank of the Lie algebra.
`--charges` means `(nz1,nz2,nt1,nt2,nt3)`; `--degree` is the number of letters.
Use `--dry-run` to inspect the required stages, or `--stage` to run one stage
after its inputs have been generated. See [PIPELINE.md](docs/PIPELINE.md).

## Files

| Directory | Contents |
|---|---|
| `wolfram/` | Twelve computational modules, a runner, and portable numerical transport |
| `julia/` | Gram/QR helpers and a pinned project/manifest |
| `tools/` | Sector runner, data verification, Cartan export, streaming matrix split |
| `data/raw/` | Byte-preserved small author outputs and four final cluster logs |
| `data/derived/` | Readable CSVs, exact matrix entries, monomials and validation |
| `docs/` | Conventions, environment, numerical method, provenance and limits |
| `tests/` | Data/transport tests and small Julia matrix checks |
| `examples/` | Expected small-sector results and a Slurm template |

The `data/` directory is included in the combined archive and in the data
repository's `2510.24008/` directory. The code repository contains the remaining
directories in the table.

The external source tree contains about 3.13 TB, including large bases,
intermediates, backups and partial outputs. It is **not** included in this compact
package. [The inventory](https://github.com/yinhslin/bps-counting/blob/2510.24008-v1.0.0/2510.24008/data/external_inventory.csv.gz) lists its 50,027 files
and sizes; it is a metadata inventory, not a checksum verification of that tree.
The selected raw files in this package do have complete SHA-256 coverage.

## Validation and limits

```sh
python3 -m unittest discover -s tests -v
julia --project=julia tests/test_numerics.jl
```

See [VALIDATION.md](docs/VALIDATION.md) for the tests actually completed during
release preparation. Large L=18 jobs have not been rerun. The matrix entries
exported from the saved Cartan bases can be checked exactly, but this alone does
not independently establish the rank or completeness of the original Q complex.
Read [NUMERICS.md](docs/NUMERICS.md) before interpreting floating-point ranks.

The code is under the [MIT License](LICENSE), as selected by the author.
Please cite the associated paper; [CITATION.cff](CITATION.cff) contains its citation.
The license does not cover the Wolfram or Julia dependencies, or the manuscript.
