# Computational stages

The release exposes the SO and USp full 1/16-BPS sector. The older SU/U and
Schur/su121/su122 command-line variants are not part of this supported interface.
Use a fresh output root when changing the method, group parameters or code.

1. `singletrace` and `singlegraviton` generate traces for the needed subcharges.
2. `multitrace` forms products of traces at the target charges and degree.
3. `independentoperator` chooses an independent coefficient-space basis.
4. `exact` acts with Q on the monomials of the operator basis at degree n-1.
5. `independentexact` forms and reduces the corresponding Q-image at degree n.
6. `multigraviton` and `independentgraviton` form the span of monotone
   representatives together with exact vectors.
7. `cohomologyC` compares the operator space at n, exact space at n, exact
   space at n+1, and the monotone-plus-exact space at n.
8. Optional `reducedgrav` or `reducedexact` applies the Cartan restriction.

The `tools/run.py` default pipeline supplies all subcharges componentwise,
including nonsorted subcharges. Sorting these would silently remove needed
trace factors. The symmetry reduction is used to summarize the final scan,
not to omit intermediate subcharge files.

The original split multi-trace jobs (`multitraceX/Y/Z`) and their site-specific
schedulers remain in the author's original-source archive. This release uses
the direct `multitrace` construction as its reference pipeline; it has not
benchmarked this path at L=18. The algebraic modules are preserved with the
changes listed in [PROVENANCE.md](PROVENANCE.md).

## Inspect a Table I plan

From the release root:

```sh
python3 tools/run.py --group so --N 7 --charges 0 0 3 3 3 --degree 8 \
  --data-root ../calculation-work/table-I-so --numerical --dry-run
```

Replace the charges with `1 1 2 2 2` for the bosonic sector, and use `--group sp
--N 6` for USp(6). Remove `--dry-run` only when adequate resources are available.
These are large calculations: individual saved bases in the supplied archive
reach tens of GB. The historical jobs used 64 CPUs on `amd_256`/`amd_512`
partitions. Those partition names do not specify a portable resource request.
No peak-memory benchmark is asserted for the reorganized pipeline.

For an existing complete working tree, run one stage with `--stage
cohomologyC`, `--stage reducedgrav`, etc. Direct dependencies must exist;
missing files cause a failure rather than a zero-dimensional count. Boundary
degrees below two or above the total charge are explicitly generated as empty
spaces by the dependency pipeline.

The runner writes a log for each stage under `run_logs/` and a version/timing
record next to each new result. It does not overwrite existing stage results.
The default is serial Wolfram execution. `--kernels K` requests K licensed
subkernels using the original parallel Table/Do machinery; this parallel mode
has not been retested in the release preparation.

## Stored files

Names are `L_nz1_nz2_nt1_nt2_nt3_n_NN.mx` or `.csv` under
`<data-root>/bps_so/all/` or `bps_sp/all/`. MX files contain symbol definitions
written by `DumpSave`. The saved independent spaces have the form
`{coefficient_matrix, ordered_monomials}`; their row count is the dimension
selected by the corresponding reduction. The Cartan-image MX files supplied
here loaded successfully across Linux-origin data and the local 64-bit Mac
kernel; the portable CSV exports remove the need to rely on MX for data review.

`--time-limit` bounds each stage. A failure preserves intermediate scratch
files for diagnosis. Review the relevant log before reusing a partially
populated work directory.
