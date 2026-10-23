# Environment record

Checked on 23 October 2026.

| Component | Evidence |
|---|---|
| Original job Julia | Job scripts prepend a `julia-1.10.4/bin` installation |
| Cluster Julia observed | 1.10.4 in the cluster's Julia conda environment |
| Cluster MAT | 0.10.7 in the user's `v1.10` project |
| Cluster MatrixMarket | 0.5.2 in the user's `v1.10` project |
| Cluster other direct packages | DoubleFloats 1.4.3, MultiFloats 2.3.0, JLD2 0.5.15, RowEchelon 0.2.1, ZChop 0.3.11, DelimitedFiles 1.9.1 |
| Cluster Wolfram installation | `math` resolves to a Mathematica 13.2 installation |
| Cluster Wolfram execution | A current login-node probe returned `No valid password found`; no successful live `$Version` query was obtained |
| Local Wolfram tested | 14.2.1 for Mac OS X ARM (64-bit), March 16, 2025 |
| Local Julia tested | 1.10.5; MAT 0.10.7, MatrixMarket 0.5.2 |
| Python | 3.10+; standard library only for the release tools |

The cluster has two Julia projects: the conda default lacks MAT, while the
user's `v1.10` project contains it. Merely activating the conda environment
is therefore insufficient evidence that it is the correct project. The
release always passes `--project=<release>/julia` explicitly.

These are observations of surviving scripts and the current environment,
not a recovered immutable 2025 environment snapshot. All 63 supplied original files match the cluster copies by SHA-256. The author-review directory
records the broader source comparison and remote query results.

The Julia manifest was resolved from installed packages without updating the
user's global environment. A normal first installation can use
`julia --project=julia -e 'using Pkg; Pkg.instantiate()'`. The manifest pins the
tested dependency tree. Wolfram requires a separate license and is not bundled.

In the Codex sandbox, Wolfram's CSV importer/exporter stalled; the same small
tests completed under normal local process permissions. This was an execution
environment issue, not a change to the computational formulas.
