# Arithmetic and rank decisions

Without `--numerical`, the computational modules use Wolfram `RowReduce` on
the constructed coefficient matrices. This is practical only for smaller
sectors. The release tests do not establish that exact reduction is feasible
for all large sectors in the paper.

With `--numerical`, `qrC.jl` forms `G=A*transpose(A)`, converts it to a dense
Float64 matrix, and uses column-pivoted QR. The rank threshold, unchanged from
the supplied active core, is

`max(1e-7, 10*eps(Float64)*maximum(abs.(diag(R))))`.

The pivot indices select original rows of A; this is a row-basis selection,
not reduced row-echelon form. `dotqrC.jl` first forms `C=A*B` and applies the
same Gram/QR procedure to C. When both imported matrices have native integer
element types, the original helper's integer multiplication branch is retained;
otherwise multiplication uses Float64. Integer overflow is not certified by
this branch; the MAT transport used in the numerical smoke tests takes the
Float64 branch.

Forming a Gram matrix squares conditioning. The cutoff is applied to the
QR diagonal of G, not directly to singular values of A. The release preserves
this method and its threshold; it does not replace it with a modular, interval
or exact rank certificate. Higher-precision names accepted by the old generic
CLI are intentionally not exposed: the original product helper ultimately
converted its Gram matrix to Float64 anyway.

The logs print the threshold and nearby QR diagonal entries. Keep these logs
when running a new large sector. Results from different tolerances, arithmetic
modes or source versions should use separate working directories.

Changes in the numerical interface are limited to explicit subprocess argument
lists, checked return codes, creation of scratch directories, zero-rank handling,
one-matrix-per-MAT validation, and a streaming Matrix Market splitter that
preserves the header and validates the declared entry count. Inactive imports
and commented alternative algorithms were removed. No rank threshold was tuned
to match Table I.
