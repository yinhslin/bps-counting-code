# Data dictionary and provenance

The selected files were supplied by the author on 23 October 2026. Each raw
file is preserved byte-for-byte. The top-level external inventory records file
sizes only; `raw/manifest.json` records SHA-256 for every selected raw file.

## Scan

The original cohomology CSV columns are
`L,nz1,nz2,nt1,nt2,nt3,n,NN,H,M`.
`L=3*nz1+3*nz2+2*nt1+2*nt2+2*nt3`, `n` is the letter degree,
`NN=7` for SO(7) and `NN=6` for USp(6), `H` is cohomology dimension and
`M` is monotone dimension. The fortuitous dimension is `H-M`.
`derived/cohomology_scan.csv` adds a `group` column and a header.

The scan represents nonnegative charges with `nz1<=nz2` and
`nt1<=nt2<=nt3`, and `2<=n<=sum(charges)`, through L=18. There are 938 such
sectors for each group. No extra degeneracy factor is inserted for permutations.
The vacuum and degrees below two are not rows in this scan. Both aggregate
tables cover all 938 expected sectors.

There are 937 canonical individual CSV files for SO(7) and 938 for USp(6).
For SO(7), `(L,charges,n)=(14,(0,2,1,1,2),5)` is present only under the
`-bk.csv` filename and in `total-so.csv`. Its values are `H=M=0`.
The adjacent count files independently give `60-60=0` and `M=0`.
The validator records this exception explicitly; the raw filename is retained.

The original `count/` CSV contains three quantities at degree n:
`closed(n), rank(Q:n->n+1), monotone(n+1)`.
Thus `H(n)=closed(n)-rank(Q:n-1->n)` and `M(n)` is the third column at n-1.
The supplied count files cover through L=16; 551 cohomology rows per group
can be cross-checked using both adjacent count records. L=17 and 18 instead
have the saved independent-basis workflow and aggregate cohomology outputs.

## Table I

`table_I_sources.json` identifies the four archived cluster logs. Its recorded
values are checked against the log text, the aggregate scan and the manuscript's
Table I. In those logs, `grav` is the dimension of the span of monotone
representatives **together with exact vectors**. It is not M itself:

`H = all - exact - nonclosed`, `M = grav - exact`, `F = H - M`.

The readable table is generated from these log values. No 10–28 GB basis file
was loaded merely to recount its rows. Earlier cluster logs contain failed or
superseded counts, including an SO bosonic `all=816`; the later corrected log
gives `all=826`. Only final logs consistent with the supplied aggregate data are
included. The author review archive retains the inspected earlier logs.

## Cartan image

For `(charges,n)=((1,1,2,2,2),8)`, both saved `reducedGraviton` objects have
an 84 by 492 coefficient matrix. The rows span the saved Cartan image; they are
**not** the original 85 SO(7) cohomology representatives.

`cartan_{so,sp}_matrix.csv` has 1-based `row,column,numerator,denominator`.
Only nonzero entries appear. `Rationalize[x,0]` exports the exact rational value
of each stored coefficient, without a fitted tolerance. The companion
`cartan_*_monomials.wl` lists the 492 monomials in column order. The integer
encoding of `X[...]` is defined by `index` in `wolfram/reducedgrav.m`.
`cartan_exports.json` records shape, raw-file hash and export environment.

Exact elimination in Python and Wolfram gives rank 84 for both stored matrices.
Together with the supplied monotone dimensions 85 and 84, this is consistent
with the paper's one-dimensional SO kernel. This check does not independently
reconstruct the restriction of the full 85-dimensional quotient or check that
every original exact vector restricts to zero.

## Scope of the selected dataset

The compact release includes CSV counts, cohomology totals, the two final
Cartan-image MX files, four final count logs, and readable derivatives. The
large trace bases, Q-action matrices and intermediate MX files remain in the
author's external archive and are indexed in `external_inventory.csv.gz`.
No claim is made here that the complete 3.13 TB archive is publicly deposited.
