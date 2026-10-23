# Release verification, 23 October 2026

The following checks passed. Machine-readable detail is in `test_record.json`
and `data/derived/validation.json`.

| Check | Result |
|---|---|
| Original source vs cluster | All 63 supplied files match by SHA-256 |
| Selected raw result files | All 3,232 files match their SHA-256 manifest |
| Scan coverage | 938 expected symmetry-reduced sectors per group through L=18 |
| Aggregate vs individual results | All present individual records agree; one SO backup-only record is documented and independently checked from adjacent counts |
| Adjacent count formula | 551 rows per group checked |
| Table I | All five state-count rows in all four columns match archived final job logs; cohomology and monotone dimensions also match the scan |
| Stored Cartan-image matrices | Both 84 by 492; exact rational rank 84 in Wolfram and independently in Python |
| Exact small pipeline | SO(7) and USp(6), `(charges,n)=((0,0,0,0,2),2)`, both H=M=1 |
| Numerical small pipeline | SO(7) and USp(6), `(charges,n)=((0,0,1,1,1),2)`, both H=M=2; nonzero Q-image exercised |
| Julia matrix interface | Six assertions: rank-deficient basis, zero matrix, product row span and paths with spaces |
| Python tools | Four tests: supplied dataset, split preservation, incomplete matrix rejection and exact rational rank |
| Missing stage input | Runner exits with an error and creates no result CSV |

The full L=18 complex, all large basis ranks, and the entire Cartan restriction
map have not been independently recomputed. The large basis dimensions in Table I
were checked from final cluster logs, not by loading all large MX files again.
The reorganized reference pipeline has not been benchmarked for L=18 or retested
with parallel subkernels. Its optional Cartan recomputation stages are retained
from the author's source; the current release check uses the supplied final
Cartan-image files.

The source archive includes earlier failed or superseded calculations. They are
not treated as alternative valid scientific results. Selection of the four
public logs is recorded explicitly and is cross-checked against the final data.

The checks above were completed during release preparation. Publication
identifiers are recorded separately; no journal submission was performed.
