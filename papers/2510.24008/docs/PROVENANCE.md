# Source and release changes

The author supplied 63 files on 23 October 2026. They were copied unchanged
to `archive/calculation_source_2026-10-23/` in the manuscript workspace before
any reorganization. Their byte counts and SHA-256 values are reproduced in
`original_source_manifest.json`. `source_map.json` identifies the twelve core
modules exposed by this release. The original archive is not part of the
public code package.

The source snapshot included successive runners, earlier numerical experiments,
Matrix Market variants, backup/test files, cluster-specific Slurm scripts and
old CSV exports. These are retained in the author archive. The public entry
point uses explicit charges and a validated dependency plan, eliminating the
old reliance on a charge-list index and on a particular account's home path.

Changes from the supplied computational core:

- Removed commented-out alternative implementations and notebook section markup.
- Centralized numerical transport; removed hardcoded cluster accounts and
  shell-constructed Julia paths. Arguments are passed as separate strings.
- Create a unique scratch directory before exporting matrices; stop on failed
  external commands or missing prerequisite files.
- Convert an out-of-loop `Continue[]` failure into an explicit abort.
- Handle empty numerical row selections without indexing a nonexistent row.
- Use an explicit 64-bit kernel check instead of the copied notebook `RefLink`.
- Keep the original matrix/graded-product/Q-action/Cartan formulas and the
  numerical rank cutoff. The default command-line mode is exact reduction;
  `--numerical` selects the author's active Float64 method.
- Replace the cluster-dependent shell splitter with a streaming Python splitter
  that preserves Matrix Market field types and checks declared entry counts.

The old numerical helpers imported packages that their active Float64 paths
did not use. The public Julia project therefore contains MAT and MatrixMarket
plus Julia standard libraries. Its manifest is a tested local lockfile, not a
claim that the cluster used the identical complete dependency lockfile in 2025.

Release checks and the small runner/interface repairs were assisted by OpenAI
Codex. This does not replace the authors' review of the algorithms or constitute
an independent reproduction of the full research computation. A detailed diff
and evidence log are retained in the manuscript's author-review directory.

The MIT license was explicitly selected by the author on 23 October 2026.
This companion continues the shared
[bps-counting-code](https://github.com/yinhslin/bps-counting-code) project.
Compared with commit `5d4d483d2ea94d582d88f1666a209ffb5eede179`, 31 of the
63 supplied files have identical Git blob hashes; eleven of the twelve core
Wolfram modules match files in `new/src/` exactly before the release edits above.
The remaining core module is `countC.m`. Code and data for this paper are
published in separate paper directories in the existing code and data
repositories; the combined archive records both exact repository revisions.
The new paper directories carry their own license and do not relicense
unrelated files in either repository.
