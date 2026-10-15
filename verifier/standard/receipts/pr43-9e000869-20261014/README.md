# Independent maintainer verification of PR #43

The exact source at `9e0008692e77836a9a61cff25c808727d6d6690d` passed independent
verification on 2026-10-14T10:07:04.865497+00:00. The checked rational bound is
`4374299/5000000` (0.8748598), for the canonical all-moduli Dirichlet statement.

The [original worker receipt](result.json) has SHA-256
`83caa5da50d8ea98b1eb16c17d1a3ff01eff96c93334ae1cc3ed235f1c93250c`. It was generated outside the candidate's writable
environment, retrieved over authenticated SSH, and checked against the exact
source-file hashes, trusted challenge, tool hashes, dependency inventory and logs.
The [kernel log](judge.log) records acceptance by Comparator, Lean, NanoDa and
con-ron. Only `propext`, `Classical.choice` and `Quot.sound` were permitted.

All 206 submitted Lean modules were rebuilt from source. No candidate compilation
cache was reused. Approved upstream objects were copied into a private library
after matching the preserved manifests; 17 missing OpenAI modules were freshly
compiled from pinned upstream source. See [dependency pins](dependency-pins.json),
[additional source hashes](extra-oai-manifest.json), and [audit](audit.json).
The complete exported proof was then checked independently of those objects.

Execution used an unprivileged Linux worker with the real Palomar sandbox,
network isolation, private candidate home and temporary directories, protected
read-only libraries and source, and resource limits. Sandbox controls, a positive
proof control, a changed-statement control and an ill-typed-proof control passed.
The trusted challenge was exported before candidate execution and remained frozen.

The replay driver came from protected tracker revision
`43cc0ac1d57025c6e8df702b98c89a565820758e`, using Palomar
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, source Lean 4.34.1 and the pinned
4.35.0-rc2 checker toolchain. Its only adjustment reduced the host-relative memory
limits from 75%/85% to 2%/3% on this large worker. Compilation used eight threads;
kernels ran serially. The 600-second compilation limit and all proof checks were
unchanged. [replay-driver.txt](replay-driver.txt) preserves the exact driver bytes
as data; [tool-pins.json](tool-pins.json) preserves the executable hashes.

[logs.json](logs.json) maps artifact paths to their exact UTF-8 log contents.
Hashing each value as UTF-8 reproduces the corresponding `result.json` digest.
All 206 compilation logs, wrapper/export logs, checker controls and final judge
log are included. Large proof exports and host-specific setup/inventory files
remain in the maintainer's evidence store; their artifact hashes are retained in
the original receipt. Host paths and credentials are not published here.

[Challenge.lean](Challenge.lean) is the trusted statement template: its intentional
`sorry` is not a proof. [Solution.lean](Solution.lean) connects the submitted theorem
to that statement. Acceptance applies to the checked solution export.

This record is maintainer verification evidence, not a candidate-supplied claim.
Registration is limited to this exact PR head and bound. It does not bypass a
mathematical rejection or approve changed sources. Attribution and Apache-2.0
notices remain with Gao's contribution and its acknowledged predecessors,
including Hailey Collet's Cycle61 construction.
