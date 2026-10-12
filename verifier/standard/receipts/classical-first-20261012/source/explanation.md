# Classical Euler-product bound

The exact bound is `1/1`, with decimal approximation `1.0`.
`Candidate.bound` proves the canonical all-Dirichlet statement: for every
positive modulus and every complex Dirichlet character, the L-function is
nonzero when `1 < s.re`, with the canonical pole-exclusion hypothesis.

The proof applies Mathlib’s equality between the continued L-function and its
Dirichlet series, followed by nonvanishing in the half-plane of absolute
convergence. `Candidate.zeta_bound` gives the zeta specialization.

The standard verifier generates `QRH.canonical_bound` and its solution wrapper
from `manifest.json`. It supplies the pinned Lean toolchain and Mathlib
libraries. Run from the repository root on the approved verification worker:

```sh
npm run verify -- submissions/classical-euler-product --image sha256:APPROVED_LOCAL_IMAGE_ID
```

PR admission requires an independently checked receipt for the current PR head.
The standard generated challenge checks the all-Dirichlet declaration.

These wrappers were prepared with AI assistance. The mathematical results are
Mathlib’s; `NOTICE` identifies the original authors and pinned source files.
`builds_on` lists tracker contributions reused mathematically; Mathlib is the
library dependency cited in `references`.

The historical catalogue date proposed for this result is 1922, the printing
year in Hardy and Littlewood’s *Partitio numerorum III*. Its volume is catalogued
as 1923. This dates an early fixed-half-plane formulation; the Euler-product
nonvanishing bound was already classical. Publication of the catalogue point
follows independent verification and admission of this submission.
