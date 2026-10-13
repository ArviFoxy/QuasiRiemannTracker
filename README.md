# Quasi-Riemann Tracker

Live: [gtimg.github.io/QuasiRiemannTracker](https://gtimg.github.io/QuasiRiemannTracker/)

Quasi-Riemann Tracker follows bounds on the real parts of zeros of Dirichlet
L-functions. The timeline and leaderboard show exact bounds, authors, sources,
and verification status. Smaller bounds are stronger; the generalized Riemann
hypothesis corresponds to a bound of $1/2$.

## Run locally

Use Node.js 22.17 or later. Repository checks also require Python 3.

```sh
npm ci
npm run dev
```

The site runs at `http://127.0.0.1:4173`. `npm run build` creates the static site
in `dist/`; `npm run preview` serves that build. Run `npm run check` to run the
tests and production build.

## Data

Proof sources live in `submissions/`. The build generates `public/catalogue.json`
from existing proof metadata in `proofs/` and the admission records of merged
submissions. Small verification records in `public/certificates/` link each
checked bound to its source commit and verification report.

Verified PR contributions are plotted at their PR submission time. Older
entries without a recorded PR submission date retain their documented date
and label; a submission date is not a mathematical discovery date. Verification
and merge dates are shown separately in the details. Metadata comes from the
latest admitted version before merge, while the first verification date and
linked certificate come from the earliest authenticated success for the same
PR head, bound and source tree. Metadata edits and reruns cannot reset that date.
The offline admission cache retains all eligible receipts; refresh it through
the normal online main-branch build to recover older receipts from the archive.

## Submit

1. Add Lean source under `submissions/<result-id>/src/Candidate/`, with theorem
   `Candidate.bound` in `Main.lean`. Use the pinned dependencies in
   [verifier/pins.json](verifier/pins.json) and
   [verifier/standard/lake-manifest.json](verifier/standard/lake-manifest.json).
2. Open a PR using the [submission template](.github/PULL_REQUEST_TEMPLATE.md).
   Start its body with the result ID, exact bound, and decimal approximation:

   ```text
   QRH-Result: example-bound
   QRH-Bound: 7/8
   QRH-Decimal: 0.875
   ```

   Give enough decimal digits to differ from the current best verified bound.
   Equal bounds accept any supported decimal precision. Fill in the template's
   `qrh-metadata` block with the title, authors, description, and source credits.

3. GitHub Actions checks the exact PR head, including drafts. Comparator checks
   the statement and allowed axioms against the
   [canonical target](verifier/upstream-challenge.lean), with the submitted bound
   substituted for $7/8$. Lean, NanoDa, and con-ron must all accept the proof.
   After review and merge, the website adds the result automatically.

Verified bounds of any strength are eligible for admission. Improving bounds
advance the best verified bound shown on the site. Maintenance PRs use a plain
description; edits to proofs and bounds trigger their respective validations.

## Hosting

GitHub Actions builds and deploys `main` to GitHub Pages. For another static
host, run `npm run build` and publish `dist/`. Set `QRH_BASE_PATH` to the site's
URL prefix when hosting under a subdirectory.

## License

Project code is licensed under [Apache-2.0](LICENSE). Third-party proofs and
dependencies retain their original licenses and attribution; see [NOTICE](NOTICE).
