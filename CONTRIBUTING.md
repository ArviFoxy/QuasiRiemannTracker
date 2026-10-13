# Contributing to QRH Bounds

## Required PR declaration and admission

The workflow classifies each PR from its changed files and assigns the matching
`maintenance` and `new-bound` labels. Maintenance PR bodies contain a summary;
remove the result fields and New bound section from the template. A result PR
starts its body with its stable result ID, exact checked bound and decimal
approximation, for example:

```text
QRH-Result: example-result
QRH-Bound: 4374433/5000000
QRH-Decimal: 0.87488660
```

Use the exact bound proved by the submission. The standard submission manifest
represents rational bounds as numerator and denominator strings. Rational bounds must be positive and reduced,
with canonical integer strings of at most 200 digits. Checked bounds such as
`29/33` and `1/1` qualify for admission. Result PRs require the three body fields
above and a checkable proof. GitHub Actions runs verification when the PR opens
or changes, including drafts. The catalogue retains accepted
contributions; the best-bound display and record history select the strongest
verified bounds by exact comparison.

`QRH-Decimal` is required for new bounds. Supply a truncated decimal with a
canonical integer part (`0` or 1–200 digits starting with 1–9), a decimal point
and 1–200 fractional digits. Examples include `0.87878787` for `29/33` and `1.0`
for `1/1`. Every supplied digit is checked using exact integer arithmetic
(`BigInt`). When the exact value differs from the strongest current
**framework-verified** catalogue bound on the trusted base, include enough
digits to show that difference at the supplied precision.
For a frontier of `0.87488664704`, the example above needs at least eight
decimal places: `0.87488660` differs from `0.87488664`, while seven places would
show `0.8748866` for both. An equal exact bound accepts an accurate decimal at
any supported precision. For algebraic bounds, an identical exact expression
establishes this equality after verification. An
irrational bound keeps its exact expression in `QRH-Bound`; its decimal is
checked against the certified enclosure in the verification result.

Changes under `proofs/`, `public/proofs/`, `submissions/`, `catalogue/` or
`registry/records/`, and changes to `public/catalogue.json` or
`public/registry.json`, receive `new-bound`. This includes deletions, metadata
corrections and either path of a rename. New-bound PRs are confined to those
proof/result paths or Lean files outside `verifier/`, `core/` and `tests/`, which
also require new-bound admission. All other paths receive `maintenance`.
Mixed PRs receive both labels and fail admission. A QRH result declaration or
New bound section requires a PR confined to proof/result changes. Put website,
documentation, workflow, verifier and dependency changes in a separate
maintenance PR. The workflow creates missing managed labels and preserves
unrelated labels. File classification and proof verification determine admission.

The `qrh/pr-admission` workflow runs the default branch's checker on the exact
submitted commit. It compiles the standard submission in an offline sandbox,
compares its theorem with the canonical all-Dirichlet challenge, and requires
acceptance from Lean, NanoDa and con-ron. The permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`. A separate publishing job rechecks the PR
commit and declaration before reporting success.

## Submit a proof

1. Add `submissions/<id>/manifest.json`, `explanation.md`, `LICENSE`, optional
   `NOTICE`, and Lean modules under `src/Candidate/`. Use the schema in
   `schemas/submission.schema.json`; the manifest's exact bound must match
   `QRH-Bound`. `submissions/classical-euler-product/` is a complete example.
2. Include authorship, references, license and upstream attribution. Supply an
   entrypoint proving the canonical theorem with the declared bound. Keep
   checker and dependency changes in a separate maintenance PR.
3. Open the PR with the three declaration lines above. The workflow runs the
   checker automatically. Compiler and judge errors appear in the Actions log;
   reports and proof exports are retained as workflow artifacts for 30 days.
4. Correct any proof errors and push a new commit to rerun verification. After
   admission, website checks and maintainer review pass, the PR can merge.

The standard worker uses the pinned Lean 4.34.1 compiler and dependencies,
with the Lean 4.35.0-rc2 Comparator and three-kernel judge. Its setup reads
protected repository files. Candidate code executes with read-only dependency
mounts, a minimal environment, resource limits and network isolation.

Catalogue publication preserves the first successful verification time and
retains proof sources and reports for reproducibility. Existing catalogue
records keep their immutable evidence and source bindings. Website CI checks
those records and the website build.

## Local verification fallback

When the hosted worker reports an infrastructure or resource failure, admission
can use an independently verified local run for the same repository, PR number,
head commit, result ID and exact bound. A completed proof rejection fails
admission. Algebraic bounds and legacy layouts can use their existing local
replay profiles when the standard hosted profile cannot represent them. Run the [standard replay adapter](verifier/standard/README.md) on a
disposable Linux worker with sufficient resources; this server can host that
worker.

To register a local run, retain its complete replay dossier and add a record to
`verifier/pr-admissions.json` through a maintenance PR. The record contains
`repository`, `number`, `head_sha`, `result_id`, `theta_exact`, `pin` and
`contribution`. The existing replay validator checks the source bindings,
canonical challenge, checker controls, tool pins and all three kernel results.
The gate reads fallback records from the protected base branch. Dispatch
`PR admission` for the candidate PR after registering its local run.

For an irrational bound, retain its exact expression and a certified rational
`bound_interval` in the verification result. Both endpoints must yield the
declared decimal prefix. The standard manifest currently represents rational
bounds; additional exact representations require a corresponding canonical
challenge and verifier implementation in a maintenance PR.

For an update to the same catalogue contribution, retain its displayed `id` and
point `proof_revision` to the reviewed new proof snapshot. Preserve the previous
metadata in `historical_records` for authentication. The contribution retains
one chart point. Both revisions' proof archives and checker evidence stay
immutable. Add the explicit revision mapping and its evidence checks when
introducing a revision. The signed registry uses immutable contribution IDs and
the supersession rules below.

Liu's existing algebraic constant retains its exact expression and a certified rational enclosure for plotting. The validator checks the enclosure with integer arithmetic and preserves the theorem's exact constant. New algebraic forms need a reviewed exact representation and comparison method.

Status and evidence changes require maintainer review and PR admission. Automatic proof verification is the active admission path, with local replay
as the infrastructure fallback described above. The
automatic signed service below awaits commissioning, including an update to
require all three kernels and validation of that requirement.

For independent reproduction of an existing pending result, use the
[external verification evidence format](docs/EXTERNAL-VERIFICATION.md). It binds
the exact checked source and target to a reviewed immutable dossier, with separate
licensed-archive and remote-source publication modes.
The algebraic endpoint dossier's complete `collection.json` is pinned by
`evidence_collection_sha256` in `core/algebraic-kernel-pins.json`. Its digest
authenticates the exact manifest bytes; the manifest then binds every evidence
file, including the original report, publication transformations and logs.
Setting or updating the pin requires independent proof verification, evidence
review and code-owner review for `core/`. Preserve existing dossiers and
introduce later runs as separate evidence. Build-time validation authenticates
the retained evidence's integrity;
maintainers perform proof replay on the offline worker.

## Signed Comparator + NanoDa admission (awaiting commissioning)

The following lifecycle describes the signed service after commissioning.
Every submission also requires the active `qrh/pr-admission` check.

The track requires the fixed all-Dirichlet theorem. It quantifies over every natural modulus with `NeZero q`, every complex Dirichlet character and every complex `s` with `θ < s.re`, retaining `¬ (χ = 1 ∧ s = 1)` and `_root_.DirichletCharacter.LFunction`. Admission requires independent verification of this complete statement and its definitions, using the canonical challenge and permitted axioms.

1. Copy `submissions/openai-baseline/` to a new stable lowercase ID. Replace its explanation, author metadata and Lean proof. Keep your modules in `src/Candidate/`; use `Candidate.Main` or another valid module as your entrypoint.
2. Update `manifest.json` following `schemas/submission.schema.json`. Store numerator and denominator as canonical decimal **strings**: the first digit of each nonzero integer is 1–9, the denominator is positive, and gcd = 1. For example, use `7/8`, `29/33` or `1/1`. Bounds must be positive. The active PR gate requires an accurate decimal and, when the exact value differs from the strongest verified bound, enough digits to show that difference.
3. List all authors accurately, describe the method, include HTTPS references and an appropriate contribution license (Apache-2.0, MIT, BSD-2-Clause, BSD-3-Clause or CC0-1.0). Include `LICENSE` and preserve required notices. Maintainers review attribution, license compatibility and the rights to distribute all contributed material.
4. Document actual mathematical reuse in `builds_on`. IDs must exist in the published registry and predate this verification. Use `references` and the explanation for citations, comparisons and acknowledgments.
5. Run `npm run verify -- submissions/your-id --image sha256:APPROVED_LOCAL_IMAGE_ID` on the documented disposable Linux worker with sealed libraries. The protected workflow creates the signed public receipt after successful verification.
6. Open a PR confined to this submission directory, using the supplied template. Include regular text files: `manifest.json`, `explanation.md`, `LICENSE`, optional `NOTICE`, and Lean modules under `src/Candidate/`. Use the toolchain and dependencies supplied by the approved image; request new libraries in a separate infrastructure PR.
7. A maintainer dispatches the protected verification workflow. It fetches source blobs at the exact head, generates the canonical challenge, isolates checking, then signs a result in a separate job. Every head change requires a new run.
8. A different maintainer reviews attribution and licensing at that exact commit. After merge, the publication job checks that the merged submission content matches the receipt. Archive every successful signed receipt first, using the protected verification journal. Publication uses the earliest valid receipt for that exact revision.

Published IDs and receipts are immutable. New revisions need a new contribution ID; use explicit predecessors and, when appropriate, a signed supersession event. Withdrawals preserve historical evidence.

The example's mathematical authorship belongs to OpenAI. The original-terminal-proof example awaits infrastructure commissioning for the signed admission pipeline. OpenAI’s original proof passed independent checks on a Linux verification worker with Comparator, Lean, NanoDa and con-ron; its reports are linked in the catalogue.

### Replaying the pinned Liu contribution

Use the [sandboxed maintainer command](verifier/liu/README.md) from a protected,
reviewed checkout. The immutable Liu dossier retains the earlier native scripts
as historical evidence. Submit candidate code through the sandboxed maintainer
driver, which exports the canonical challenge before candidate code executes,
clears the candidate environment, runs every compilation offline under genuine
Linux confinement, and requires all three independent kernels. A maintainer
must review tool/profile changes separately from proof PRs.
