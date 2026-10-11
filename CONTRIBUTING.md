# Contributing to QRH Bounds

## Required PR declaration and admission

Every PR body must contain exactly one standalone declaration:

```text
QRH-Type: maintenance
```

Use `maintenance` for website, documentation or separately reviewed checking
infrastructure changes; remove the result, bound and decimal fields for this
type. A result/proof PR instead declares its stable result ID, exact checked
bound and decimal approximation, for example:

```text
QRH-Type: new-bound
QRH-Result: example-result
QRH-Bound: 4374433/5000000
QRH-Decimal: 0.87488660
```

Use the exact bound string authenticated by the maintainer receipt and admission
record. Do not substitute a rounded decimal for a rational or algebraic bound.
The title, labels and an author-written check report cannot replace these body
fields or independent evidence.

`QRH-Decimal` is required for new bounds. Supply `0.` followed by 1–200 digits,
truncated rather than rounded. Every supplied digit is checked using exact
integer arithmetic (`BigInt`). Include enough digits to differ from the
strongest currently **framework-verified** catalogue bound on the trusted base,
truncated to the same precision; pending and historical records do not count.
For a frontier of `0.87488664704`, the example above needs at least eight
decimal places: `0.87488660` differs from `0.87488664`, while seven places would
show `0.8748866` for both. A bound equal to the current frontier cannot satisfy
this rule. An irrational bound keeps its exact expression in `QRH-Bound`; its
decimal is checked against the certified enclosure in the trusted evidence.

Changes under `proofs/`, `public/proofs/`, `submissions/`, `catalogue/` or
`registry/records/`, and changes to `public/catalogue.json` or
`public/registry.json`, require `new-bound`. This includes deletions, metadata
corrections and either path of a rename. New-bound PRs may change only those
proof/result paths or Lean files outside `verifier/`, `core/` and `tests/`, which
also require new-bound admission. Put workflow, verifier, dependencies and other checking
infrastructure changes in a separate maintenance PR.

The `qrh/pr-admission` check uses trusted default-branch code and evidence. For
`new-bound`, it fails until an independent maintainer has registered an accepted
check for this repository, PR number, exact head commit, result ID and exact
bound. It requires Comparator and all three kernels: Lean, NanoDa and con-ron.
It does not execute submitted Lean or scripts. Site CI success, a
`verification-pending` label and an author-supplied receipt cannot satisfy it.
Pushing a new commit invalidates the old admission, even if the proof looks
unchanged. Editing the declaration reruns admission as well.

## Add a result or improve the website

1. Fork the repository and create a branch. For a result, edit `catalogue/results.json`, preserving exact constants, authorship, publication dates and evidence links. Keep any checking infrastructure changes in a separate PR.
2. Use **framework-verified** only after an independent maintainer run in the trusted offline Linux sandbox: the exact claimed statements and their definitions must pass Comparator, with exported proofs accepted by Lean, NanoDa and con-ron. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The maintainer receipt must bind the complete checked source and dependency pins; author-written reports or regenerated checksums cannot grant verification or preserve acceptance after a source change. Retain the source, checker pins, exact statements and acceptance reports for maintainer review. These labels do not create a signed Comparator/NanoDa receipt. Use the first successful independent run for the verification date and timeline. Existing **verification-pending** entries describe historical evidence; that label does not exempt a new PR from admission.
3. Add proof sources under `proofs/<stable-id>/` with license/attribution and reproduction instructions. Existing proof snapshots are immutable; submit revisions as a new directory. Heavy Lean checks run independently of website CI.
4. Run `npm ci --ignore-scripts`, `npm run check`, and `npm run test:browser` (install Chromium with `npx playwright install chromium` if necessary).
5. Open a pull request with the required body declaration, attribution and evidence links. A result PR remains blocked until its independent check and exact-head admission are available. After `qrh/pr-admission`, site checks and maintainer review, merging updates the public website automatically through GitHub Pages.

### Registering an independently checked head

A maintainer runs the appropriate reviewed replay driver on a disposable,
offline Linux worker, then reviews the resulting receipt, complete source
bindings, canonical challenge, checker acceptance and isolation evidence.
Only the replay profiles supported by `core/maintainer-replay.mjs` can be
admitted. If a result needs a new driver, target representation or tool profile,
review and merge that infrastructure first, then perform the independent check.
The PR gate never invents a profile or treats a general Lean build as acceptance.

Publish the immutable replay dossier under `evidence/pr-checks/<id>/` and add
its record to `verifier/pr-admissions.json` in a separate maintainer-reviewed
maintenance PR. An already reviewed dossier under `public/proofs/` may also be
referenced; use `evidence/pr-checks/` for new admission dossiers so registering
evidence does not itself require a proof admission. The admissions file has
`schema_version: 1` and an `admissions` array. Each entry specifies
`repository`, `number`, `head_sha`, `result_id`, `theta_exact`, `pin` and
`contribution`; the pin and contribution must pass the existing independent
replay validator. The dossier's `reviewed_pr_head` must match `head_sha`.
The `pin` uses the existing replay-pin format (for example,
`core/cycle25-kernel-pins.json`). The `contribution` identifies the checked source
`repository`, `source_commit`, `source_compiler`, `judge_toolchain` and
`palomar_commit`, plus any fields required by that replay profile.
Evidence or admission records supplied only by the candidate PR are not trusted.

For an irrational exact bound, the checksum-pinned `result.json` must include
a certified `bound_interval` for that same `theta_exact`, with rational
`lower` and `upper` objects containing `numerator` and `denominator`. The gate
reads this report through the existing replay validator; there is no PR-body
interval field. Both interval endpoints must produce the declared decimal
prefix at its supplied precision. If they disagree, refine the certified
enclosure before registering the evidence.

Once that maintenance PR is on the default branch, a maintainer can dispatch
the PR admission workflow with the candidate PR number to check its current
head again. Do not push a cosmetic commit just to rerun it: that creates a new
head requiring a new admission. No historical or pending PR is automatically
grandfathered into this process. The admissions file starts empty.

For an update to the same catalogue contribution, retain its displayed `id` and
point `proof_revision` to the reviewed new proof snapshot. Preserve the previous
metadata in `historical_records`; it remains authenticated but does not create
another chart point. Both revisions' proof archives and checker evidence stay
immutable. Add the explicit revision mapping and its evidence checks when
introducing a revision. This catalogue workflow does not change the separate
signed registry's immutable contribution IDs or supersession rules below.

Liu's existing algebraic constant retains its exact expression and a certified rational enclosure for plotting. The validator checks the enclosure with integer arithmetic; a truncated decimal must not replace the theorem's constant. New algebraic forms need a reviewed exact representation and comparison method.

No author can grant themselves a verified badge merely by passing a website build. Status and evidence changes require maintainer review and PR admission. The automatic signed admission path below is not running. It must be updated to require all three kernels and tested before it can admit verified results. Commissioning that separate service is not needed for the independent maintainer replay lane above.

For independent reproduction of an existing pending result, use the
[external verification evidence format](docs/EXTERNAL-VERIFICATION.md). It binds
the exact checked source and target to a reviewed immutable dossier, with separate
licensed-archive and remote-source publication modes. It does not alter the
signed admission protocol.
The algebraic endpoint dossier's complete `collection.json` is pinned by
`evidence_collection_sha256` in `core/algebraic-kernel-pins.json`. Its digest
authenticates the exact manifest bytes; the manifest then binds every evidence
file, including the original report, publication transformations and logs. A
contributor cannot replace the reports and recalculate their checksums without
invalidating this pin. Maintainers set or update it only after independent proof
verification and evidence review, with the code-owner review required for `core/`.
Do not regenerate the pin automatically to fix a failing build. Preserve existing
dossiers and introduce later runs as separate evidence. This integrity check
does not rerun Lean or create a signed registry admission.

## Signed Comparator + NanoDa admission (separate, not yet commissioned)

The following lifecycle describes the separate service once commissioned. Its
workflow is not a substitute for the active `qrh/pr-admission` requirement.

The track admits only the fixed all-Dirichlet theorem. It quantifies over every natural modulus with `NeZero q`, every complex Dirichlet character and every complex `s` with `θ < s.re`, retaining `¬ (χ = 1 ∧ s = 1)` and `_root_.DirichletCharacter.LFunction`. Zeta-only, conditional and restricted-character results do not qualify. A manuscript, a successful Lean build or an AI critic's approval is not admission evidence.

1. Copy `submissions/openai-baseline/` to a new stable lowercase ID. Replace its explanation, author metadata and Lean proof. Keep your modules in `src/Candidate/`; use `Candidate.Main` or another valid module as your entrypoint.
2. Update `manifest.json` following `schemas/submission.schema.json`. Store numerator and denominator as decimal **strings**, with a positive denominator, no leading zeros, and gcd = 1. `14/16` is rejected; use `7/8`. Bounds must be at most `7/8`; the active PR gate additionally requires a decimal digit differing from the current verified frontier.
3. List all authors accurately, describe the method, include HTTPS references and an appropriate contribution license (Apache-2.0, MIT, BSD-2-Clause, BSD-3-Clause or CC0-1.0). Include `LICENSE` and preserve required notices. Maintainers still review compatibility and attribution; a declared license alone cannot grant rights you do not have.
4. Put only actual mathematical reuse in `builds_on`. IDs must exist in the published registry and predate this verification. Put citations, comparisons and acknowledgments in `references`/explanation instead. Method similarity does not imply dependence.
5. Run `npm run verify -- submissions/your-id --image sha256:APPROVED_LOCAL_IMAGE_ID`. This requires the documented disposable Linux worker and sealed libraries. A local attempt is not a signed public receipt.
6. Open a PR changing **only this submission directory**, using the supplied PR template. No symlinks, binaries, `.olean` files, lakefiles, toolchain changes, caches, workflow changes or registry entries are allowed. Dependencies come from the approved image; request new libraries in a separate infrastructure PR.
7. A maintainer dispatches the protected verification workflow. It fetches source blobs at the exact head, generates the canonical challenge, isolates checking, then signs a result in a separate job. A head change requires a new run, even if the Lean files look unchanged.
8. A different maintainer reviews attribution and licensing at that exact commit. After merge, the publication job checks that the merged submission content matches the receipt. Archive every successful signed receipt first, using the protected verification journal. Publication uses the earliest valid receipt for that exact revision.

Published IDs and receipts are immutable. New revisions need a new contribution ID; use explicit predecessors and, when appropriate, a signed supersession event. Withdrawals do not delete historical evidence.

The example's mathematical authorship belongs to OpenAI, not to QRH Bounds. The original-terminal-proof example is currently infrastructure-blocked in this stricter admission pipeline. OpenAI’s original proof was checked separately on Linux verification worker with Comparator, Lean, NanoDa and con-ron; its reports are linked in the catalogue.

### Replaying the pinned Liu contribution

Use the [sandboxed maintainer command](verifier/liu/README.md) from a protected,
reviewed checkout. The immutable Liu dossier's earlier native scripts are
historical evidence and must not be used as untrusted-submission entrypoints.
The replacement exports the canonical challenge before candidate code executes,
clears the candidate environment, runs every compilation offline under genuine
Linux confinement, and requires all three independent kernels. A maintainer
must review tool/profile changes separately from proof PRs.
