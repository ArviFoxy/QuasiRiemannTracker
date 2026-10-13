# GitHub submission and publication workflow

The active contribution workflow is PR → automatic classification,
`qrh/pr-admission` and site checks → maintainer review/merge → automatic Pages
deployment; see `DEPLOYMENT.md`. A successful site build checks the website and evidence
integrity. The admission worker executes proof verification.

## Required PR admission

The workflow infers the PR category from its changed files. New-bound PR bodies
start with three standalone lines:
`QRH-Result: <stable-id>`, `QRH-Bound: <exact-checked-bound>` and
`QRH-Decimal: <truncated-decimal>`. Maintenance PR bodies contain the change
summary; result fields and the `New bound` section belong to new-bound PRs.
The exact bound must match the submission manifest and the theorem checked by
the worker. Positive bounds such as `29/33` and `1/1` qualify for
admission after successful verification. The catalogue retains accepted
contributions, and the best-bound display selects the strongest verified value.
See `../CONTRIBUTING.md` for examples.

The decimal has a canonical integer part (`0` or 1–200 digits starting with
1–9), a decimal point and 1–200 truncated fractional digits. The validator
checks every digit using exact `BigInt` arithmetic. When the exact bound differs
from the strongest currently **framework-verified** catalogue bound on the
trusted base, supply enough digits to show that difference at the declared
precision. For example, `4374433/5000000` requires
`QRH-Decimal: 0.87488660` to distinguish it from a frontier of `0.87488664704`
(`0.87488664` at eight places); the first differing digit is the eighth. An equal
exact bound accepts an accurate decimal at any supported precision. For
algebraic bounds, an identical exact expression establishes this equality after
verification.

Any change under `proofs/`, `public/proofs/`, `submissions/`, `catalogue/` or
`registry/records/`, or to `public/catalogue.json` or `public/registry.json`,
forces the new-bound lane. Both names of a renamed file count. New-bound PRs
must contain only proof/result paths. Lean files outside `verifier/`, `core/`
and `tests/` also require new-bound admission. Checking code and trust policy
updates belong to separate maintenance PRs.

All other changed paths are maintenance. The workflow assigns `new-bound` and
`maintenance` labels for each detected category, creating these labels as needed
and preserving unrelated labels. These labels are informational: admission always uses the
actual changed paths. A PR containing both kinds of changes receives both labels
and fails admission. A result declaration or `New bound` section also fails if
the PR contains any maintenance changes, including a maintenance-only PR.

Draft and ready-for-review PRs run the same admission checks. Maintainers can
also dispatch proof verification for either status.

The admission workflow runs on `pull_request_target` for `opened`, `reopened`,
`synchronize`, `edited`, `ready_for_review` and `converted_to_draft`, and supports a maintainer
`workflow_dispatch` with a PR number. The admission validator executes from the
trusted default-branch checkout; PR metadata and changed paths arrive through
the GitHub API as data. For PRs with more than 3,000 changed files, it reads
the diff between the merge base and exact head in a temporary bare Git
repository. The file count must agree with the PR metadata. Rename detection
retains both paths, and Git runs with external diff commands and text
conversion disabled. It posts `qrh/pr-admission` to the current PR
head. Body edits and head changes rerun verification.

The workflow has three jobs:

1. `prepare` classifies changed files, manages category labels and validates the
   declaration. Maintenance PRs complete admission here. Result PRs receive a
   pending check and an immutable context artifact for this run and attempt.
2. `verify` fetches the exact head as Git objects and reads the standard
   submission as data. It installs pinned tools and dependencies, then compiles
   the proof in Palomar's offline sandbox. Comparator checks the canonical
   theorem and its definitions; Lean, NanoDa and con-ron check the exported
   proof. This job has read-only repository permissions. Logs, reports and
   exports are uploaded automatically with 30-day retention.
3. `admission` consumes only artifacts from the same run and attempt. It checks
   the source identity, declared bound, complete kernel acceptance and sandbox
   controls, validates the decimal, rechecks current PR metadata, and completes
   `qrh/pr-admission`. This separate job holds the check-publishing permission.

All orchestration and checker code comes from the protected default branch.
The candidate supplies its manifest and proof files through
`submissions/<id>/`. A successful live check directly satisfies admission.

For infrastructure or resource failures, the publishing job can use a matching
local replay registered in `verifier/pr-admissions.json` on the base branch.
`validateMaintainerReplay` authenticates the local dossier, source, exact head,
bound, canonical theorem, controls and all three kernels. Proof rejection and
invalid standard submissions fail admission. Existing local profiles remain
available for algebraic bounds and legacy proof layouts. See `../CONTRIBUTING.md` for the local
fallback process. A stronger disposable worker on the local server can produce
that replay when the standard hosted worker lacks capacity.

An irrational bound retains its exact expression and a certified rational
`bound_interval`. Both interval endpoints must yield the declared decimal
prefix. The standard submission format currently supports rational bounds;
new exact representations require an appropriate checker implementation.

GitHub check results belong to commits. After a body-only edit, the previous
result may remain visible until the new run posts its check; a runner startup
failure needs a fresh dispatch. Review the latest admission run before merging.
Changing proof code always changes the head and requires new verification.

## Repository protection setup (required)

Merge enforcement requires the repository owner to activate these branch
protections and rulesets in GitHub:

- Require `qrh/pr-admission` and the existing `test` check on the default branch before merge.
- Preserve the default branch and its history through branch protection; route changes through reviewed PRs, require independent maintainer review, dismiss stale approvals and require approval of the most recent push. Apply these requirements to administrators and bots.
- Require code-owner review for `.github/`, `verifier/`, `evidence/pr-checks/`, `worker/`, `schemas/`, `core/`, lockfiles and all `registry/` paths. Keep checking infrastructure changes separate from proof/result PRs.
- Prefer a repository/organization rule requiring the protected admission workflow or a dedicated check-producing GitHub App. These options bind the required check to its trusted producer as well as its name.
- Restrict Actions to approved actions pinned by commit and default read-only token permissions. The admission workflow needs `checks: write` to publish its result and `pull-requests: write` to manage category labels. Keep its executable code restricted to the trusted default branch.
- Keep the append-only registry check mandatory for all registry changes: `node verifier/audit-history.mjs BASE_COMMIT`. Validate signed contents with `npm run build`. Obtain `BASE_COMMIT` from the protected base SHA.

After merging the gate, activate and confirm the required checks and independent
review settings. Automatic admission operates independently of the signed service below.

## Separate signed service (commissioning required)

The following describes the signed proof-admission service after commissioning.
Activation requires updating and testing its all-three-kernel requirement.
The active `qrh/pr-admission` requirement also applies to these submissions.

### Additional branch and environment protections

- Restrict Actions to approved actions pinned by commit and default read-only token permissions. Scope verification and publication secrets to their protected signing and publication environments. The verification workflow accepts **maintainer `workflow_dispatch` only** on the default branch and checks out the immutable `github.workflow_sha` for executable orchestration.
- Require the exact-head verification check produced by the protected signing job before merge, alongside code-owner, attribution and license review. Where available, bind its trusted producer through a protected-workflow ruleset or dedicated GitHub App. Signed-record verification also gates publication.
- Protect `verification-workers`, `receipt-signing` and `registry-publication` environments: require the default branch and approval from a maintainer other than the initiating actor, and enforce these requirements for every actor. Provision `verification-workers` with public inputs only. Store Ed25519 verification/publication private keys separately in the two signing environments; public keys and permitted IDs go in reviewed policy.
- Provision the `qrh-ephemeral` runner group exclusively as JIT/one-job disposable Linux VMs. The worker image is prebuilt, locally available and pinned by actual image ID. Destroy the entire runner after each checking job, including failures. Rootless Docker, kernel support and cgroup limits must be operational and commissioned.

### Signed proof PR lifecycle

1. The contributor opens a PR adding a single `submissions/<id>/` directory. Trusted code validates the schema, file count/size, normalized rational, safe paths, file modes and IDs, and enforces the single-directory scope.
2. A maintainer dispatches **Verify submission (trusted dispatch)** with the PR number. Trusted API calls fetch raw blobs at its exact 40-character head SHA. Reviewed orchestration compiles candidate Lean exclusively inside the offline unprivileged container. Credentials remain in the host orchestration, and dependency/cache mounts are read-only.
3. On success, a separate hosted runner downloads the artifact from that same workflow run and attempt. It checks commissioning and current PR head, signs a receipt using the protected verification key, and posts the exact-head check to the PR commit. Successful receipt issuance requires checker acceptance at that current head. Operational logs retain pending, failed, timed-out and blocked attempts separately from the registry.
4. Retain **every successful signed receipt** immediately in the protected journal. Download the signed artifact and run `node verifier/archive-receipt.mjs path/to/receipt.json path/to/verification.log`. Submit these content-addressed files in a separate maintainer journal PR. Archive the first success before accepting a rerun to preserve the first-verification timestamp. Keep logs durably in Git/object storage with authenticated digests beyond GitHub's 90-day artifact retention.
5. An independent maintainer explicitly reviews attribution, license and explanation and approves the exact head. The latest review per reviewer wins; dismissed or changed reviews revoke approval. Merge only after these checks.
6. Dispatch **Prepare signed publication** with the successful verification run/attempt. It authenticates the Ed25519 receipt, checks the earliest journal receipt, current PR head, independent review and merged source digest. A merge conflict resolution that changes the proof fails the content check and needs a new reviewed submission/receipt.
7. The job creates a signed publication bundle artifact. Put it under `registry/records/<id>/` through a maintainer-reviewed registry PR; run registry authentication/build and immutable-history audit. Deploy the generated static site through the separate approved hosting process.

Publication jobs run reviewed artifact preparation code and produce bundles for
maintainer-reviewed registry PRs. Repository publication authority stays with
the protected publication environment and maintainer review. Signed-service
entrypoints are restricted to trusted maintainer dispatch.

## Withdrawals and supersessions

From protected maintainer code with the publication signing key and `QRH_REVIEWER`, run:

```sh
node verifier/events.mjs withdraw existing-id 'Reason for withdrawal'
node verifier/events.mjs supersede old-id 'Reason for supersession' new-id
```

Commit the new signed, chained event through registry review. Preserve the receipt, original publication and historical source as immutable records. The table can include withdrawn records; the active ranking and frontier respond to events while history retains earlier accepted results.
