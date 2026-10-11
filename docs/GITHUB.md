# GitHub submission and publication workflow

The active contribution workflow is PR declaration → `qrh/pr-admission` and
site checks → maintainer review/merge → automatic Pages deployment; see
`DEPLOYMENT.md`. A successful site build checks the website and evidence
integrity. It does not establish a new mathematical result.

## Required PR admission

Every PR body needs exactly one standalone `QRH-Type: maintenance` or
`QRH-Type: new-bound` line. New-bound PRs also need `QRH-Result: <stable-id>` and
`QRH-Bound: <exact-checked-bound>`. The exact bound must match the independently
checked receipt and protected admission record; a rounded approximation is
insufficient. See `../CONTRIBUTING.md` for examples.

Any change under `proofs/`, `public/proofs/`, `submissions/`, `catalogue/` or
`registry/records/`, or to `public/catalogue.json` or `public/registry.json`,
forces the new-bound lane. Both names of a renamed file count. New-bound PRs
must contain only proof/result paths, so the submission cannot change the code
or trust policy used to accept itself. Lean files outside `verifier/`, `core/`
and `tests/` also require new-bound admission.

The admission workflow runs on `pull_request_target` for `opened`, `reopened`,
`synchronize`, `edited`, `ready_for_review` and `converted_to_draft`, and supports a maintainer
`workflow_dispatch` with a PR number. It runs the trusted default-branch
validator, reads PR metadata and changed paths as data, and posts
`qrh/pr-admission` to the current PR head. It never checks out or executes PR
code, installs candidate dependencies, or runs proof compilation with the
workflow token. Body edits rerun the check; a head change requires a new
independent admission.

For a new bound, the validator reads `verifier/pr-admissions.json` from the
trusted base. Its initially empty `admissions` array contains records binding
the repository, PR number, exact `head_sha`, `result_id` and `theta_exact` to
the reviewed `pin` and `contribution`. An entry alone is not acceptance:
`validateMaintainerReplay` authenticates the complete immutable dossier,
source revision/content, exact bound, canonical challenge, replay driver and
dependency pins, allowed axioms, isolation checks, Comparator acceptance and
Lean/NanoDa/con-ron results. The receipt must also bind `reviewed_pr_head` to
the candidate head. Missing, stale or invalid evidence fails the check.

Maintainers perform the actual replay on the reviewed offline Linux worker.
They register the resulting dossier under `evidence/pr-checks/<id>/` and its
admission record in a separate infrastructure maintenance PR. Existing trusted
`public/proofs/` dossiers can also be referenced. New profiles or checker
changes must be reviewed separately before the replay; the gate supports only
the existing reviewed replay profiles. A candidate cannot supply its own
admission through its branch. After the evidence PR merges, dispatch the gate
for the unchanged candidate head to refresh its check.

The workflow becomes active only after its bootstrap PR merges into the
default branch. Then dispatch it for already-open PRs, including PR #15, or
wait for a supported PR event. Existing green site checks do not imply an
admission. No old PRs are preapproved.

GitHub check results belong to commits. After a body-only edit, the previous
result may remain visible until the new run posts its check; a runner startup
failure needs a fresh dispatch. Review the latest admission run before merging.
Changing proof code always changes the head and requires new evidence.

## Repository protection setup (required)

Branch protection and repository rulesets were not configured when this gate
was introduced. A workflow cannot make itself a required merge condition:
the repository owner must configure the following protections in GitHub.

- Require `qrh/pr-admission` and the existing `test` check on the default branch before merge.
- Protect the default branch against direct pushes, force pushes and deletion; require independent maintainer review, dismiss stale approvals and require approval of the most recent push. Prevent administrator/bot bypass for submission admission.
- Require code-owner review for `.github/`, `verifier/`, `evidence/pr-checks/`, `worker/`, `schemas/`, `core/`, lockfiles and all `registry/` paths. Keep checking infrastructure changes separate from proof/result PRs.
- Prefer a repository/organization rule requiring the protected admission workflow or a dedicated check-producing GitHub App. Requiring a check name alone does not prevent another workflow from producing a same-name check. Ordinary PR-controlled CI is not an admission authority.
- Restrict Actions to approved actions pinned by commit and default read-only token permissions. The admission workflow needs a check-writing token only to publish its result; it must keep candidate code out of that runner.
- Keep the append-only registry check mandatory for all registry changes: `node verifier/audit-history.mjs BASE_COMMIT`. Validate signed contents with `npm run build`. `BASE_COMMIT` must be the actual protected base SHA, not a submitted string.

These settings are an owner setup step; adding workflow files does not enable
them. Check both required checks and independent review settings after merging
the gate. The active maintainer replay lane does not depend on commissioning
the signed service below.

## Separate signed service (not yet commissioned)

The rest of this document describes the signed proof-admission service once
commissioned. It does not replace `qrh/pr-admission`. It must be updated and
tested to require all three kernels before it can admit verified results.

### Additional branch and environment protections

- Restrict Actions to approved actions pinned by commit and the default read-only token permissions. No secrets for fork PRs. The supplied verification workflow uses **maintainer `workflow_dispatch` only** on the default branch, and checks out the immutable `github.workflow_sha`. It never checks out a PR as executable orchestration.
- Require the exact-head verification check produced by the protected signing job (see below) before merge, in addition to code-owner/attribution/license review. Use an organization ruleset requiring this protected workflow or a dedicated check-producing GitHub App if available; do not treat an arbitrary same-name status from PR-controlled CI as authoritative. Signed-record verification still independently gates publication.
- Protect `verification-workers`, `receipt-signing` and `registry-publication` environments: default branch only, required independent maintainers, prevent self-review, no bypass. Configure no secrets in `verification-workers`. Store Ed25519 verification/publication private keys separately in the two signing environments; public keys and permitted IDs go in reviewed policy.
- Provision the `qrh-ephemeral` runner group as JIT/one-job disposable Linux VMs. Never attach a persistent general-purpose self-hosted runner. The worker image is prebuilt, locally available and pinned by actual image ID. Destroy the entire runner after each checking job, including failures. Rootless Docker, kernel support and cgroup limits must be operational and commissioned.

### Signed proof PR lifecycle

1. The contributor opens a PR adding a single `submissions/<id>/` directory. Schema, file count/size, normalized rational, safe paths, file modes and IDs are validated by trusted code. Workflow/library/registry changes are refused.
2. A maintainer dispatches **Verify submission (trusted dispatch)** with the PR number. Trusted API calls fetch raw blobs at its exact 40-character head SHA, not a tarball or submitted lakefile. No candidate script is executed on the runner. Candidate Lean runs only inside the offline unprivileged container, with no host API token or writable cache mounts.
3. On success, a separate hosted runner downloads only the artifact from that same workflow run and attempt. It checks commissioning and current PR head, and signs a receipt using the protected verification key. It posts the exact-head check to the PR commit. Failure or a source change produces no successful receipt. Pending/failure/timeout/blocker logs stay outside the registry.
4. Retain **every successful signed receipt** immediately in the protected journal. Download the signed artifact and run `node verifier/archive-receipt.mjs path/to/receipt.json path/to/verification.log`. Submit these content-addressed files in a separate maintainer journal PR. Archive the first success before accepting a rerun; this prevents the first-verification clock from moving. Keep logs durably in Git/object storage with authenticated digests; GitHub's 90-day artifact retention alone is insufficient.
5. An independent maintainer explicitly reviews attribution, license and explanation and approves the exact head. The latest review per reviewer wins; dismissed or changed reviews revoke approval. Merge only after these checks.
6. Dispatch **Prepare signed publication** with the successful verification run/attempt. It authenticates the Ed25519 receipt, checks the earliest journal receipt, current PR head, independent review and merged source digest. A merge conflict resolution that changes the proof fails the content check and needs a new reviewed submission/receipt.
7. The job creates a signed publication bundle artifact. Put it under `registry/records/<id>/` through a maintainer-reviewed registry PR; run registry authentication/build and immutable-history audit. Deploy the generated static site through the separate approved hosting process.

Publication jobs do not execute Lean, check out candidate sources as code, or grant the worker write access to the repository. They prepare artifacts, not automatic pushes or merges. This avoids giving a submission the ability to publish itself. The signed service uses no `pull_request_target` or candidate-controlled `workflow_run` entrypoint. The active PR admission workflow above uses `pull_request_target` only to read metadata and authenticate protected-base evidence.

## Withdrawals and supersessions

From protected maintainer code with the publication signing key and `QRH_REVIEWER`, run:

```sh
node verifier/events.mjs withdraw existing-id 'Reason for withdrawal'
node verifier/events.mjs supersede old-id 'Reason for supersession' new-id
```

Commit the new signed, chained event through registry review. Never edit/delete the receipt, original publication or historical source. The table can include withdrawn records; the active ranking and frontier respond to events while history retains earlier accepted results.
