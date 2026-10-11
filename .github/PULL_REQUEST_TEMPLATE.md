QRH-Type: choose-maintenance-or-new-bound

<!-- Replace the value above with exactly maintenance or new-bound.
Every PR needs this standalone marker in its body. For new-bound, fill in the
two fields below. For maintenance, remove them. Use the exact bound string from
the independently checked receipt, for example 4374433/5000000; do not round it.
Changing proofs/, public/proofs/, submissions/, catalogue/, public/catalogue.json,
public/registry.json or registry/records/ requires new-bound, including renames.
-->
QRH-Result: stable-result-id
QRH-Bound: exact-checked-bound

## Change

Summary:

## For a mathematical result

Source, paper and proof links:
Current verification status and evidence:
Authors, project credits and human/AI collaboration attribution:
License and upstream notices:
Mathematical predecessors (separate from references):

- [ ] The verification label reflects the evidence actually available.
- [ ] Existing proof snapshots and historical evidence remain unchanged.
- [ ] Local site checks pass (`npm run check`).
- [ ] For `new-bound`, this PR changes only proof/result paths; changes to checking infrastructure are in a separate maintenance PR.
- [ ] For `new-bound`, an independent maintainer has checked this exact head with Comparator, Lean, NanoDa and con-ron, and its evidence is registered on the protected default branch.

The `qrh/pr-admission` check fails until the required markers and trusted
evidence match this exact PR head. A new commit requires a new reviewed
admission. A pending verification label or successful website build does not
satisfy this check. Website-only maintenance needs no proof receipt.

## Only for the separate signed admission workflow

- [ ] The proof matches the exact all-Dirichlet statement without added hypotheses.
- [ ] A valid manifest and Lean files are in a single `submissions/<id>/src/Candidate/` tree.
- [ ] Local attempts, failures and blockers are reported honestly.

Maintainers review the change and its evidence before merging. A successful
website build does not verify a mathematical proof. Merging a reviewed change
triggers automatic website deployment. Signed Comparator + NanoDa admission
is a separate, uncommissioned workflow. See [CONTRIBUTING.md](../CONTRIBUTING.md)
for the active PR admission process.
