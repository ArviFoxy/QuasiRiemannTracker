# Replay a standard submission

This adapter uses the existing standard manifest, canonical challenge generator,
and solution wrapper. Palomar supplies sandbox confinement, resource limits,
Comparator and the Lean, NanoDa and con-ron kernels.

Prepare source from its immutable Git commit with `prepare.mjs`. The prepared
contract binds every submission file, its module build order, generated Lean
files and a SHA-256 inventory of the maintainer's approved libraries. The
libraries JSON maps absolute worker filenames to SHA-256 hashes. Review the
library source revisions and cache provenance before preparing that inventory.

```sh
node verifier/standard/prepare.mjs \
  --checkout /srv/tracker --head FULL_HEAD_SHA \
  --repository owner/repository --id submission-id \
  --libraries /srv/libraries.json --out /srv/prepared
python3 verifier/standard/replay.py \
  --profile /srv/profile.json --prepared /srv/prepared --work /srv/run
```

The operator-owned profile supplies `palomar`, `source_toolchain`,
`judge_toolchain`, `exporter`, `submission` and `libraries` paths. `submission`
points to the prepared source directory. Use the repository's pinned Lean
4.34.1 compiler and Mathlib dependencies, the Lean 4.35.0-rc2 judge bundle and
Palomar commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.

Run as an unprivileged user on a disposable Linux worker with working
bubblewrap, delegated cgroups and seccomp. The controller needs write access to
the library directories for confinement-probe cleanup. Every proof phase sees
these libraries through read-only sandbox mounts. Library files are authenticated
before and after checking. The candidate sees only its declared source,
libraries, compiler and writable build directories. The canonical challenge is
exported before candidate execution. The judge receives the frozen exports and
protected configuration.

A successful run retains checker controls, compiler logs, proof exports, source
bindings and its acceptance time. Archive the full run and library inventory.
Publish the receipt, contract, controls, tool hashes, statements and logs under
`verifier/standard/receipts/<run-id>/`, with a checksum collection. Large exports
and the library inventory remain in the retained run; their hashes bind them to
the published receipt. Register the reviewed collection in
`verifier/pr-admissions.json` with replay profile `standard-submission-v1`.

Only an accepted check of the exact source and PR head permits admission.
