# Independent Docker proof replay

These protected maintainer tools verify the classical bound **1/1** and the
single-prime bound **29/33**. Each profile fixes the PR head, exact target types,
source hashes, dependency artifacts, compiler, exporter and checker tools.

The classical profile checks all-Dirichlet and Riemann-zeta nonvanishing in
`Re(s) > 1`. The single-prime profile checks all-Dirichlet, zeta and finite-order
Eisenstein Hecke nonvanishing in `Re(s) > 29/33`, with their principal-pole
exceptions. The contributor's Appendix D.3 theorem is compiled with its source
package; the independent exported targets are the three endpoint theorems.

## Verification order

1. Authenticate every tool and dependency artifact against the protected pins.
2. Run isolation controls and the official positive, wrong-statement and
   ill-typed-proof checker controls.
3. Compile the maintainer's literal challenge against the canonical library and
   freeze its exported statement before reading candidate source.
4. Copy source bytes from the pinned checkout. Compile the changed modules in
   an isolated output tree using authenticated dependency artifacts.
5. Export the solution into a supervisor-owned file. Comparator checks its
   statements and referenced definitions against the frozen challenge; Lean,
   NanoDa and con-ron check the exported proof closures. The permitted axioms are
   `Classical.choice`, `Quot.sound` and `propext`.
6. Reauthenticate frozen inputs and write the receipt outside candidate mounts.

Docker runs with a read-only root, no network, an unprivileged user, dropped
capabilities, default seccomp, explicit bind mounts and bounded resources.
The trusted `setpriv --no-new-privs` launcher applies NoNewPrivs before execution.
The official Comparator command uses `--inadvisably-no-sandbox` because Docker
provides the process confinement. Its original warning is retained in the logs.

The classical library contains 3,617 independently source-compiled modules.
The single-prime canonical library combines this run's compiled dependencies
with OAI objects matching the previously approved library manifest. Candidate
foundations match approved source/build hashes; additional candidate dependency
cache objects are pinned and their exported proof dependencies are kernel
checked. The provenance manifests identify each module's origin. Compiler and
checker binaries match the existing protected Cycle25 tool pins.

## Reproduction

Use a protected checkout and operator-owned paths as shown in
`profile.example.json`. Prepare Lean 4.34.1, the pinned exporter, the official
Lean 4.35.0-rc2 checker bundle, and Palomar commit
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. The JSON profiles contain exact tool
and dependency inventories. `build-library.py` compiles an authenticated module
import graph in a Docker container with `/source`, `/controller`, `/build` and
`/logs` mounts. Source hashes appear in the provenance files; upstream commits are pinned in
`../cycle25/pins.json` and the submitted dependency locks.

Run fresh controls with `checker-controls.py --runtime PATH --work NEW_PATH`.
The runtime contains the judge toolchain, Palomar checkout and
`docker-image-id.txt`. Its result must match the protected profile before proof
execution. Then run:

```sh
python3 verifier/docker/replay.py --pins verifier/docker/classical-pins.json \
  --profile /srv/qrh/operator-profile.json --work /srv/qrh/new-replay
```

Use `single-prime-pins.json` for the alternative bound. Preserve the complete
private workspace, including the frozen exports, for subsequent checking.
`publish.py` collects exact logs, statement configuration, controls and the
receipt for review. Export and compiled-object hashes remain in the receipt and
pins; public proof sources provide the reproduction inputs.

## Metadata updates

`recheck.py` supports a new PR head with identical proof, target and tool pins.
It authenticates the original source replay and exports, compares the proof
bytes with the new Git commit, and reruns Comparator and all three kernels.
The new receipt retains the original source-build head and receipt alongside
the newly checked head. Both generations of checker logs are published.

The admission catalogue binds each result ID, exact bound and PR head to its
protected collection. A framework-verified catalogue entry also requires its
proof bytes to match that admission. Keep published drivers, pins and evidence
immutable; introduce a new versioned profile for a later implementation change.
