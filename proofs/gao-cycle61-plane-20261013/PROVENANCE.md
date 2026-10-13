# Authorship and source provenance

**Verification status: LOCAL_FULL_PROOF_VERIFIED_HOSTED_ADMISSION_PENDING.** This describes the exact staged source and completed component checks, with completed local proof verification and tracker admission still pending.

Zhongpai Gao, with AI assistance, prepared the present parameter refinement, source integration and concise note. AI assistance contributed to the numerical search, exact rational derivations, Lean transformations and verification engineering. This credits the new refinement without assigning the inherited analytic construction to its new author.

The complete analytic source is adapted from Hailey Collet's Cycle61 submission, [PR #42](https://github.com/GTimG/QuasiRiemannTracker/pull/42), frozen at `fb6d4fd11aeaff0b37dd96bad3b274ce28a5c08b`. Its target is `874861/1000000`; the present target is `4374299/5000000`. The inherited physical reconstruction, common probe, uniform main/error estimates and zero-exclusion assembly remain credited to that source and its predecessors. The copied `UPSTREAM_PROVENANCE.md` and `UPSTREAM_NOTICE.md` preserve the upstream author's historical attribution verbatim.

The new source changes are:

- Coupled LOW/HIGH cutoff and reserve parameters: `q0 = 67/100`, `Ka = 67/48`, `rho0 = 214/549`, `lambda = 16281/4106`, `B0 = 2025/2053` and `B = B0 − 1/100000`.
- Linked endpoint values for `theta`, `c`, `ell`, `x`, `y` and `kappaStar`, with the original `h`, mesh width, cell range and alpha retained.
- Exact reserve bounds carried through explicit semantic owners in the actual source-support, mesh, main and error consumers.
- New global rational quadratic certificates at the top, old junction and half row, retaining the downstream theorem names and endpoint/feedback interfaces.
- Canonical final theorem specializations at the new exact boundary.

The frozen candidate comprises all 194 Lean files and changes 64 relative to the submitted Cycle61 snapshot. Source comments, mathematical namespaces, licenses and original module provenance markers are retained. The markers identify original pre-adaptation material; current file identities are given by `source-pin.json` and the publication manifest.

Retained mathematical sources include:

- OpenAI/math, `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, including all 2,923 protected OAI source files used by the Cycle61 closure: original seven-eighths initialization, Hecke/Dirichlet definitions and analytic/arithmetic framework.
- Akash Levy's weighted-numerator source, `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, [PR #6](https://github.com/GTimG/QuasiRiemannTracker/pull/6), adapted through Cycle25.
- Hailey Collet's earlier Cycle25 and related developments, including [PR #8](https://github.com/GTimG/QuasiRiemannTracker/pull/8) and [PR #9](https://github.com/GTimG/QuasiRiemannTracker/pull/9), with the latter pinned at `58344dfdbe756cf2f743da1908ffe0582418cf5b` in the inherited attribution.
- Gao's earlier local refinement, selected source `ca182b70ac2aee2d053d679b4ddf1233883f9eef`, [PR #15](https://github.com/GTimG/QuasiRiemannTracker/pull/15).
- nielstron's [PR #26](https://github.com/GTimG/QuasiRiemannTracker/pull/26), `16ce30342471344c2b2f0d383388e6f9acb9bccf`, credited by Cycle61 for the dependency-ordered bundling approach.

The package retains Apache-2.0 and all supplied predecessor notices and licenses. Mathlib and other dependencies, Lean and independent checker tools retain their own authorship and licenses; their binaries are not redistributed here.
