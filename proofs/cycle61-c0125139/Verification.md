# Verification and reproduction

The unconditional endpoint and all four comparison exports have completed whole-file Lean 4.34.1 development compilation. Their reported axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The frozen original closure contains 3,695 modules: 595 Cycle61, 161 Cycle25, 13 LocalMoment, 3 ZetaZeroFree and 2,923 protected OpenAI modules. The complete clean rebuild passed on 13 October 2026: all 3,695 modules exited successfully, with no submitted objects reused and no frozen sources changed. Third-party dependencies retain the protected revisions and compatibility patches.

The [complete build receipt](verification/clean-source-build.json) records every module's exit status and output hashes. Its SHA256 is `ee3bbf12a683ecf267e6e035fb038764f32231534c22050f1a7ca3f11f5bd862`. Every source record in the successful build inventory matches [the source manifest](source-manifest.json); that manifest retains the earlier freeze inventory identifier as provenance. The successful build inventory is `890539fce5c79415d14eacf63a46f388da8a9a0b2d99447ab060eda3a47960f6`.

The build used Lean 4.34.1, compiler SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, four concurrent single-threaded compiler processes and a 16 GiB memory allowance per process. An earlier attempt stopped at an 8 GiB allowance; the successful run rebuilt the full unchanged source closure. The [final export axiom log](verification/Cycle61.Verification.log) reports only the three standard axioms for each of the four comparison exports.

The final claims are:

- `Cycle61.FinalAssembly.beta_le_rational`: the unconditional rational bound.
- `Cycle61Verification.allDirichlet`: every nonzero modulus and complex character, strict boundary, principal pole excluded.
- `Cycle61Verification.zeta`: ordinary off-pole zeta nonvanishing.
- `Cycle61Verification.allHecke`: the exact `HeckeFamily.Character` and `LFunction` with its residue-one pole exception.
- `Cycle61Verification.zetaTotal`: a separate statement using Mathlib's total-function convention at the pole.

The submission wrapper `Candidate.bound` exposes the literal all-Dirichlet theorem expected by the tracker. Bundling remaps imports, isolates module-local scopes and records necessary name qualifications and token spacing. The map also records a theorem-local heartbeat allowance of 40,000 for `actual_main_low_all_height_splice`, whose statement and proof body remain unchanged. Protected replay time limits are unchanged. The transformed package was checked in the separate replay described below.

The original source passed the literal-statement Comparator and all three independent kernels on 13 October 2026. The checked contracts are `Cycle61Verification.allDirichlet`, `zeta` and `allHecke`, including their full exported proof closures. `zetaTotal` is the separate fourth development export. The verifier freshly compiled the 306 protected modules needed by the challenge, ran positive and negative controls, and checked unchanged source, tool and dependency inputs through completion. Both the judge and whole launcher exited 0; the final external dependency seals are byte-identical.

The [original replay receipt](verification/original-three-contracts.json) has SHA256 `c73351b1215497c446203eeea24a07c53265d42ece8fcb36ec709add89ff1b62`. The [judge transcript](verification/original-judge.log) records acceptance by con-ron, NanoDa and Lean plus the Comparator success marker. [Replay bindings](verification/original-replay-bindings.json) connect that result to the clean build, exact exports and final seals. The source compiler was Lean 4.34.1; the independent judge toolchain was 4.35.0-rc2.

The transformed Candidate completed a separate fresh compilation of all 194 modules and passed the canonical all-Dirichlet Comparator and Lean/NanoDa/con-ron checks. Both its judge and whole launcher exited 0. The locally checked source commit is `53aa723f5b406403c784808667215d5dc3af1899`. [The Candidate receipt](verification/local-candidate.json), [whole-launcher receipt](verification/local-candidate-launcher.json) and [judge transcript](verification/local-candidate-judge.log) preserve the exact source, tool, control and exit-status evidence.

Both local replays used the recorded native judge adapter because this host refuses the standard nested namespace setup. The trusted Comparator, pinned checker inputs and official per-kernel sandboxes were retained; the adapter and resource-policy differences are recorded in the receipts. These are explicitly adapted local checks. Protected exact-head acceptance requires a separate tracker run on the submitted commit. Consult the PR for its current status.

The receipts identify the original and transformed source hashes, dependency pins, whole-process exit statuses, checker versions and locally checked commit; the packaging directory supplies the source map. Every later submitted commit requires a new exact-head tracker check.
