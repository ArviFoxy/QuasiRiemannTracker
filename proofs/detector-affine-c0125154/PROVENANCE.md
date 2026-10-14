# Authorship and source attribution

**AI disclosure:** DaysSky with Claude assistance. DaysSky directed this work. The mathematical change, the Lean formalization and the exact certificates were developed with Claude assistance. Model review is not independent kernel verification.

## What is reused

Everything comes from the Cycle61 submission [`cycle61-c0125139`](../cycle61-c0125139/README.md) by Hailey Collet, together with the sources that submission credits:

* OpenAI/math;
* Akash Levy's weighted-numerator proof;
* the earlier Cycle25 QRH work;
* Zhongpai Gao's local refinement.

See [`licenses/cycle61-PROVENANCE.md`](licenses/cycle61-PROVENANCE.md). The key ingredient used here is Cycle61's initial affine moment (Theorem 2.2, `Cycle61Moment.InitialAffineAt`) and its generic paid main and error families. This submission applies them to the detector's dictionary characters.

## What is new

New modules under `submissions/detector-affine-c0125154/src/Candidate/Affine/`:

| module | content |
|---|---|
| `Arith.lean` | closed forms for the new count; the combination lemma `affine_count_bound` |
| `Certificates.lean` | exact Bernstein certificates on the region |
| `Region.lean` | region consequences of the certificates; `region_compare` |
| `Mesh.lean` | an early copy of Cycle61's chosen geometry mesh (`detectorMesh`) |
| `Count.lean` | `AffineMarkedMoment`; per-fiber affine count; `count_from_raw_moments_both` |
| `Balanced.lean` | `cutoffA`; balanced count for both the old and the new count |
| `SourceCount.lean` | source count at `cutoffA`; `SourceMomentsAtA` |
| `Moments.lean` | `DetectorAffineInput`; per-character source moments |
| `Masked.lean` | monotonicity of `countingR`; masked amplitude class count |
| `Supply.lean` | proof of `DetectorAffineInput` from Cycle61's generic affine machinery |

Changed Cycle61 bundles in `Bundles/`:

| bundle | change |
|---|---|
| B000 | endpoint constants |
| B003 | `CountParameters.affine` |
| B021 | regenerated row certificates; degree-(2,4) basis |
| B022 | region-aware `countingR` (`countingR0` is the old one); row lemmas |
| B023 | `SourceMomentBound` with the affine field; `t_le`; ε ≤ 1/10000 |
| B024, B025 | per-character heights; `commonMesh` includes `detectorMesh` |
| B043 | per-character finite numerator inputs |
| B060 | recomputed endpoint constants |
| B070 | `countingR0` |
| B074, B075 | batches at `cutoffA`; affine source count |
| B076 | masked count through `masked_amplitude_class_count_A` |
| B078 | per-character fixed numerator; `DetectorAffineInput` threaded through the final theorems |
| B192 | supplies `actual_detector_affine_input` |
| B167, B176 | Split, unchanged, for the tracker's 600-second per-module replay limit:<ul><li>`B167` → `B167Part1`–`4`, one per original source section; section 1 is further split at declaration boundaries into `B167Part1A`–`1D`</li><li>`B176` → `B176Part1`–`4`; section 2 is further split into `B176Part2A`–`2C`</li></ul>Every declaration, statement and proof is Cycle61's, in the original order. The pieces repeat their section's namespace, `open` and `variable` preamble. A section's local instance is declared once and re-enabled with `attribute [local instance]`. `B167.lean`, `B176.lean`, `B167Part1.lean` and `B176Part2.lean` are now thin modules importing their last piece. |
| Main.lean | the bound |

Constants that depend on the endpoint were recomputed by `scripts/patch_consts.py`. `arithmetic/rational-check.py` rechecks them.
