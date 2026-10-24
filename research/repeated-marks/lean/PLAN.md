# Lean formalization plan (repeated marks + global physical face)

Target: a tracker submission whose `Candidate.bound` states nonvanishing for
`Re s > 8747289/10^7`, checked by Lean, NanoDa and con-ron.

## Already formalized (Mathlib only, compile standalone)

| file | content |
|---|---|
| `LemmaC.lean` | Lemma C (common-width payment) for arbitrary facet families |
| `RepeatedGain.lean` | per-class thresholds and branches; `f_0 = ν S`; facet linearity; coefficient bounds `A,B ≥ 0`, `B ≤ C_max`; `G_K = inf_p f_p`; Lemma C for `G_K` (`gainK_payment`); width monotonicity; homogeneity |
| `Bernstein2.lean` | bicubic Bernstein positivity on boxes; computable bisection-tree checker `checkBox` with soundness `checkBox_sound` (`decide +kernel`) |
| `FiberClass.lean` | `fiber_exponent_class`, the analytic core of Lemma B_K: per-class cutoff, `K` repeated slots; generalizes Collet's `fiber_exponent` |

## Structure of Collet's formalization (two read-only maps)

**The gain is hard-coded.** `High.gain` (`Record1252270103Source/High/Selection.lean`) appears in
statements from `feedback_fiber_count` up to the join
`GlobalPhysicalAnnularCofactor`. Above the join everything is typed by `ActualGaps` /
`selectedGain` (`Core/PhysicalReserve.lean`), up to `nf_truncated`.

**The step theorem is bound to `SourceValid`.** `NFStep` (`Graph/GraphContract.lean`) takes
`SourceValid` and is hard-wired to `finalK = 11243277/2500000`. About 36
positional projections of `SourceValid` appear across ~15 files.

**The endpoint runs two stages.** The intermediate stage (seed graph, θ_I = 0.8747759)
feeds the final stage. Lewko (PR #70) reused the seed graph and intermediate stage
through `final_natural_cap seed_step`, then copied the final return (`Record1252270103Return`, 430 files) and its
finite certificates (265 files) under a new namespace.

## Work list

1. **Source step fork** (~75 files, mostly retyping `High.gain` → `gainK`,
   `ActualGaps` → `ActualGaps2`). New pieces:
   - `inverse_fiber_count` with a `K`-fold selection, through
     `overlapping_annular_inverse_marked_energy` (already proved; accepts
     overlapping lists);
   - per-bin cutoffs: `binCutoff` uses the bin's `p`; `MaxWeighted`,
     `ActualBinSourceTau` and `LocalWitnesses` supply one witness per cutoff
     (template: PR #67 `GenericCountAssembly`);
   - `feedback_fiber_count` via `fiber_exponent_class`;
   - scalar side: `gainAt_common_reserve` → `gainK_payment` (reserve 0; the
     `/12` term is discarded downstream anyway); `gainAt_weighted_width_mono` →
     `gainK_width_mono`; root completion through the coefficient bound `B ≤ C_max`.
2. **`SourceValid2` and its soundness.** It replaces the six HIGH facet gates with,
   for each width endpoint and each branch, a `checkBox` certificate for the
   bidegree-(3,3) gate numerator on `[q,3/4] × [0,1/2]`. Then `NFStep2`.
3. **The 59-node graph.** Generated `Source` data, `decide +kernel` node
   certificates, and the induction.
4. **Return fork** (as Lewko did). Lemma D in
   `PhysicalDirect/{Input,Fourier,Hybrid,Geometry}`:
   - global face `⟨B,Λ,0,B,0,cap⟩`;
   - clipped capacity for every shift;
   - damping via `ClippedCapacityDamping.small_shift_reserve`.

   Drop `small_plain_shortening`, `shift_bound`, `large_shift_reserve`, the
   plain/width window fields and `freeShift` from `PhysicalSchedule`. Change
   `cap` to 9/200 (also in `Conductor.lean` and `Finite/ReturnConstants.lean`),
   the C count cap 11/250 to 13/250 (`ReturnFormulas.branchCap`), and widen
   `Geometry.Bounds` (`h < 0.81`, `y < 0.47`, `ℓ < 0.168`; every use is loose).
   Regenerate the row, admission and cover certificates from `cert_return.py`.
5. **Endpoint and `Candidate.bound`.**
