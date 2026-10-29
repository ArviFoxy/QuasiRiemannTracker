Update (new head pushed to `submission-arvi-density`):

1. `Candidate.bound` now states the reduced bound `43693617 / 50000000` (= 0.87387234), matching
   `QRH-Bound: 43693617/50000000`. The first head stated `87387234 / 100000000`, which is not reduced and
   cannot match the challenge generated from the declaration.
2. The marked HIGH gates of the 129 chain steps are now certified by reflection (`Cert/Reflect.lean`): the
   cleared gate polynomial of each facet branch is computed in Lean from the step's rational data and proved
   equal to the gate once for all parameters (`eval_Fpoly`); its positivity on the box is PR 76's
   kernel-evaluated tree test `checkZ` (`decide +kernel`, six checks per step). This replaces the per-step
   `ring` identities and 3D Bernstein boxes: compiled size of a chain step 1.8 MB (was about 100 MB), about
   15 s per step.
3. Local build of the whole closure of `Candidate.bound` with Lean 4.34.1: no errors; axioms `propext`,
   `Classical.choice`, `Quot.sound`. The upstream `verifier/standard/prepare.mjs` accepts the head locally.
