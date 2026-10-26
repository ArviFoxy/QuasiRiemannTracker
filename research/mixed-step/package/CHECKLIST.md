# Before opening the PR: facts and checks to verify

The metadata and PR body state these. Each must be true of the final package.

**Proof**
- [ ] `nf_step3 : NFStep3` proved, with no `sorry` or axiom. `#print axioms Candidate.bound` gives only
      propext, Classical.choice, Quot.sound.
- [ ] Collisions (p²m columns) and seed suppliers handled in Lean, not assumed. The transfer agent is
      working on both.
- [ ] Collet's MAIN-layer objects reused unchanged (Phase 0: the stop set is clean). Confirm in the final
      import graph.

**Numbers**
- [x] Faces C and P: the exact values in `faces_k92.json` match `FinalReturn/ReturnConstants`.
- [x] Return: θ = 34971/40000, θ* = 0.8742701, 67 rows, 25 windows (return agent's report).
- [ ] Fan: 46 steps. Family: 8 pieces, 2^16 grid steps each. Junctions: 8. All built.

**Packaging**
- [ ] Package `Submissions.arvi_mixed_step_20261026` contains only our modules. The dependency
      `arvi-repeated-marks-on-sil-face-20261025` is imported unchanged, and no PR 76 return module is in
      the closure (`package_mixed.py` checks this).
- [ ] Every forked file keeps the original copyright line verbatim, plus a fork note. Every new file has
      an origin note.
- [ ] `metadata.json` passes `verifier/submission-metadata.mjs` (it passes now). The PR declaration
      parses (it parses now).
- [ ] Canonical wrapper (`verifier/challenge.mjs`) at 34971/40000 compiles against `Candidate.bound`.
- [ ] Full build with the pinned toolchain; export size and time measured, within the hosted budget.
- [ ] The branch is based on upstream main (PR 76 is merged, and its sources are byte-identical to the local copy); all changed files are under
      `submissions/arvi-mixed-step-20261026/`.
- [ ] Commits authored by Arvi <arvi.pub@gmail.com> with the Claude co-author line; no session links
      anywhere.
