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
- [x] Faces C and P: the exact values in `faces_k92_ramp.json` (caps 111411/1310720, 527267/6553600) match
      `FinalReturn/ReturnConstants` and the dev `Graph/MixedChain` (`faceC_cap`, `faceP_cap`).
- [x] Return: θ = 437037/500000 (0.874074), θ* = 0.8740728, h = 403/500, Lemma W windows, 33 rows, 14 windows;
      161 modules ALL-OK, axioms clean (return agent, 2026-10-26).
- [x] Piece 7 with the cap ramp `3/40 + y/100` (`Certs3c`) built; `mixed_chain_sources` axioms clean.
- [x] Fan: 46 steps. Family: 8 pieces, 2^16 grid steps each (piece 7 with the cap ramp). Junctions: 8. All built;
      packaged closure up to `Graph/Endpoint3` ALL-OK, `beta_of_step3 : NFStep3 → β ≤ 437037/500000` axioms clean.

**Packaging**
- [ ] Package `Submissions.arvi_mixed_step_20261026` contains only our modules. The dependency
      `arvi-repeated-marks-on-sil-face-20261025` is imported unchanged, and no PR 76 return module is in
      the closure (`package_mixed.py` checks this).
- [x] Every forked or adapted file keeps the original copyright line verbatim, followed by
      `Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.` and the fork note (`fork/add_mod_line.py`; 102 files in the
      development tree; `package/make_submission.py` refuses a package that has a derived file without it). Every new
      file has an origin note and, as in PR 76, no copyright line of its own (authorship: `metadata.json`).
- [x] `metadata.json` passes upstream main's `validateSubmissionMetadata` (re-checked at 0.874074); QRH-Decimal 0.874074 is
      the exact value of 437037/500000.
- [ ] Canonical wrapper (`verifier/challenge.mjs`) at 437037/500000 compiles against `Candidate.bound`.
- [ ] Full build with the pinned toolchain; export size and time measured, within the hosted budget.
- [ ] The branch is based on upstream main (PR 76 is merged, and its sources are byte-identical to the local copy); all changed files are under
      `submissions/arvi-mixed-step-20261026/`.
- [ ] Commits authored by Arvi <arvi.pub@gmail.com> with the Claude co-author line; no session links
      anywhere.
