# Packaging the mixed-step proof as a new submission

The mixed-step proof ships as a **new submission**, `submissions/arvi-mixed-step-20261026`. It is not an
update of PR 76.

**Dependencies.** The new package builds on top of PR 76 (`arvi-repeated-marks-on-sil-face-20261025`,
ours) and imports its modules unchanged, so nothing is vendored:
- Sil's start face with the weakened hypothesis (`FourthPower/`);
- the face-family machinery (`Faceless/`), `Finite/`, `Gain/`, `Graph/{Start,StartFace,NaturalCap}`;
- the `_rm` fork that the mixed fork builds on.

Collet's tree and the baseline are dependencies as well. PR 76's own return (`ReturnD/`,
`FinalReturn/`) must stay out of the import closure, because the new return reuses its namespaces. The
script checks this.

**Layout.** One Lean package, `Submissions.arvi_mixed_step_20261026`:
- `ReturnD/`, `FinalReturn/`: the final return, θ = 34971/40000. Built by the return agent
  (`../return_cut/`).
- The development tree `Submissions.arvi_mixed_step` (prefix renamed):
  - the certificates: `Fan/`, `Family/`, `Finite/{SourceValid3,HighGate3}`;
  - the chain: `Graph/{Chain3,MixedChain,Endpoint3}`;
  - the step: `Ledger/`, `Transfer/`, `Collision/`, `Residual/`, `ForkMx/` (the `_mx` fork), `Downstream/`,
    `Source/NFStep3`.
- `Candidate/Main.lean`: `bound` at `(34971/40000 : ℝ) < s.re`.
- `metadata.json` dependencies: `arvi-repeated-marks-on-sil-face-20261025`, `hailey-collet-1252270103`,
  `openai-baseline`.

**Branch.** The new submission's branch stacks on PR 76's submission branch, so its diff is only
`submissions/arvi-mixed-step-20261026`.

**Script.** `package_mixed.py LAKE TARGET_DIR ROOTS…` computes the import closure over our two trees,
copies each module to the target prefix, rewrites its imports, checks that PR 76's return stays out, and
reports path clashes and stale files.
