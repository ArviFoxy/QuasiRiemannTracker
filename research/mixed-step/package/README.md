# Packaging the mixed-step proof as a new submission

The mixed-step proof ships as a **new submission**, `submissions/arvi-mixed-step-20261026`. It is not an
update of PR 76.

**Upstream state** (`upstream/main`, 2026-10-26):
- merged: Collet (`hailey-collet-1252270103`), the baseline (`openai-baseline`), Sil's fourth-power
  package (`sil-fourth-power-20261025`, PR 74) and our `arvi-repeated-marks-20261024` (PR 73);
- not merged: PR 76 (`arvi-repeated-marks-on-sil-face-20261025`).

So the new package depends only on Collet and the baseline, and **vendors** from PR 76 whatever is in
its import closure. That is:
- Sil's start face with the weakened hypothesis: PR 76's `FourthPower/`, 421 modules, with
  Apache-2.0 notices kept;
- the face-family machinery (`Faceless/`), `Finite/`, `Gain/`, `Graph/{Start,StartFace,NaturalCap}`;
- the `_rm` fork modules that the mixed fork builds on.

PR 76's own chain and return are not in the closure and are not copied.

**Layout.** One Lean package, `Submissions.arvi_mixed_step_20261026`:
- `ReturnD/`, `FinalReturn/`: the final return, θ = 34971/40000. Built by the return agent
  (`../return_cut/`).
- Vendored PR 76 modules, at their PR 76 relative paths.
- The development tree `Submissions.arvi_mixed_step` (prefix renamed):
  - the certificates: `Fan/`, `Family/`, `Finite/{SourceValid3,HighGate3}`;
  - the chain: `Graph/{Chain3,MixedChain,Endpoint3}`;
  - the step: `Ledger/`, `Transfer/`, `Collision/`, `Residual/`, `ForkMx/` (the `_mx` fork, kept apart
    from PR 76's `Fork/` to avoid path clashes), `Downstream/`, `Source/NFStep3`.
- `Candidate/Main.lean`: `bound` at `(34971/40000 : ℝ) < s.re`.

**Script.** `package_mixed.py LAKE TARGET_DIR ROOTS…` computes the import closure over the three
trees, copies each module to the target prefix, rewrites its imports, and reports path clashes and
stale files.

A test without the pending modules gives a closure of 620 modules: 438 vendored from PR 76
(421 `FourthPower`), 172 return modules and 10 of ours.
