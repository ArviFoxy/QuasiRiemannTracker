# Parked exploration (not part of the submission)

The user decided (2026-10-26) to submit at the built bound 437037/500000 and not to pursue further improvements before the
formalization of `nf_step3` is complete.

- `flow_k92x.json`: the mixed flow continued past s = 0.062 to s = 0.070 (same settings as `flow_k92.json`, MH = 1e-4;
  it reaches the HIGH-parent floor B = 22/23 at s ≈ 0.0685 and is infeasible at 0.0705). A 10-piece exact family
  (sig = …, 0.0595, 0.0640, 0.0680) passes the exact step checks (`mixed_family.check`).
- Pricing by the return agent: moving the count face C from s = 0.0595 to s = 0.062 gives θ* = 0.8740679 (−4.9e-6 against
  0.8740728); further positions were being priced when the session was interrupted.
- `price_ext.py`: the return agent's pricing helper for the extended flow.

Resume after the submission if desired: a new piece needs `QRH_FLOW3=parked/flow_k92x.json`, `QRH_SIG3=…`,
`QRH_CAPRAMP`, the generator's chain/junction modes generalized to a ramped last piece, and `FinalReturn` rebuilt with the
new C (return_cut/REGENERATE.md).
