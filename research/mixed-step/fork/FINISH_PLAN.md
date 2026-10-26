# Finish plan: from "conditional on NFStep3" to a sorry-free `Candidate.bound` (2026-10-26, 10:30 UTC)

**Goal.** A complete Lean proof of `Candidate.bound` at 437037/500000 with axioms `[propext, Classical.choice, Quot.sound]`.
Everything is built except one theorem, `QRH.MixedStep.Graph.NFStep3` (Graph/Chain3.lean): the mixed source step
`SourceValid3 n low h → SourceValid3X n low → ParentGood low → NFAccounting n → P low → P h → P n`.

**Built and kernel-checked (do not touch):**
- the return `Submissions/arvi_mixed_step_20261026/{ReturnD,FinalReturn}` (θ = 437037/500000, h = 403/500, Lemma W),
- the certificates and the chain: `Fan/`, `Family/`, `Graph/{Chain3,Chain3c,MixedChain,Endpoint3}`
  (`beta_of_step3 : NFStep3 → β ≤ theta`, axioms clean),
- the ledger (`Ledger/`), transfer (`Transfer/`, `Residual/`, `Collision/` partly), the forks `ForkMx/` (F3, F4, F6 green),
  `Downstream/` contracts, `Source/NFPhysical3`, `Source/NFStep3` (reduces `NFStep3` to the items below).

**What `nf_step3` still needs** (`Source/NFStep3.lean`, `nf_step3_of`):

| # | item | file(s) | status |
|---|------|---------|--------|
| A | F5 bridge: `RegularPointSupplier_mx`, `regular_supplier_of_points_mx : … → RegularJointSupplier_mx` | `ForkMx/…` closure modules 47–51 (+ check 45, 46) | modules 11, 12, 31–37, 45, 46 written; 47–51 missing |
| B | `regular_supplier3` (RegularSupplier3Statement) | `ForkMx/…/High/GlobalPhysicalRegularSuppliers`, `Downstream/Supplier3` | per-node pieces green; waits on A |
| C | collision families: label-level collision energy bound with extended columns (option (k)), shortenPlains = initialInput of shortened data, extended-column energy equality | `Collision/`, `Residual/`, new files | steps 1–2 (tuple/element level) and `CollTwist` done; ideal-level and assembly open; **three design points open** (HANDOFF "## Collision families") |
| D | the full transfer contract replacing `PlainTransfer` (`Downstream/Families.lean:378`), `pieces_transfer_coll` | `Downstream/Families.lean` | open; depends on C |
| E | `RegularJointSupplierCol3` for collision families | `Downstream/Contract3`, `Supplier3` | open; depends on A, C |
| F | `balanced_of_regular3` (two `sorry`s at Downstream/Balanced3.lean:220–221) | `Downstream/Balanced3.lean` | open; depends on D, E |
| G | `nf_step3` closing and `#print axioms` | `Source/NFStep3.lean` | depends on B, F |

**Rules (all agents).**
- No `sorry`, `admit`, `axiom`, `native_decide`. `#print axioms` on every top theorem.
- Compile one module at a time with `/home/user/lean-env/mk_mixed.sh <path under arvi_mixed_step/, no .lean>`;
  at most ONE Lean process per agent (memory: 15 GB total). Dependency closure builds:
  `QRH_PKG=Submissions.arvi_mixed_step python3 research/mixed-step/build/build_roots.py JOBS LOGDIR ROOT…`.
- Only edit your own files. Do not touch Collet's tree, the baseline, PR 76's package, or other agents' files; if you need a
  change there, write the request in HANDOFF.md under your section and tell the coordinator.
- Forks keep Collet's copyright line verbatim first, then the PR 76 note (if any), then the fork note
  (HANDOFF "## Conventions"; `fork/fix_headers.py`).
- Do not commit; the coordinator commits. Record tops (exact statements) in HANDOFF.md under your own section.
- No claims of success without a compile: report only what `mk_mixed.sh` accepted.
- If something is mathematically false or a hypothesis cannot be discharged, STOP and report the precise obstruction
  (statement, which gate/inequality fails, numbers) to the coordinator. Do not weaken a statement silently.
- Commit nothing with session links; do not mention model names in files.

**Documents.** `L45_DESIGN.md` (design, §7 collisions), `LEDGER_INTERFACE.md`, `LEAN_NOTES.md`, `fork/HANDOFF.md` (exact
statements by owner: F4 tops, F3/F5 lead tops, F6 twins, N6, Collision families, N7), `fork/closure_mx.tsv`.
