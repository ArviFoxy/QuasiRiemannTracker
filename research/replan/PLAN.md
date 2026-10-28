# Replan after the density-split records (2026-10-28)

Reports behind every number here (this folder): `pr83.md` (PR 83's step engine and return), `pr84_86.md`
(PRs 84–86, chain model), `lemmaW.md` (exact return toolchain on PR 86, all levers priced), `floor.md`
(the density floor), `process.md` (new upstream rules). Scripts: `scripts/` (`$SCRATCH` = the analysis
folder they ran in; `lemmaW/tc` is the exact return toolchain, validated against PR 86's Lean).

## 1. Where things stand

- **Record:** PR 86 (Jacob Sussman), 4369779/5000000 = **0.8739558**, merged 2026-10-28.
  Lineage: Sil's fourth-power face (0.8746935) → our PR 76 (0.8746075) → Sil's PR 83 density split
  (0.873995, depends on PR 76) → PR 84 (0.873985) → PR 85 (0.873981); PR 86 depends on PR 83 only.
- **Open upstream PRs:** #52 (old WIP) and #72 (0.874771). #75/#77/#78 closed unmerged.
- **Bar (Arvi):** at least 2e-5 below the record, i.e. **θ ≤ 0.8739358**.

## 2. Findings

| item | value | source |
|---|---|---|
| Our mixed step (437037/500000 = 0.874074) | **superseded**: PR 83's native step has the same barrier `L* = 18B/7` (= `6qB/(1+q)` at q = 3/4), handles p² columns, and its chain alone gives 0.874024 | `pr83.md` §2, §4 |
| The binding link | the return: edge `newTop` (d = h), p = 1/2, δ ≈ 0.4415, count C branch; PR 86 is the least 7-digit θ for its faces | `lemmaW.md` §1 |
| Lemma W | **0** (PR 83's constants — window caps = face caps, mMinus, sMinus — already are its relaxations) | `lemmaW.md` §2 |
| Cheap tuning (role split count = step 46 / physical = step 38, finer chain, c, h, caps) | ≤ 2e-6 in total (role split −9e-7) | `lemmaW.md` §3, §5 |
| Density floor q ≥ 13/20 (Collet's `33/40 ≤ a`) | a domain choice; Collet's tree already proves the needed lemma at `a ≥ 4/5` (`Record1252270103Bootstrap/PR67Source/Cycle63/Density/NaturalEndpoint:94`); nothing else binds before q = 0.60 | `floor.md` |
| Floor 3/5 + chain to step ≈ 73 (L ≈ 2.2065) + role split (count 73 / physical 38) | **0.8739463 (−9.5e-6)**; continuum limit 0.873945 | `lemmaW.md` §4, `floor.md` §5 |
| **Still missing for the bar** | **1.05e-5** | |

What would close the remaining 1.05e-5 (on top of floor + split; priced exactly by modified formulas,
none provable today, `lemmaW.md` §4.3):

| lever | needed |
|---|---|
| density-step slope s0 (source side) | −5.3 % (continuum) / −6 % (ΔL = 0.005); only with the floor at ≤ 0.60 |
| return exponent E | −4.9e-5 |
| count R at the binding point | −8.1e-5 (0.013 %) |
| capacity C_N at the new edges | +4.4e-4 (0.9 %) |
| inverse slot cost c_I = 2 | → 1.9941 (−0.3 %) |
| long-line slope k_L = 5/6 | → 0.8313 (−0.2 %) |
| class fourth-moment saving η4 | 2.4e-4 |
| selected slots save δpC instead of δpC/2 | −3.0e-4 (far beyond the bar; saturates at 0.87364) |

## 3. Plan

**Stop:** the mixed-step formalization (`fork/FINISH_PLAN.md` phases 2–5, tasks MStep/L3/L4/L5/G and
phases 1–5). The branch keeps the history; nothing more goes into it.

**Track B — research (decides whether the bar is reachable; runs first, in parallel):**
- **B1, return constants.** For c_I, k_L, η4, the selected-slot saving δpC/2, C_N and the count R: the
  Lean definition, the theorem behind it, the mathematical source of the constant, and whether (a) the
  proof has slack (as the 33/40 floor had), (b) a stronger lemma is already proved somewhere in the
  upstream library, or (c) a known argument improves it. Price candidates with `scripts/lemmaW/tc`.
- **B2, source slope.** The step ODE `dB/dL = (B − 10/(15−6q))/(L − 1)`, `q = 0.999·L/(6B − L)`: trace
  every constant (Collet's zero-density exponent `ρ(ν) = 1 − 10ν/(15−6ν)`, the 6 of the packed envelope
  `H = 1 + t − 6u`, the `L − 1`, 0.999, the selection law, `J(w,q)`) to its Lean source; look for slack
  or stronger proved lemmas; test whether our mixed-step idea (fourth-power transfer of a block of live
  slots, lowering the LOW exchange rate) applies inside the density step's LOW branch. Quantify each
  with the chain model.

**Decision gate after B:** if a lever worth ≥ 1.05e-5 on top of track A is provable, implement it
(track C) together with A; otherwise report the best reachable value and stop before Lean work beyond A1.

**Track A — engineering (needed in every scenario that reaches the bar; Sonnet implements):**
- **A1 step generator.** A Python generator for density-step certificate files in PR 86's format
  (`Source/HybridK15_NN.lean`: every gate of `HybridGates` cleared to a polynomial ratio, exact-rational
  Bernstein boxes), validated by regenerating PR 86's steps; floor as a parameter.
- **A2 floor fork.** Import Collet's `a ≥ 4/5` lemma; fork PR 83's `Density/{Price, LeafHigh,
  LeafHighEnergy, Leaf, StepGates}` and `Source/HybridGates` with the floor 3/5 (~2.1k lines, ~10
  numerals, ~25-line adapter for the old certificates); steps 47–≈73 from A1.
- **A3 return.** Two-source endpoint (count face = chain end, physical face = step 38; template PR 85's
  `Return/Endpoint.lean`), re-tile window 03 (guard 8 fails below L ≈ 2.27), rows and admissions from
  our toolchain (exact match with PR 86's 32 rows and 240 admissions already shown). Own namespace
  (PR 86's `Return` re-declares PR 83's namespace, so import PR 86's `Source` only).
- **A4 package** under the new rules (`process.md`): folder `YYYY-MM-DD-arvi-<slug>` dated the UTC day
  the PR opens, Lean prefix `Submissions.arvi_<slug>`, `dependencies` by stable ids
  (`sil-density-split-20261026`, PR 86's id), metadata fields only as allowed; admission budget 12 h
  replay, 30 min per module, 24 GiB. Rewrite `mixed-step/package/make_submission.py` accordingly.

**Execution.** Analysis and research: Sonnet/Haiku agents, reports into this folder. Implementation:
one Sonnet agent per item with a written brief; one Lean process at a time; I review, integrate and
commit. No PR without Arvi's OK.

## 4. Results of track B (2026-10-28)

- **B1, return constants** (`B1_return_constants.md`): negative. Every constant (c_I, c_E, k_L, η4, the
  δpC/2 halving = capacity) is the exact output of an analytic input; each needs an open improvement
  (large-sieve saving for slot-twisted cubic-theta coefficients; sextic Möbius moment; a ‖Q‖⁴ face).
- **B2, source slope** (`B2_source_slope.md`): no slack constant (the 6 = 4 + 2 and the L − 1 are
  forced; 0.999 → 1 gives −0.8e-6). One structural lever of the right size: a **marked
  (amplitude-class) HIGH leaf** — count PR 83's HIGH rows with the library's marked count
  (`Cycle25DetectorRowCount.rowCount` / `physical_source_amplitude_count`, today used only by the
  return) instead of the unmarked ρ(ν). Floor 3/5 + role split: black box 0.8739390 (+3.2e-6 to the
  bar), supply relaxed to 0.12: 0.8739344 (passes), floor 0.55 + supply 0.12: 0.8739274. Needed from the
  first density step. Cost 4–7k hand-written + 60–200k generated lines, multi-week; completion
  estimated 35–45 %; first a 1–2 day bridge audit (report §6).
- **B3, incumbent bootstrap** (`B3_incumbent_bootstrap.md`): sound (PR 86 proves the Hecke-family
  `beta ≤ θ_rec` as an intermediate), only the native slot price κ moves: **−1.3e-6**; requires
  regenerating all density certificates; worthwhile only as an add-on.

| route | θ | vs record | vs bar |
|---|---|---|---|
| floor 3/5 + split (A only) | 0.8739463 | −9.5e-6 | +1.05e-5 |
| A + bootstrap + 0.999→1 + finer chain | ≈ 0.873943 | ≈ −1.3e-5 | ≈ +7e-6 |
| A + marked leaf (black box) + extras | ≈ 0.873935 | ≈ −2.1e-5 | ≈ −1e-6 |
| A + marked leaf, supply 0.12, floor 0.55 + extras | ≈ 0.873925 | ≈ −3.1e-5 | ≈ −1e-5 |

Only the marked HIGH leaf reaches the bar.
