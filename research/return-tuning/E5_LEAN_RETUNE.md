# E5 return retune in Lean: design 2 of the fresh-look report

Status: **done and checked** (kernel certificates pass; exact Python mirror reproduced). Lean project
`/home/user/lean-env/qrh`, toolchain 4.34.1. Sources edited there; nothing committed, nothing mirrored into
`research/lean/` (the committed mirrors `research/lean/arvi_return_tuning` and `research/lean/arvi_density/Return`
are older than this state and need a sync by whoever owns the sync).

## 1. Result

- Design: REPORT.md item 2. **theta = 43670599/50000000 = 0.87341198** (c = 6329401/50000000, N = 6329401),
  **h = 8001361/10000000** (7-digit floor of the exact floor-margin ceiling 0.800136132599...). Item 1 (fallback) was
  not needed.
- Endpoint (module `Submissions.arvi_return_tuning.Endpoint`, namespace `QRH.ArviDensity.Return.Tuning`):

      theorem beta_le_theta_of_sources
          (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
            QRH.Record1252270103Source.GlobalSource (99999/100000) (401/200) (13399/100000))
          (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
            QRH.Record1252270103Source.GlobalSource (99999/100000) (401/200) (13399/100000)) :
          HeckeZeroSupremum.beta ≤ (43670599/50000000 : ℝ)

      theorem dirichlet_of_sources (hC) (hP) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
          (hs : (43670599 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
          DirichletCharacter.LFunction χ s ≠ 0

  (`HeckeZeroSupremum = OAI.SevenEighths.HeckeZeroSupremum`; hC, hP as above.) Count face = physical face =
  G(99999/100000, 401/200, 13399/100000), each under `51/100 ≤ β` (the complementary case is trivial).
  Axioms of both theorems, of `windows_ok` and of the four edge covers: `propext, Classical.choice, Quot.sound`.

## 2. Exact mirror (rerun in this session, `fresh-look/scripts`, no change to the scripts)

`python3 exact_design.py 401/200 27/1000 3/10 11/25 - 3/25 6329401` (2.6 s):
`best N 6329401 theta = 0.87341198 (c = 6329401/50000000), h = 8001361/10000000, cover True, newTop 36 leaves/114
tests`; windows `C 2847/8192 8189/16384 0`, `C 2847/8192 9507/16384 3/8`, `capP 1/16384 3273/8192 3/8` (all three
used by newTop; minimal). Per edge at N: oldSmall 1 leaf/1 test, oldSwitch 4/7, newSwitch 2/3, newTop 36/114, deepest
box 17 bisections. N+1 = 6329402 fails on newTop (box delta ~0.45218, p in [0.49998, 1/2], the uncapped full-face
interior optimum of REPORT section 1); the other three edges still pass at N+1. `hceiling(theta)` = 0.800136132599,
at N+1 it is 0.800135945399 (floor7 8001359). `sidecheck2.py` (gen_return86 side conditions) passes for this
configuration; Lean's `TransportInstances` agrees (config 3 with the merged floor margin 1/200 fails, as REPORT says).
Exact rational recomputation of every `Constants.lean` value lemma (ell, x, y, kappa, dp, the four edge capacities,
geometry_mellin): all equal the Lean literals.

**Kernel negative control** (scratch copy of the (c, h)-dependent part of Data/RowsQ/CoverQ with c, h as arguments;
`decide +kernel`): at the real constants `coverOK .newTop` is true (copy agrees with the module); N = 6329401 is true
with fuel 17 and false with fuel 16 (mirror: max depth 17); N+1 = 6329402 is false with fuel 30 (with h = 8001361/10^7
and with h = 8001359/10^7); oldSmall, oldSwitch, newSwitch at N+1 are true. So the kernel matches the mirror exactly,
including the one-step failure and the minimal fuel. Nothing differed from the mirror.

## 3. Lean constants (pre-E5 merged -> new), all in `arvi_density/Return/Constants.lean`

| constant | merged (theta 0.87387234) | new |
|---|---|---|
| c | 6306383/50000000 | 6329401/50000000 |
| theta | 43693617/50000000 | 43670599/50000000 |
| h | 8044451/10^7 | 8001361/10^7 |
| countCB, physicalB | 96232839/10^8, 49283557/5*10^7 | 99999/100000 (both) |
| countCL, physicalLambda | 3853/2000, 4503/2000 | 401/200 (both) |
| countCap | 9999/100000 | 13399/100000 |
| physicalCap | 31/500 | 3/25 |
| numeratorCap | 3/50 | 3/40 |
| sMinus (hence naturalM = 1757/4000) | 3/100 | 27/1000 |
| mMinus | 377/1000 | 3/10 |

Unchanged: dm = 19/25, reserve = 1/10^8, naturalK = 9/2, weakC7 offset 7/4000 (branch unused by the windows), the
literal 11/25 in `upperM`/guard 12 (slack 3/4000 - 10^-7), eta = 10^-7. Derived values proved by `norm_num`:
ell = 6488203/37500000, x = 55932397/150000000, y = 68114791/150000000, kappa = 18670599/25000000,
dp = 8001361001/10^10; edge capacities oldSmall 62500/56011797, oldSwitch 11114791/336070782, newSwitch 57/1000
(numeratorCap branch), newTop 324159335616997/6015000000000000 (physical branch).

## 4. Files changed (Lean project)

- `Submissions/arvi_density/Return/Constants.lean`: all constants and value lemmas above; header note.
- `Submissions/arvi_density/Return/Endpoint.lean`: merged endpoint restated for the new faces and theta; **not
  compiled** (it sits on the stale merged certificate, section 6); the compiled endpoint is the tuning one.
- `Submissions/arvi_return_tuning/Data.lean`: base literals cQ, hQ, faces, caps, numCapQ (this run added only a
  docstring paragraph with the current values, which also forced the clean rebuild timed in section 5).
- `Submissions/arvi_return_tuning/GuardsQ.lean`: mMinusQ = 3/10, sMinusQ = 27/1000 (naturalMQ is computed from it).
- `Submissions/arvi_return_tuning/Windows.lean`: the three windows.
- `Submissions/arvi_return_tuning/EdgeCertificates.lean`: only the docstring (deepest box 17); fuel stays 30.
- `Submissions/arvi_return_tuning/Endpoint.lean`: source faces G(99999/100000, 401/200, 13399/100000) and theta literal.
- Consumers of the changed constants that needed **no** edit (proofs generic or by `norm_num`/the guards):
  `Return/Formulas, Facts, CountWidth (lowerM_buffer, natural_join_bounds 2/5 <= 1757/4000 < 1/2, admitted_widths,
  witnessLower_nonneg), CountDecode (admitted_natural_tail), CountAdmission, CountMonotonicity, CountWindow,
  Conductor, Geometry, TransportInstances (BoundsN with the new h), SourceInlet, WindowSources,
  EndpointFromNumerator`; tuning `Guards, RowsQ, CoverQ, FinalWindows, FinalScheme, FinalEnvelopeBounds, FinalRows,
  FinalSchedule, EndpointFromSources`. `ReturnD/*` does not import `Return/*` and is unchanged (floor margin 1/200
  still holds at this h).

## 5. Build and timing

`lake build Submissions.arvi_return_tuning.Endpoint`: Build completed successfully (12266 jobs), 7.6 s when run
first (everything already built by the earlier runs, oleans newer than sources). A real rebuild of the 12 modules
downstream of `Data.lean` (forced by the docstring edit): **1m16.5s wall** (user 58 s), per module Data 3.0,
RowsQ 2.4, CoverQ 3.3, Windows 8.6, FinalWindows 3.1, FinalScheme 4.1, FinalEnvelopeBounds 4.1, EdgeCertificates 22,
FinalRows 3.4, FinalSchedule 4.1, EndpointFromSources 6.3, Endpoint 6.3. Standalone elaboration (`lake env lean <file>`, each
includes ~3-4 s import load), seconds: Poly2 5.6, GuardsQ 4.1, Guards 7.8, Data 4.8, RowsQ 4.6, CoverQ 5.2,
**Windows 9.4**, FinalWindows 5.5, FinalScheme 5.4, FinalEnvelopeBounds 6.1, **EdgeCertificates 25.0**, FinalRows 4.8,
FinalSchedule 5.8, EndpointFromSources 8.5, Endpoint 8.4 (sum 111 s sequential). Return base: Constants 3.2, Formulas 4.2,
Facts 5.5, Conductor 5.2, CountAdmission 6.0, CountMonotonicity 4.5, CountDecode 6.7, CountWidth 6.0, CountWindow 5.1,
Geometry 4.2, SourceInlet 5.1, WindowSources 5.8, TransportInstances 4.4, EndpointFromNumerator 4.4. All exit 0, no
errors, no sorry. Kernel checks alone (profiler): windows 5.6 s, oldSmall 5.8 s, oldSwitch 6.6 s, newSwitch 7.0 s,
newTop 24.6 s (run in parallel, so EdgeCertificates is ~25 s wall). For comparison, the five-window reflective
proof of concept at the merged constants took 18.1 s (Windows) and 33.5 s (EdgeCertificates) in `logs/times.tsv`.

## 6. Collateral: modules that no longer compile, by design of the change

Changing the shared constants and the endpoint faces breaks every module that still carries the old record
(theta 0.87387234, old faces). Reproduced with `lake build` (FinalF50, `arvi_ode_shape.Final`) and `lake env lean`
on sample files (the `Rows/*` samples); the other modules in the list depend on those and were not built:

- Merged certificate of `arvi_density/Return` (generated for the old constants; 37 `Rows/*` files, `Windows`,
  `FinalWindows`, `FinalScheme`, `FinalEnvelopeBounds`, `EdgeCertificates`, `FinalRows`, `FinalSchedule`,
  `EndpointFromSources`, `Endpoint`): e.g. `Rows/Edge_oldSmall.lean:17:147: error: unsolved goals` (Bernstein
  identity, coefficients of the old constants) and `Rows/Admission01.lean` (12 errors of the same kind). Not
  regenerated: the reflective package replaces it (E5_RETUNE.md already listed it as stale).
- `arvi_density/FinalF50.lean`, `arvi_energy_region/ShapeEndpoint.lean` (import the stale merged endpoint).
- `arvi_return_tuning/FinalF50.lean` (error text): `FinalF50.lean:16:64: Type mismatch ChainF50.final_source hβ has
  type GlobalSource (96232839/100000000) (3853/2000) (1/10) but is expected GlobalSource (99999/100000) (401/200)
  (13399/100000)` and `:17:15` likewise for `ChainF50.source_64` (49283557/50000000, 4503/2000, 1/10). ChainF50
  cannot supply the new faces (its end face has B = 0.9623 < 0.99999, so it does not restrict to the new face).
- `arvi_ode_shape/Final.lean` (4 `Type mismatch` errors, lines 65, 66, 71, 72, same old faces from `count_source`,
  `physical_source`) and `Facets.lean` (imports it). Not my files; not touched.
- `arvi_return_tuning/Compat.lean`, `SameStatement.lean` (compare against the stale merged windows / old statement).

None of these is imported by the E5 path. The previous record (theta 0.87387234, merged return, ChainF50, FinalF50)
remains reproducible from the snapshot `research/chain/package/2026-10-29-arvi-density/` (on disk, excluded from
git). Decision needed from the owner of those files: delete/retire the three obsolete tuning modules and the
merged certificate, or keep them as history.

## 7. Next uses

The R1-conditional final theorem is `dirichlet_of_sources (fun hβ => e5_end ...) (fun hβ => e5_end ...)` with the
end face of the E5 line at Lambda = 401/200 (`Curve.lean`: sA = 1/1000, domain Icc (401/200) (5143/2000), end cap
13399/100000); the tuning endpoint takes exactly that face. Stretch items (REPORT 2', 3) not attempted: 3 needs the
transport floor margin change in `ReturnD` (rebuild of 119 modules).
