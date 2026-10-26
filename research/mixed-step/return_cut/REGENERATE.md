# The final return of the mixed-step proof: regeneration and build

The final return half of the new proof: the source half (the mixed source step) is formalized
separately, and the return only consumes its two faces as hypotheses. Current design: **(b)**,
Lemma W count windows and the face caps of piece 7's cap ramp, **θ = 437037/500000 = 0.874074**.

- **Package.** `Submissions.arvi_mixed_step_20261026` in the Lake project `/home/user/lean-env/qrh`.
  The return is `ReturnD/` (119 modules: Collet's transport layer and generic physical return,
  forked) and `FinalReturn/` (42 modules: constants, formulas, count windows, rows, endpoint). Other
  agents keep further modules in the same directory (`Graph/`, `Family/`, `Fan/`, `Finite/`); these
  scripts never touch them. Imported unchanged: Collet's and the baseline's trees, and
  `Graph.NaturalCap` of PR 76's package (`β ≤ 7/8`).
- **Top theorem.** `QRH.RepeatedMarks.Return.Final.beta_of_global_sources`
  (`FinalReturn/EndpointFromSources.lean`):
  `UniformUnitFaceSource countGlobal → UniformUnitFaceSource physicalGlobal →
   2·β − 1 ≤ naturalK/6 → β ≤ theta`. Its single-stage corollary
  `QRH.RepeatedMarks.Return.beta_of_two_global_sources` (`FinalReturn/EndpointFromGlobalSources.lean`)
  discharges the natural cost by the baseline's `β ≤ 7/8`, as PR 76 does.
- **Interface for the source side.** `countGlobal = globalFace countCB countCL capC` and
  `physicalGlobal = globalFace physicalB physicalLambda capP`, with `globalFace B Λ cap = ⟨B,Λ,0,B,0,cap⟩`
  and the exact faces of `../faces_k92_ramp.json`. Equivalently (`interface_beta` in
  `AxiomsCheck.lean`), two `Record1252270103Finite.Source` values `fC`, `fP` with these exact `B`,
  `L`, `cap` (`q` and the fees are free) and
  `51/100 ≤ β → QRH.Record1252270103Graph.P fC ∧ QRH.Record1252270103Graph.P fP` give `β ≤ theta`:

  | face | `B` | `L` | `cap` |
  |---|---|---|---|
  | C (`mpiece7` at `1 − Dy`) | `4553636084322336971646479/4724464025600000000000000` (0.9638418) | `4954148591857540990249/2362232012800000000000` (2.0972320) | `111411/1310720` (0.0849998) |
  | P (`mpiece7` at `35747·Dy`) | `74757332803822334159435159927/77405618595430400000000000000` (0.9657869) | `5033014753577776399373/2362232012800000000000` (2.1306183) | `527267/6553600` (0.0804546) |

  The caps are those of the ramp `cap(y) = 3/40 + y/100` (`Dy = 1/65536`), which the dev tree's
  `Graph/MixedChain.lean` (`faceC_cap`, `faceP_cap`) delivers.

## 1. Design (b) (exact; `return_cut.env`)

| parameter | value | where it lands |
|---|---|---|
| `theta` | `437037/500000` = 0.874074; exact θ* = 0.8740728 (margin 1.2e-6) | `ReturnConstants.c = 62963/500000` |
| `h` | `403/500` = 0.806 | `ReturnConstants.h` |
| faces C, P | the table above (`QRH_FACES = ../faces_k92_ramp.json`) | `countCB`, `countCL`, `physicalB`, `physicalLambda`; caps in `SourceInlet.countGlobal`, `physicalGlobal` |
| count windows (Lemma W) | `QRH_WINDOWS=lemmaW`; window caps = face caps | `ReturnFormulas` (`crossM`, `crossW`, `lowerM`, `upperM`, guards, `branchCap`), `CountWidth`, `CountDecode`, `FinalWindows` |
| `SC` (Collet's count window `countWindow`) | `29/500`, no longer binding | `SourceInlet.countWindow` |
| `SP` (physical numerator cap) | `29/500` | `numeratorCap`, `ReturnD/Schedule.cap`, `EndpointFromSources` |
| natural cost `K` | `9/2` | `naturalK` |
| switch bound | `dMinus_lower : 1/2 < dMinus` (`QRH_DMINUS=1/2`); `ds` = 0.73830 | `ReturnD/Schedule.lean` |
| transport bounds | `h < 807/1000`, `y < 467/1000`, `ell < 1710/10000` (`QRH_RELAXED`); here `h` = 0.806, `y` = 0.465259, `ell` = 0.170371; the lower ends `874/1000 < theta` (slack 7.4e-5), `793/1000 < h`, `458/1000 < y`, `1672/10000 < ell` hold | `ReturnD/TransportGeometry.lean`, `ReturnD/Transport/FinalFixedHigh.lean` |
| receipts | Lemma D mode (`QRH_MODE=lemmaD`) | `gen_return_lean.py` |

The certificate has 33 rows (6 edge modules; branches old 16, C-7 7, C 6, Ccap 3, Pcap 1) and 14
admission windows. Smallest slacks at the declared θ: `theta > 874/1000`
7.4e-5, `principal_z` 9.3e-5, `floor` 1.1e-4.

**Fallback (a)** (`return_cut_a.env`): Lemma W with the caps 3/40 (`../faces_k92.json`),
`theta = 874137/1000000` (exact θ* = 0.8741351 at h = 803/1000), 34 rows, 16 windows. It uses the
same `ReturnD` as (b), so switching rebuilds `FinalReturn` only:
`QRH_ENV=$PWD/return_cut_a.env ./run_all.sh WORKDIR`.

## 2. Lemma W (spec: `../../return-transfer/REPORT.md` §2)

Collet's count certificate carries three conservative windows: the lower plain window `m_- = 2/5`,
the width window `s_+` below the face cap, and the natural-tail join at the fixed `m_H`. Lemma W
opens them to the faces' proved domain. The plain line joins the natural one at the crossover
`m_X = (K·B − Λ)/(2(K − Λ))`, where the face width `(B − 2m)/Λ` equals the natural width
`(1 − 2m)/K = w_X`, so there is no jump.

**Lean feasibility (checked by building).** Collet's `count_from_piecewise_moments` and
`count_fiber_at_window` take an `AdmittedWindow`, whose fields need only `0 ≤ mLo`,
`2/5 ≤ mHi < 1/2`, `cap ≤ sourceCap`, `cap ≤ 7/37`, the plain crossing, the natural tail at `mHi`,
and positive widths on `[mLo, mHi]`, with the moment on `broadFace B Λ sourceCap`. The windows are a
plain list, so `mHi` can differ per window. Our instance (`FinalWindows`) now has
`mLo = lowerM − 1e-7 ≥ 0`, `mHi = crossM b ∈ [2/5, 1/2)` (`cross_join_bounds`, by `norm_num` per
branch), and `sourceCap = branchCap` = the face cap (`Restricts` allows equality).

**What changed (generated, behind `QRH_WINDOWS=lemmaW`):**
- `ReturnFormulas`:
  - `crossM b`, `crossW b = (1 − 2·crossM b)/K`;
  - `lowerM`: `2/5 + η` becomes `η`;
  - `upperM`: `min(1/2 − η, crossM b − η)`, and for capped branches also `(B − Λz*)/2 − η` (no 11/25, no `s_-`);
  - guard 10, the N-tail: at `crossM b` with width `crossW b`;
  - guard 12: `1/2 − crossM b − η`; guard 13: `crossW b − η`;
  - guard 14 (capped): `(z* − η)·DJ`;
  - `branchCap` = the window caps.
- `CountWidth`:
  - `lowerM_buffer` is `η ≤ lowerM`;
  - `cross_join_bounds` and `cross_width` (the identity `(B − 2·crossM)/Λ = crossW`, by `norm_num` per branch) replace `natural_join_bounds`;
  - `admitted_widths` runs up to `crossM b`, from guard 13 and `cross_width`.
- `CountDecode`: `admitted_natural_tail` at `crossM b`, from guard 10 and `(1 − 2·crossM)/(6·(K/6)) = crossW`.
- `FinalWindows`: `mHi := crossM w.branch`.
- Regenerated as before: `ReturnConstants`, `CountWindows`, `FinalEdgeCertificates`, `Rows`.

All of it compiled on the first build; no proof needed repair.

## 3. Exact θ* (`theta_star.py`: exactly the Lean branch set, Lemma W, the transport bounds)

| setting | caps C, P | best h | θ* | binding at θ* − 1e-7 |
|---|---|---|---|---|
| Collet windows | 3/40, 3/40 | 2011/2500 | 0.8742701 | `newTop` cover |
| (a) Lemma W | 3/40, 3/40 | 0.803 (0.8741352 at 0.8025, 0.8741356 at 0.8044) | **0.8741351** | `newTop`, δ ≈ 0.433, p = 1/2: the capped count branches at the face cap (`Ccap`/`Pcap`, return margin ≈ 0); the uncapped ones fail their window (face width at m* > cap) |
| (a) with the report's windows (cap − 1e-4) | 749/10000 | 0.8025–0.803 | 0.8741359 | as above |
| **(b)** ramp `y/100` | 0.0849998, 0.0804546 | 0.806 (end of [0.796, 0.806]) | **0.8740728** | `newTop`, δ ≈ 0.443, p = 1/2: the uncapped count branch C (the face line `B_C`, `Λ_C`; return margin ≈ 0); the capped branches fail their upper window (face width at m* = 0.0821 < z*) |
| (c) ramp `y/50` | 0.0949997, 0.0859091 | 0.806 | 0.8740728 | as (b) |
| (d) ramp `3y/200` | 0.0899998, 0.0831818 | 0.806 | 0.8740728 | as (b) |

- θ\*(h) falls with h for (b)–(d) up to h ≈ 0.8062 (0.8740725). Beyond that the `floor` receipt
  (`BoundsR.floor_margin`) binds: at h = 0.8065, θ* = 0.8740919.
- The transport bound `458/1000 < y` binds only for h ≤ 0.7985.
- The C cap stops binding above about 0.0821 (the face width at the binding crossing), so every
  ramp from (b) on gives the same θ*.

**Face positions (pricing only, `price_faces.py`, `price_grid.py`; flow faces from `../flow_k92.json`,
B = E + L·s).**
- At the binding point (`newTop`, δ ≈ 0.443, p = 1/2), the count value of the affine branch falls
  monotonically along the flow: R = 0.613384 at s = 0.030, 0.612933 at 0.0595, 0.612898 at 0.062.
  So no extra count face inside the family (pieces 5–7, or the fan) can help: one extra face at any
  of 10 positions s ∈ [0.030, 0.059] leaves θ* unchanged.
- Moving C beyond the family end helps: θ* = 0.8740680 with C at s = 0.062 (h = 0.8062) and
  0.8740679 at h = 0.80625, against 0.8740725 for (b) at the same h. This needs a C cap ≥ 0.086
  (with 0.085 the C cap binds again, 0.8740704).
- P is best where it is (s ≈ 0.056–0.057). An extra count face beyond the family equals moving C,
  and 2 or 4 such faces give nothing more.
- `theta_star.certifiable` now resets `cert_return.ADM_CACHE` when the faces change: it caches
  admissions by branch name, which only matters when faces vary inside one process.

## 4. Changes to the generators (defaults unchanged)

- `../../repeated-marks/cert_return.py`:
  - `QRH_DMINUS` (default 3/4) sets the receipt `dMinus_lower_3_4` (`ds − DMINUS`).
  - `QRH_WINDOWS` (`collet` by default, or `lemmaW`); `crossover(B, L)` and `admission_polys_W`.
- `../../repeated-marks/gen_return_lean.py`:
  - mode `lemmaD` (also drops `source_lambda_low`);
  - with `QRH_WINDOWS=lemmaW`: `LEMMA_W_EDITS` on the formulas, `window_caps` (`QRH_WCAP`, default the face caps), and `lemma_w_branches`, which asserts `K > Λ`, `2/5 ≤ m_X < 1/2` and `w_X > η` for the five improved branches.
- `../../repeated-marks/fork_return.py`: with `QRH_WINDOWS=lemmaW`, `LEMMA_W` patches `CountWidth`, `CountDecode` and `FinalWindows`. Each patch is asserted to apply once.
- `../../repeated-marks/fork_transport.py`:
  - `QRH_DMINUS` relaxes `dMinus_lower`;
  - `QRH_RELAXED` sets the `BoundsR` bounds (now `807/1000, 467/1000, 1710/10000`: the lower θ pushes `ell` above 0.17).
- `single_stage.py` (here): PR 76's hand edits of the two endpoint modules.

**Checks.**
- With PR 76's parameters and no flags, the generators give byte-identical output to the originals (rechecked after the Lemma W changes).
- The pipeline reproduces all 164 return modules of PR 76 byte for byte.

## 5. Commands

```sh
cd /home/user/QuasiRiemannTracker/research/mixed-step/return_cut
./run_all.sh WORKDIR                                   # design (b); WORKDIR a new scratch directory
QRH_ENV=$PWD/return_cut_a.env ./run_all.sh WORKDIR2    # fallback (a)
```

`run_all.sh` runs these steps, with the env file sourced:

```sh
python3 theta_star.py              # exact θ*; also --h H1,H2,... for an h scan, --anchor A
./regenerate.sh WORKDIR            # generators, assembly, installation of ReturnD/ and FinalReturn/
python3 build.py 2 LOGDIR          # the 161 return modules, dependency order, at most 2 Lean processes
python3 axioms_check.py > AxiomsCheck.lean
cd /home/user/lean-env/qrh && PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH \
  lake env lean /home/user/QuasiRiemannTracker/research/mixed-step/return_cut/AxiomsCheck.lean
```

`regenerate.sh` runs, from `research/repeated-marks/`:

```sh
# W/faces.json = $QRH_FACES as the list [C, P]; CAPC, CAPP = its caps
python3 gen_return_lean.py W/faces.json $QRH_THETA $QRH_H 0 1 W/RET $QRH_SC $QRH_SP lemmaD
python3 fork_return.py W/RET W/OUT $CAPC $CAPP $QRH_SC $QRH_SP transport
python3 fork_transport.py W/RD $QRH_SP           # QRH_RELAXED, QRH_DMINUS
# assemble W/PKG (ReturnD from W/RD; FinalReturn from W/OUT plus ReturnConstants, ReturnFormulas,
# ReturnFacts, Rows from W/RET; Submissions.repeated_marks_20261024 -> $QRH_PKG)
python3 single_stage.py W/PKG/FinalReturn $QRH_PKG $QRH_PR76
# install: only changed files are rewritten; stale .lean files of ReturnD/, FinalReturn/ are removed
```

## 6. Results (2026-10-26)

| build | design | modules compiled | wall | sum of module times | status |
|---|---|---|---|---|---|
| 1 | Collet windows, θ = 34971/40000, `faces_exact.json` | 172 | 1318 s | 2528 s | ALL-OK |
| 2 | Collet windows, θ = 34971/40000, `faces_k92.json` | 53 | 749 s | 1321 s | ALL-OK |
| 3 | **(b)**: Lemma W, θ = 437037/500000, `faces_k92_ramp.json` | 161 (119 `ReturnD`, 42 `FinalReturn`) | 923 s | 1738 s | ALL-OK |

- `ReturnD` was rebuilt in build 3 because `TransportGeometry` changed (`h < 807/1000`, `ell < 1710/10000`).
- All return oleans are consistent: each is newer than its source and than its dependencies' oleans.
- The `#print axioms` of all modules print only the three standard axioms. No `sorry`.

**Axioms** (`AxiomsCheck.lean`, final build):

```
'QRH.RepeatedMarks.Return.Final.beta_of_global_sources' depends on axioms: [propext, Classical.choice, Quot.sound]
'QRH.RepeatedMarks.Return.beta_of_two_global_sources' depends on axioms: [propext, Classical.choice, Quot.sound]
'QRH.RepeatedMarks.Return.ReturnCountWindow.toAdmitted' depends on axioms: [propext, Classical.choice, Quot.sound]
'interface_beta' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`AxiomsCheck.lean` also checks, in the kernel, `c`, `theta = 437037/500000`, `h`, `naturalK`,
`numeratorCap`, `GenericArithmetic.cap`, `countGlobal`, `physicalGlobal`, `countWindow`, `branchCap`
and the four face rationals.

**The dev tree's endpoint.** `Submissions/arvi_mixed_step/Graph/Endpoint3.lean` (dev `MixedChain`
with the ramp caps) elaborates against this `FinalReturn` with no errors. A scratch copy with
`#print axioms` gives `QRH.MixedStep.Graph.beta_of_step3 : NFStep3 → β ≤ QRH.RepeatedMarks.Return.theta`
with `[propext, Classical.choice, Quot.sound]`. (Checked with `lake env lean` without `-o`; nothing
in the dev tree was written.)

**Stale copies.** In this package, `Graph/MixedChain.lean` (01:45, caps 3/40) and its
`Graph/Endpoint3` are older copies:
- Endpoint3 fails against the new return (`faceC_cap = 3/40 ≠ 111411/1310720`);
- their oleans (01:57) were built against the previous return.

Refresh them from the dev tree and rebuild before any manual check (`lake env lean` trusts imported
oleans). A `lake build` rebuilds them anyway, since these manual builds leave no trace files.
