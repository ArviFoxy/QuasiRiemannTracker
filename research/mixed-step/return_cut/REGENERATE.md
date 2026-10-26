# The final return of the mixed-step proof: regeneration and build

The final return half of the new proof, built and checked now: the source half (the mixed source
step) is formalized separately, and the return only consumes its two faces as hypotheses.

- **Package.** `Submissions.arvi_mixed_step_20261026` in the Lake project `/home/user/lean-env/qrh`,
  directories `ReturnD/` (119 modules: Collet's transport layer and generic physical return, forked)
  and `FinalReturn/` (53 modules: final-stage constants, rows, windows, endpoint). Everything else is
  imported unchanged: Collet's and the baseline's trees, and `Graph.NaturalCap` of PR 76's package
  (`β ≤ 7/8`). PR 76's package, Collet's and the baseline's trees are not modified.
- **Top theorem.** `QRH.RepeatedMarks.Return.Final.beta_of_global_sources`
  (`FinalReturn/EndpointFromSources.lean`):
  `UniformUnitFaceSource countGlobal → UniformUnitFaceSource physicalGlobal →
   2·β − 1 ≤ naturalK/6 → β ≤ theta`, with `theta = 34971/40000`. The single-stage corollary
  `QRH.RepeatedMarks.Return.beta_of_two_global_sources` (`FinalReturn/EndpointFromGlobalSources.lean`)
  discharges the natural cost by the baseline's `β ≤ 7/8`, as PR 76 does.
- **Interface for the source half.** `countGlobal = globalFace countCB countCL (3/40)` and
  `physicalGlobal = globalFace physicalB physicalLambda (3/40)`, with `globalFace B Λ cap = ⟨B,Λ,0,B,0,cap⟩`
  (Collet's `SourceInlet`) and the exact faces `C`, `P` of `../faces_exact.json`.

## 1. Design (all exact; `return_cut.env`)

| parameter | value | where it lands |
|---|---|---|
| `theta` | `34971/40000` = 0.874275 (exact θ* = 0.8742701, `theta_star.py`) | `ReturnConstants.c = 5029/40000` |
| `h` | `2011/2500` = 0.8044 | `ReturnConstants.h` |
| count face C | `B = 517574273064321753867031/536870912000000000000000` (0.96406), `L = 563952501813603236449/268435456000000000000` (2.10089) | `countCB`, `countCL` |
| physical face P | `B = 51846496626077474773381/53687091200000000000000` (0.96572), `L = 114318071421667363757/53687091200000000000` (2.12934) | `physicalB`, `physicalLambda` |
| face caps | `3/40` (both) | `SourceInlet.countGlobal`, `physicalGlobal` |
| count window `SC` | `29/500` | `SourceInlet.countWindow`, `ReturnFormulas.branchCap` |
| physical numerator cap `SP` | `29/500` | `ReturnConstants.numeratorCap`, `ReturnD/Schedule.cap`, the restriction in `EndpointFromSources` |
| natural cost `K` | `9/2` | `ReturnConstants.naturalK` |
| switch bound (Relaxation 1) | `dMinus_lower : 1/2 < dMinus` (`QRH_DMINUS=1/2`); `ds = 13958000/18907431` = 0.73823 | `ReturnD/Schedule.lean` |
| transport bounds (Relaxation 2) | `h < 806/1000`, `y < 467/1000`, `ell < 1700/10000` (`QRH_RELAXED`); the values are `h` = 0.8044, `y` = 0.46527, `ell` = 0.16957, and the lower ends `793/1000 < h`, `458/1000 < y`, `1672/10000 < ell`, `874/1000 < theta` hold | `ReturnD/TransportGeometry.lean` (`Geometry.BoundsR`), `ReturnD/Transport/FinalFixedHigh.lean` |
| receipts | Lemma D mode (`QRH_MODE=lemmaD`): Collet's window receipts and `λ_P > 3` are not checked; the schedule needs `2 ≤ λ_P ≤ 9/2` | `gen_return_lean.py` |

The certificate has 67 rows and 25 admission windows (PR 76: 42 and 17). Smallest kept receipts:
`principal_z` 9.1e-5, `conductor_kink_before_top` 6.8e-4 (`dk` = 0.80372 < `dp` = 0.8044),
`floor` 1.27e-3, `incumbent` 1.45e-3.

## 2. Changes to the generators (default behavior unchanged)

- `../../repeated-marks/cert_return.py`: `DMINUS = QRH_DMINUS` (default `3/4`); the receipt
  `dMinus_lower_3_4` checks `ds − DMINUS`.
- `../../repeated-marks/gen_return_lean.py`: a mode `lemmaD` (as `cert_return.run(mode='lemmaD')`):
  the `global` drops, and `source_lambda_low` (`λ_P > 3`, needed only by PR 69's FR21) is not checked.
  `pr69` and `global` are unchanged.
- `../../repeated-marks/fork_transport.py`: with `QRH_DMINUS` set, the schedule field
  `dMinus_lower:3/4<dMinus` becomes `dMinus_lower:QRH_DMINUS<dMinus` (with a doc comment). All uses of
  the field need only `1/2 < dMinus` (`GenericFeedback` `d ≥ 0`, `PhysicalDirect/Geometry` `d > 0`,
  `Active` `1/2 < d`, `SelectedBin` `0 < d`, `1/2 ≤ d`, `SourceSelection` `1/200 ≤ dm`, `1/2 ≤ d`).
  The concrete proof in `FinalReturn/FinalSchedule.lean` (`dsimp …; norm_num`) is generic in the
  field's statement and proves `1/2 < ds` unchanged.
- `single_stage.py` (here): PR 76's hand edits of the two endpoint modules, made reproducible
  (the two-stage theorems of `EndpointFromSources` removed; `EndpointFromGlobalSources` replaced by
  the single-stage endpoint).
- The physical-face restriction in `EndpointFromSources` already follows `SP`
  (`fork_return.lemma_d` writes `⟨physicalB,physicalLambda,0,1/2,0,SP⟩`): it is now `29/500`.

**Checks of the pipeline.**
- With PR 76's parameters (`../../combined/sil_face.env`, PR 76's faces) the modified generators
  give byte-identical output to the unmodified ones (no `QRH_DMINUS`, modes `global`).
- The whole pipeline (`gen_return_lean` → `fork_return` → `fork_transport` → prefix rename →
  `single_stage.py`) reproduces all 164 return modules of PR 76's package byte for byte.

## 3. Commands

```sh
cd /home/user/QuasiRiemannTracker/research/mixed-step/return_cut
./run_all.sh WORKDIR          # all of the below; WORKDIR is a new scratch directory
```

Step by step (what `run_all.sh` runs):

```sh
source return_cut.env
python3 theta_star.py         # exact θ* with exactly the Lean branch set; the declared θ must pass
./regenerate.sh WORKDIR       # generators, assembly, installation into the Lake project
python3 build.py 2 LOGDIR     # every module, dependency order, at most 2 Lean processes
cd /home/user/lean-env/qrh
PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH \
  lake env lean /home/user/QuasiRiemannTracker/research/mixed-step/return_cut/AxiomsCheck.lean
```

`regenerate.sh` runs, from `research/repeated-marks/`:

```sh
python3 gen_return_lean.py $QRH_FACES $QRH_THETA $QRH_H 0 1 W/RET $QRH_SC $QRH_SP lemmaD
python3 fork_return.py W/RET W/OUT $QRH_CAP $QRH_CAP $QRH_SC $QRH_SP transport
python3 fork_transport.py W/RD $QRH_SP         # reads QRH_RELAXED and QRH_DMINUS
# assemble W/PKG: ReturnD from W/RD; FinalReturn from W/OUT plus ReturnConstants, ReturnFormulas,
# ReturnFacts and Rows/ from W/RET; rename Submissions.repeated_marks_20261024 -> $QRH_PKG
python3 single_stage.py W/PKG/FinalReturn $QRH_PKG $QRH_PR76
# install: only files whose content changes are rewritten; stale .lean files are removed
```

`build.py` compiles each module with
`lake env lean -o .lake/build/lib/lean/<module path>.olean -i <…>.ilean <module>.lean` from the Lake
project, in dependency order, rebuilding a module when its olean is missing or older than its source
or a package dependency's olean. It never touches other packages' oleans.

## 4. Rerunning on new faces

Replace `../faces_exact.json` (or point `QRH_FACES` elsewhere) and run `./run_all.sh WORKDIR`.
`ReturnD/` does not depend on the faces or on `theta` (it is generic in `Geometry.Parameters`,
`BoundsR` and `PhysicalSchedule`), so only `FinalReturn/` is rebuilt. If `theta_star.py` reports that
the declared `theta` fails, set `QRH_THETA` at or above the reported θ* (and check that the new
`ell`, `y`, `h` stay inside `QRH_RELAXED`).

## 5. Results

(filled in below)
