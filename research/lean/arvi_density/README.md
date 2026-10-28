# arvi_density: the density-split leaf with the floor as a parameter

Fork of the density-split leaf of PR 83 (Sil, `Submissions.sil_density_split_20261026`) in which the density
floor `q >= 13/20` (real parts `a >= 33/40`) is a real parameter `qf`, `3/5 <= qf <= 3/4`, instantiated at
`qf = 3/5` (real parts `a >= 4/5`). Lean prefix `Submissions.arvi_density`, namespace `QRH.ArviDensity`.
Only the modules that carry the floor are forked; everything else (the whole `CubeFree` engine, the LOW branch,
`LeafRows`, `LeafHighRow`, `UniformLow`, the HIGH pointwise bound) is imported from PR 83 unchanged.

Why `3/5`: the floor enters only through the HIGH row count, Collet's `fixed_natural_dictionary_raw_density`
(`33/40 <= a`, `Cycle61/Density/NaturalEndpoint.lean`). Collet's tree already contains the same lemma for
`4/5 <= a` (`Record1252270103Bootstrap/PR67Source/Cycle63/Density/NaturalEndpoint.lean`, built). Its statement
is definitionally the Cycle61 one with `33/40` weakened to `4/5` (and `J` chosen before the dictionary), so it is
used as is. Since `a = (1+q)/2`, `q >= qf >= 3/5` gives `a >= 4/5`.

## Forked files (modified copies of Sil's files, header `Copyright (c) 2026 Sil, ArviFoxy`)

| file | what changed |
|---|---|
| `Source/HybridGates.lean` | `13/20` becomes `qf` in `gQFloor`, the structure `HybridGates qf …` (field `q_floor`), `gQFloor_mul` and `HybridGates.dens_floor`; namespace `QRH.ArviDensity` (all other definitions and lemmas are copies) |
| `Density/Price.lean` | `densQ qf …` clips to `[qf, 3/4]`; `densQ_ge/le/nonneg/eq`, `densityPrice`, `densityPrice_f/lip` take `qf` (`0 <= qf <= 3/4`) |
| `Density/LeafHigh.lean` | `high_row_count` for `4/5 <= b` (was `33/40`), calling the new `fixed_natural_dictionary_raw_density_four_fifths` = Collet's PR 67 lemma; the scalar lemmas are unchanged |
| `Density/LeafHighEnergy.lean` | `high_branch` takes `qf` with `3/5 <= qf`; cut `qf <= q <= 3/4` (was `13/20 <= q`); the bins satisfy `4/5 <= b` because `(q+1)/2 >= 4/5` |
| `Density/Leaf.lean` | `density_priced_source` takes `qf` and uses the forked price and `high_branch`; the LOW branch is Sil's (uniform in `q`) |
| `Density/StepGates.lean` | `dsData`, `ds_ledger`, `ds_reference`, `dsGates` take `qf`; the exact instances `dsGates_first/second` are not restated |

Written from scratch: `Density/Compat.lean` (the floor `13/20` as a special case), `Density/Step.lean`
(composition with Sil's engine), `Theorem.lean` (instantiation at `3/5`, `#print axioms`).

## Top theorems (all depend only on `propext`, `Classical.choice`, `Quot.sound`)

* `Density.density_priced_source (qf B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain) (hL : 0 < L₀) (hqf : 3/5 ≤ qf)
  (hqf' : qf ≤ 3/4) hβ hface h0 h1 hparent : PricedPackedSource (densityPrice qf B₀ L₀ c₀ L A D s₀ hL _ hqf')
  Mmin Mmax Lplain`
* `Density.dsGates (h : HybridGates qf B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c) (hL : 0 < L₀)
  (hqf0 : 0 ≤ qf) (hqf1 : qf ≤ 3/4) : StepGates (dsData qf B₀ L₀ c₀ B L c A D hL hqf0 hqf1)`
* `Density.density_step`: `HybridGates qf …`, `DSFace`, `0 < B₀`, `3/5 ≤ qf ≤ 3/4`, `51/100 ≤ β` and the parent
  source `G(B₀,L₀,c₀)` give the source `G(B,L,c)` through Sil's `cubefree_step` (`StepInputs` from
  `step_inputs_of_provider`, `contrary_raw_side_provider`, `diag_supply`).
* At `qf = 3/5` (`Theorem.lean`): `density_priced_source_three_fifths`, `dsGates_three_fifths`,
  `density_step_three_fifths`.
* Non-vacuity: `sil_first_step_three_fifths`, `sil_second_step_three_fifths` apply `density_step_three_fifths`
  to PR 83's two transitions (a certificate with floor `13/20` is one with floor `3/5`, `HybridGates.ofSil_of_le`).

## The `13/20` special case (`Density/Compat.lean`)

`HybridGates.ofSil` (Sil's `HybridGates` is the fork's `HybridGates (13/20)`; the 46 certificates of PR 86
transfer), `HybridGates.mono_floor`, `HybridGates.ofSil_of_le`, `densityPrice_thirteen_twentieths` and
`dsData_thirteen_twentieths` (by `rfl`), `density_priced_source_thirteen_twentieths` (PR 83's leaf from the
fork's leaf), `dsGates_first_of_floor`, `dsGates_second_of_floor`.

## New certificates

A step at the floor `3/5` is certified by `HybridGates (3/5) B₀ L₀ c₀ B L c A D`, in Sil's layout with the
`q_floor` block proving a reserve for `dens - 3/5` (`gQFloor_mul (3/5) …`) and `Hybrid.*`, `box_lower`, `bern*`
taken from `QRH.ArviDensity` (a copy of Sil's scalar layer). `q_lower` (`dens > 1/2`) is kept as a field although
`qf >= 1/2` implies it. `research/density/gen_hybrid.py` produces such files (tested on PR 86's step 1, then fed to
`density_step_three_fifths`) with `--floor 3/5 --namespace QRH.ArviDensity --gates-namespace QRH.ArviDensity
--gates-import Submissions.arvi_density.Source.HybridGates --gate-lib fork_lib.py` and

```python
# fork_lib.py
import dataclasses
def modify(lib):
    q = next(g for g in lib.gates if g.key == "q_floor")
    q = dataclasses.replace(q, lean_fn="gQFloor (3/5 : ℝ)", mul_lemma="gQFloor_mul (3/5 : ℝ)")
    return dataclasses.replace(lib.replace("q_floor", q), structure="HybridGates (3/5 : ℝ)")
```

## Import closure and build

Compared with PR 83's leaf and provider modules the closure gains 9 modules of this package and 21 modules of
Collet's tree (13 `PR67Source/Cycle63/Density/*`, 8 `PR67Source/LocalMoment/*`), all already built.
Build: `QRH_PKG=Submissions.arvi_density python3 research/mixed-step/build/build_roots.py 2 LOGDIR
Submissions.arvi_density.Theorem` (clean build: 165 s wall with 2 jobs, 189 s of module time, on a loaded machine).
