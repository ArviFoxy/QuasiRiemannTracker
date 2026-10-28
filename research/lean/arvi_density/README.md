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

## The marked step (`density_step_marked`)

The marked leaf (`Density/LeafMarked.lean`, `Density.density_priced_source_marked`, price `markedDensityPrice`: the HIGH
term `highTerm` reduced by PR 76's repeated-mark gain `gainC ν B₀ L₀ c₀ s M`, eight copies) is turned into a step
`G(B₀,L₀,c₀) → G(B,L,c)` exactly as the unmarked leaf is by `Density/Step.lean`: scalar gates `HybridGatesM`, the
generic `StepGates (dsDataM …)` (`dsGatesM`), and Sil's `cubefree_step`.

| file | content |
|---|---|
| `Source/HybridGatesMarked.lean` (from scratch) | `HybridGatesM`; `HybridGatesM.ofHybridGates`; the machinery of the generated certificates: `le_gainC_of_facets`, cleared forms `gHighM_ij` of `highJ + facetVal_ij`, the density box variable `nuT`, `cNumY/cDenY`, `gHighM_scaled`, `box_lower3` |
| `Density/StepGatesMarked.lean` (modified copy of `Density/StepGates`) | `dsDataM`, `ds_high_aux_marked`, `ds_ledger_marked`, `ds_reference_marked`, `dsGatesM` |
| `Density/StepMarked.lean` (from scratch) | `density_leaf_marked`, `density_step_marked`, `density_step_marked_of_hybridGates` |
| `Source/HybridMarkedK15_46.lean`, `Source/HybridMarkedStretch46.lean` (generated) | marked certificates (below) |
| `MarkedStepTheorem.lean` (from scratch) | instantiation at `qf = 3/5`, the two certificates and PR 83's two transitions, `#print axioms` |

### The gates

`HybridGatesM qf B0 L0 c0 B L c A D` has the 18 fields of `HybridGates qf …` (`width_pos`, `sel_den_pos`, `dens_den_pos`,
`q_lower`, `q_upper`, `q_floor`, `H_lower`, `retained_cap`, `retained_width`, `low_identity`, `low_div_eq`,
`low_per_excess_width`, `principal_reference`, `second_reference`, `second_diagonal`, `reference_upper_positive`,
`sel_hasDerivAt`, `selection_monotonicity`) and, in place of `high_at_q` and `high_density_derivative`,

```lean
high_marked : ∃ r, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → ∀ ν, dens B0 L0 L A D v ≤ ν → ν ≤ 3/4 →
  r ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν
        + gainC ν B0 L0 c0 (width B0 L0 B L v - sel A D v) (packed A D v)
```

How the unmarked ledger controls HIGH on all of `ν ∈ [q, 3/4]`: `HybridGates.high_reserve` (uniform reserve of `highJ` there)
comes from `high_at_q` (reserve of `highJ` at `ν = q(v)`) and `high_density_derivative` (`25/24·H - (B-(L-1)w-u) > 0`) through
`highJ(ν₂) - highJ(ν₁) ≥ (ν₂-ν₁)(25/24·H - …)` on `[1/2, 3/4]`; `ds_high_aux` turns it into `ν(P_C+s) - (1-ρ)H ≤ u`.

The marked ledger (`ds_ledger_marked`, HIGH part): the marked excess `ν s - gainC ν … s H` is nondecreasing in the
retained width (`weighted_exponent_mono_rm`), `s ≤ w - u ≤ w - σ` (`σ = sel v`) and `P_C ≤ B + tl - L w`
(root face, `S ≥ w`), so the payment is `ν(B+tl-(L-1)w-σ) - (1-ρ)H - gainC ν … (w-σ) H`; the gain at the actual
`H = 1+t-6u` is compared with the nominal `1-6σ` by `gain_mono_rm`/`gain_row_loss_rm` (loss `≤ tl + 6·mesh`); then
`ds_high_aux_marked` closes it from `high_marked`. No separate `s = 0` gate and no density-derivative gate are needed
(a convexity argument is not necessary: the monotonicity in `s` is PR 76's `gainK_width_mono`). The reserve
`12·mesh + 3·tl ≤ r` fixes `meshL = m/24`, `tlL ≤ m/6`.

`high_marked` quantifies over all `ν ∈ [q(v), 3/4]` because the facets of the gain are not monotone in `ν`
(the eight-copy inverse facets decrease), so the reduction to `ν = q(v)` of the unmarked case does not hold.

### Certificates (`research/density/gen_hybrid.py --marked`)

`gainC` is the infimum over `p ∈ [0,1/2]` of the minimum of six facets `(i,j)`, so `high_marked` follows from
`r ≤ highJ + facetVal_ij` for all `(v, ν, p)` (`le_gainC_of_facets`). The density is the box variable
`t ∈ [0,1]`, `ν = q(v) + t(3/4 - q(v)) = Y/E` (`E = densE`, `Y = densK (1-t) + 3/4 t E`), so the region is the
box `[0, c-s₀] × [0,1] × [0,1/2]` and nothing is lost; the cleared forms times `E²` are polynomials of degree
`(4,2,≤3)` / `(3,1,≤2)` in `(v,t,p)` and are certified by exact tensor Bernstein coefficients (nested `bern2`, `bern3`).
For all 46 PR 86 steps at floor `3/5` each branch is one box (276 boxes); the 74 steps of the scratch floor-0.60 chain also.

* `HybridMarkedK15_46`: PR 86's transition 46, `A = 1/2`, `D = 5713/250`, floor `3/5`: reserve `67/25000`.
* `HybridMarkedStretch46`: the same parent, child `B = 4944203/5000000` (`B` lowered by `3/10000`), `A = 2/5`; here
  `high_at_q` is `-0.0045` at `v = 0`, so there is no `HybridGates` certificate, while the marked gate holds with
  reserve `41/25000`.

`MarkedStepTheorem.lean`: `k15_46_marked_step`, `stretch_marked_step` apply `density_step_marked` to them;
`sil_first_step_marked`, `sil_second_step_marked` apply `density_step_marked_of_hybridGates` to PR 83's certificates.
All depend only on `propext`, `Classical.choice`, `Quot.sound`.

Build: `QRH_PKG=Submissions.arvi_density python3 research/mixed-step/build/build_roots.py 2 LOGDIR
Submissions.arvi_density.MarkedStepTheorem` (`research/density/lean_check/run_marked_check.sh` regenerates the two
certificates first); each certificate elaborates in about 40 s.


## The return layer (`ReturnD/`, `Return/`)

`ReturnD/` (119 modules) is PR 83's transport layer `ReturnD/` forked into this package (module prefix `Submissions.arvi_density.ReturnD`, namespace
`QRH.ArviDensity.Return`; a token rename of Sil's files, notices kept, one `Modified by ArviFoxy` block added to each), with the coarse box
`BoundsN` widened to `ell < 175/1000`, `y > 440/1000` and `small_saving` threshold `6/100` (9 lines in `TransportGeometry.lean` and
`Transport/FinalFixedHigh.lean`; every consumer of the box is unchanged), so that every `theta > 873/1000` allowed by `floor_margin` is admissible
(PR 83: `theta > 0.8739167`). `Return/` (44 modules) is PR 86's final return in PR 86's layout, generated by `research/density/gen_return86.py`
for the constants of `Return/Constants.lean` (now the baseline: theta = 4369779/5000000, both sources PR 86's final face) with a two-source endpoint

```lean
QRH.ArviDensity.Return.dirichlet_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → GlobalSource countB countL countSrcCap)
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → GlobalSource physB physL physSrcCap)
    (χ : DirichletCharacter ℂ q) (hs : theta < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) : LFunction χ s ≠ 0
```

so the density chain can supply two different faces. Regenerate `Return/` for the final faces and theta with `gen_return86.py` (see
`research/density/README.md`). Build: `QRH_PKG=Submissions.arvi_density python3 research/mixed-step/build/build_roots.py 2 LOGDIR
Submissions.arvi_density.Return.Endpoint` (119 + 44 modules, about 15 + 8 minutes on two processes).
