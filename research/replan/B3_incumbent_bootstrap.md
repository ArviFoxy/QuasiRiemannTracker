# B3 — The record as incumbent (acyclic bootstrap): where 7/8 enters, what it buys (2026-10-28)

Read-only plus Python (no `lake`/`lean`, nothing committed or posted, nothing under `research/` edited except this file).
Scratch (scripts, logs): `$SCRATCH/analysis/B3/` (`$SCRATCH` = `$SCRATCH`).
Exact return prices use the validated toolchain `$SCRATCH/analysis/lemmaW/tc/` (`pr86.py`, `best.py`, `cert_return.py`; reproduces PR 86's Lean to exact rational equality).

Path shorthand (all `grep -R`, the `lean-env` entries are symlinks):
`S83/` = `$SCRATCH/upstream/submissions/2026-10-26-sil-density-split/src/Submissions/sil_density_split_20261026/`;
`S86/` = `$SCRATCH/upstream/submissions/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/`;
`HC/` = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/`; `P76/` = `.../arvi_repeated_marks_on_sil_face_20261025/`; `BL/` = `.../openai_baseline/`;
`LW/` = Lewko's tree, extracted to `$SCRATCH/analysis/B3/lewko/submissions/2026-10-23-lewko-acyclic-bootstrap-874772906/src/Submissions/lewko_acyclic_bootstrap_874772906/`.
Tags: **[V]** verified by reading Lean or by exact computation; **[R]** float replica of the Lean gates (validated, not a proof); **[I]** inference.

---------------------------------------------------------------------------------------------------

## 0. Verdict

The idea is mathematically sound (acyclic: the new proof takes PR 86's `β ≤ θ_rec` as an input) and is worth **−1.3e-6** in θ. That is 13 % of the 1.05e-5 still missing after floor + longer chain + role split, and 6.7 % of the full 2e-5. It is not a route to the bar.

* **[V]** The incumbent enters the record's proof quantitatively in **one** place: the native step's slot price `κ = 2β−1 ≤ 3/4` (`β ≤ 7/8`). It sets the native barrier `L* = 6κB/(1+κ) = 18B/7` and so the junction face where the native chain hands over to the first density step. With `θ_I = 4369779/5000000`: `κ' = 3739558/5000000 = 0.7479116`, `K' = 6κ' = 4.487470` (was 4.5), `L*` moves 2.571403 → 2.567306 (−0.0041) at `B = 0.99999`.
* **[V]** Every other 7/8 is either a qualitative upper hypothesis that `β ≤ θ_I` satisfies a fortiori (HIGH cap, density clip, Collet's range `a ≤ 7/8`, the return's `naturalK`, `δ ≤ 3/4`, transport tail exponents) or a structural constant that only coincides (`9/2 = (3/2)·3`, `(9/2)^{2/3}`). Pricing those as if lowered gives exactly 0 (return) or identical certificates (density gates).
* **[R]+[V]** Exact θ\* (floor-coupled h):

  | configuration | incumbent 7/8 | incumbent θ_rec | gain |
  |---|---|---|---|
  | PR 86 style: floor 0.65, Collet windows, branches old/C/Pcap, count k=46 / physical k≈38, discrete chain ΔL=0.005 | 0.873954805 | 0.873953441 | **−1.36e-6** |
  | floor 0.60, Lemma W six branches, count k=73 / physical k≈37, discrete chain | 0.873946251 | 0.873944910 | **−1.34e-6** (gap to 0.8739358: 1.045e-5 → **9.11e-6**) |
  | same, continuum (ODE) faces | 0.873945041 | 0.873943726 | −1.32e-6 |
  | iterate θ_I ← θ\* (continuum) | | 0.873943710 | further −1.6e-8 (A) / −5e-9 (B): converged after one step |

  The gain is linear in the reduction of `K`: **1.05e-4 per unit of K** (scan θ_I = 0.8747 … 0.8735, §3.4). An incumbent equal to the bar itself would give 1.34e-6.
* Lewko's acyclic bootstrap gained 4e-9 from ΔK = −3.6e-5 (1.1e-4 per unit K), the same sensitivity (§4).
* **Lean cost [I]**: roughly 0.5–0.9k hand-adapted lines (a κ'-priced native step; the 18.9k-line `Second/*` provider, the density engine and the root chain are reused) plus the same regeneration work as the floor plan, but now **all** density certificates must be regenerated (the chain shifts), so PR 86's 46 files cannot be reused (~3 MB of generated Lean for 46–75 files). Not worth doing for 1.3e-6 alone; it is a cheap rider only if tracks A1–A3 are executed anyway and the rest lands within ~1.3e-6.

---------------------------------------------------------------------------------------------------

## 1. Where 7/8 / 3/4 / 9/2 / 18/7 enter the record's proof (question 1)

Closure of PR 86's `Theorem` over the five source packages: 4401 modules (PR 86: 93, PR 83: 489, PR 76: 422, Collet: 474, baseline: 2923; `B3/closure86.py`). I grepped the non-baseline packages for `7/8`, `3/4`, `9/2`, `18/7`, `naturalK`, `naturalκ`, `nativeK`, `*incumbent*`, `native_kappa_bound`, `beta_le_seven_eighths` and read the hit clusters: every quantitative one, and representative files for the many mechanical `(7/8)` hypothesis forwards in `ReturnD/Transport/**` and `Cycle61/**` (generated rows/certificates excluded).

**How the proof uses `β`.** Assume `θ < β = HeckeZeroSupremum.beta` (sup of real parts of all non-pole zeros of the Hecke family, `BL/OAI/NumberTheory/DirichletL/Hecke/ZeroSupremum.lean:10-16`). The baseline gives `β ≤ 7/8` (`P76/FourthPower/IncumbentInput.lean:16`, `P76/Graph/NaturalCap.lean:15`, `HC/Cycle61/Density/FixedDensity.lean:15-19`). The only quantitative consequence is the prime-sum bound `‖slot‖² ≤ C Z^ε P^κ` for **any** `κ ≥ 2β−1` (`BL/.../Moments/NaturalFixedRaySourceNaturalPrime.lean:73`, `NaturalFixedRaySourceRayPrime.lean:18`, `RayMaskedFloorSlots.lean:33`; hypothesis `hκ : 2*beta-1 ≤ κ`, no lower bound on κ).

### 1.1 Table (a = incumbent input, replaceable; b = structural / coincidence; "qual." = only an upper hypothesis)

| # | site | content | class | effect of `θ_I = θ_rec` |
|---|---|---|---|---|
| 1 | `S83/Source/NativeBootstrap.lean:25-26,31,38,62-63`; PR 86 `S86/Source/NativeK15.lean` (30 steps, `nativeK`) | `nativeK := 3/4` ("`2*(7/8)-1` from the baseline bound"); gates `retention` and `overshoot` `0 < 1 − κ(6B₀−L₀)/L₀`; barrier `Ls := 18*Bg/7` | **a, quantitative** | barrier 2.571403 → 2.567306; **the whole −1.3e-6** |
| 2 | `S83/CubeFree/StepData.lean:180-192` (`nativeData`: `κ := 3/4`, `price := parentPrice (3/4) …`), `:236-243` `native_retention_aux`, `:257-351` `native_ledger` | the native ledger inequality `κ·defect/L₀ ≤ u + ε/16` | **a, quantitative** | κ → κ' in two proofs (~140 lines) |
| 3 | `S83/CubeFree/Leaf/Native.lean:85-98`, `Leaf/Parent.lean:118-123,157-158,249-256`, `Assembly/Leaves.lean:55,80` | the analytic native leaf: `nativePrice (3/4)`, `parentPrice (3/4)`, `canonical_energy … (3/4) … native_kappa_bound` | **a, quantitative** | analytic input already generic: `P76/FourthPower/NativeNonfixedEnergy.lean:27-32` `canonical_energy (hκ : 2β−1 ≤ κ)` ← `NativeSlotDeletion.lean:72` ← baseline `natural_slot_product` |
| 4 | `S83/CubeFree/StepData.lean:89,106,152-154`, `RootParameters.lean:70`, `Density/StepGates.lean:37`, `CubeFree/Second/Provider.lean:309-316`, `SideInstance.lean:57-77`, `ConcreteWindow.lean:87,140`, `Side.lean:66,130,166` | `StepGates.kappa : D.κ = 3/4`, `small_price` and the *small-branch* leaf `nativePrice (3/4)` | a, formal | keep at 3/4: the small branch is priced at 3/4 for **every** step and is weaker than κ'; `Provider.frame_leaves` takes `hleaf : PricedPackedSource D.price …` generically **[I: not compiled]** |
| 5 | `P76/FourthPower/IncumbentInput.lean:16-30` and its users `MixedFirstIntegratedWindows.lean:249`, `MixedNativeFloor.lean:127`, `RepairedRootParameters.lean:201`; `Parameters.lean:16,60-63` (`incumbent := 8747759/10^7`, only the sanity constraint `theta < incumbent`, the pre-PR-74 record) | PR 74/76's fourth-power chain that makes the initial face `G(0.99999, 3.72, 0.06)` | a, but irrelevant | the native chain forgets its start: after 30 steps `L−L* = 6.4e-5` whatever `L₀` (3.72 vs 3.7117) |
| 6 | `S83/Density/Price.lean:25-27` (`densQ` clip), `:52` (`highSup` over `[q, 3/4]`), `Source/HybridGates.lean:72,119` (`gQUpper`, field `q_upper`), `:167,179,193` (`density_slope_ge`, `highJ_mono*` on `ν ≤ 3/4`), `Density/Leaf.lean:145,218,294` | HIGH range `ν ∈ [q, 3/4]`, `q ≤ 3/4` | a, **qual., non-binding** | `highTerm` is decreasing in ν (`J` increasing, `high_deriv` gate), so the HIGH sup sits at ν = q and the cap never matters. `q_upper` reserve ≥ 2.5e-3 (step 1), the binding gate is `high_at_q` at every step. Chains with `qmax = 3/4` and `qmax = κ'` are identical to 1e-8 in B ([R] `logs/new_f065*.jsonl`) |
| 7 | `S83/Density/LeafHigh.lean:107`, `LeafHighEnergy.lean:43,109,130,148,186`, `LeafRows.lean:280,297`; `HC/Cycle61/Density/FixedDensity.lean:25,57,64,73-82`, `ActualZeros.lean:27,46,49,78,121` (Collet Lemma 2.1: `33/40 ≤ a ≤ 7/8`, `rawZeroBin … (7/8)`) | upper end of the zero bin; `ρ(ν) ≥ 2/7 > 1/6` for summability (`unmarkedDensity_ge_two_sevenths`, FixedDensity:80-82) | a, **qual.** | `a ≤ θ_I ≤ 7/8` satisfies it; the count exponent `ρ(2a−1)` does not depend on the top of the bin |
| 8 | `S86/Return/Endpoint.lean:38-46` (`natural_cap_return`), `S86/Return/Constants.lean:21` (`naturalK := 9/2`), `FinalScheme.lean:14-16`; `S83/ReturnD/Schedule.lean:46,48,50` (`Λ_P ≤ 9/2`, `small_plain_global`, `incumbent : kappa ≤ naturalκ`), `PhysicalDirect/Geometry.lean:6,71`, `ClippedCapacityDamping.lean:21,32`; `HC/Record1252270103Return/CountScheme.lean:9-12` (`naturalκ ∈ [7/10, 3/4]`) | the return's natural cost `K = 6·naturalκ` | a, **qual.** | exact toolchain: θ\* identical to 1e-9 for K ∈ [4.2, 4.6] (both window families, 3 face sets); K = 4.8 hurts (+1.6e-4). `K' = 4.48747` changes nothing, the guards of the binding window are slack |
| 9 | `S83/ReturnD/Schedule.lean:51-54` (`δ ∈ Icc 0 (3/4)`), `GenericScalar.lean:110,127` (`hupper : β ≤ 7/8`, unused in the proof), `GenericFeedback.lean:17-40` + `HC/Record12518109Return/CountingBridge.lean:20-23` | δ-range of the row cover; feedback transport κ = 2θ−1 → 2β−1 with Lipschitz constants 1/50 (new), 1/8 (old), `5/216` (envelope) | a, **qual.** | shrinking the cover box to `δ ≤ 2θ_I−1 = 0.7479` changes θ\* by 0.0 (binding δ\* = 0.4415; a box `δ ≤ 0.43` would, `−4.5e-6`, but is below δ\*) |
| 10 | `S83/ReturnD/Transport/Transport/{SmallTail,PhysicalSmallTail,CanonicalRayCube,CanonicalCubeReduction,NormalizedTransport,HighApproximation}.lean`, `Transport/FinalFixedHigh.lean:31,71,114`, `ReturnD/PhysicalDirect/MomentGates.lean:49,54`, `ReturnD/TransportGeometry.lean:19-26` (`BoundsN`: `θ < 7/8`, `small_saving : 7/100 < …`) | `Z^((7/8) − (4+b)/6 − S + 8e)` tail exponents with `a ≤ 7/8` | a (qual.) / b | `NormalizedTransportSaving.lean:96-97` proves `7/8 − (4+b)/6 − S + 8e + ν ≤ β − (4+b)/6 − σ` by `linarith [small_saving, theta_lower]`: truly needs `S ≳ 7/8 − β ≈ 1e-3`, `BoundsN` demands 0.07 (actual `S` = 0.0732): non-binding by 70×; replacing 7/8 by θ_I would only add 1e-3 of unused slack |
| 11 | `S86/Return/Constants.lean:29,36` (`kappa := 1−2c`, `oldCapacity d = min d (2y−d)/(6·kappa)`) | the 'old' branch and capacity use the **target** κ = 2θ−1, not the incumbent | **b** | already "bootstrapped" by construction; enters through the self-consistent θ\* |
| 12 | `NativeGates.principal/secondRef` (`S83/Source/NativeBootstrap.lean:33,35`), `S83/Source/HybridGates.lean:84-91`, `CubeFree/StepData.lean:98-99` (`9/2·sel`) | reference gaps | **b** | `9/2 = (3/2)·3` from `RootParameters.lean:161-163,202` (`lower = (3/2)(P+S+3u−5/6)`, `upperOne − lower = 1 − P − 2S − (9/2)u`); not K |
| 13 | `S83/CubeFree/Second/ProviderGeometry3.lean:37-39`, `ProviderDiag*.lean` `(9/2)^{2/3}` | plain-length slop `log_Z(1/(2/9))` | **b** | none |
| 14 | baseline `BL/…/Detector/FinalAssembly*.lean`, `Hecke/ZeroSupremum.lean:65-70`, `Hecke/CommonProbe.lean:24-27` | `7/8 < β →` is the baseline's own contrary hypothesis | b | it *proves* 7/8; nothing to replace |
| 15 | `HC/Cycle61/Moment/LowBranch/{Incumbent,Main}.lean`, `Physical/InitialCoarse.lean:65` (`original_incumbent`, `PositiveAt … (3/4)`) | the baseline's natural positive moment at κ = 3/4 ("incumbent" here = OpenAI's moment, not the record) | a (qual.) | a fact at κ = 3/4, true regardless; Collet's variant is already valid for κ ≥ 7/10 (`HC/Cycle25/Energy/CertifiedExistence.lean:5,28`; `HC/Record12518109Source/Incumbent.lean:21`) |

### 1.2 Why the density phase is incumbent-free [V]

* LOW rows cost `q·w` per erased slot (`S83/Density/LeafLow.lean`, `UniformLow.lean`), HIGH rows `ν(P+s) − (1−ρ(ν))M`; neither involves κ. The price is `max(q·deletionNeed, sup_{ν∈[q,3/4]} highTerm)` (`Density/Price.lean:122`) and `J(w,ν)` is increasing in ν on `[1/2, 3/4]` (`HybridGates.lean:167-196`), so lowering the top of the HIGH range changes nothing.
* The density chain starts where `q(0)` reaches κ (the native barrier in disguise, `pr83.md` §2.2). Hence κ matters only through *where the density flow starts*.

### 1.3 A correction to an earlier note [V]

`research/upstream/PR75_NOTE.md` says "Sil's native κ stays at 3/4, because the OpenAI certificate requires κ ≥ 3/4". The `3/4 ≤ κ` hypotheses live in the baseline's `Energy/*` stage lemmas (`BL/…/Energy/CertifiedExistence.lean:22,43`, 20 files). They are reached only through `NativeZeroInput.zero_input` (`P76/FourthPower/NativeZeroInput.lean:22-30`, which internally takes `κ := max(3/4, 2β−1)` but whose **statement is κ-free**) and Collet's `original_incumbent`. The slot-deletion half of `canonical_energy` has no lower bound on κ, and Collet already re-proved the certificate for `κ ≥ 7/10` (`HC/Cycle25/Energy/CertifiedExistence.lean:5`). So the native price can be lowered to any `κ' ∈ [7/10, 3/4]` with `2β−1 ≤ κ'`; this is how Collet's own two-stage `seedK → finalK` (`HC/Record1252270103Graph/GraphContract.lean:21-22`, `natural_global_source (K ∈ [21/5, 9/2])`, `Natural.lean:17`) works.

---------------------------------------------------------------------------------------------------

## 2. The new hypothesis and whether PR 86 provides it (question 2)

* **Statement needed [V]:** `OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (4369779/5000000 : ℝ)`, used as `2β−1 ≤ κ'` with `κ' = 3739558/5000000` in `canonical_energy`/`canonical_delete`/`natural_slot_product` (all take `hκ : 2*beta-1 ≤ κ`).
  `beta = sSup (insert (1/2) {s.re | ∃ χ : Hecke Character, 0 < s.re ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0})` (`BL/…/Hecke/ZeroSupremum.lean:10-16`): all characters of the Hecke family (all conductors, ray twists), all heights, pole excluded inside the definition.
* **PR 86's top theorem does not give it directly [V]:** `Candidate.bound` / `QRH.SilDensitySplit.K15.dirichlet_nonvanishing` (`S86/Theorem.lean`) is the **Dirichlet** statement, derived from the Hecke one by `Cycle25.dirichlet_of_hecke` (`S86/Return/Endpoint.lean:61-69`); the Dirichlet statement is weaker (Dirichlet L-functions are base changes; sextic Hecke characters over `Z[ω]` that are not base changes are not covered).
* **It does provide the Hecke form as an intermediate [V]:** `QRH.SilDensitySplit.Return.beta_le_theta_of_source (fun hβ => QRH.SilDensitySplit.K15.final_source hβ) : HeckeZeroSupremum.beta ≤ 4369779/5000000` (`S86/Return/Endpoint.lean:48-58`, `S86/Source/ChainK15.lean:89`). So the plumbing is three lines, with `dependencies: ["density-split-fine-chain", …]` (import of `Submissions.density_split_fine_chain.{Return.Endpoint, Source.ChainK15}`; acyclic; PR 86's own `Return` re-declares PR 83's `QRH.SilDensitySplit.Return` namespace, so the new package must not import PR 83's `Return/*`).
* Strictness: the contrary branch gives `θ_new < β ≤ θ_rec`, hence `2β−1 ≤ κ'` exactly (non-strict).

---------------------------------------------------------------------------------------------------

## 3. Pricing (question 3)

### 3.1 What was modelled

1. **Native barrier / native gates** [V exact + R]: `B3/native_chain.py` re-derives PR 86's 30 explicit native steps (`S86/Source/NativeK15.lean`; recipe: constant `a = 0.120629`, 99 % of the retention-allowed decrement and of the cap-allowed cap) and runs the same recipe with `κ'`. All 14 `NativeGates` are exactly positive; the chain ends at `L = 2.567371` (`L − L* = 6.4e-5`, PR 86: `6.5e-5`), cap 0.139718, so the boot face is `(0.99999, 2.56738, 0.1397)`.
2. **Density chain** [R]: `B3/chain_greedy.py` is the gate replica of `HybridGates` (14 gates, per-step optimal (A, D), ε = 1e-6), with the start face, floor, `q`-cap and ΔL as parameters. Run from PR 86's boot `(0.99999, 2.5715, 0.1397)` it reproduces PR 86's chain (`B` at step 46: 0.9888174 vs the Lean 0.9888151, 2.3e-6). Variants: floor 0.65 / 0.60; `qmax = 3/4` / `κ'`.
3. **Return** [V exact]: the validated toolchain with the chain faces (role split count = chain end, physical = step 37/38), Collet-window/old,C,Pcap (PR 86 set) and Lemma W/six branches (lowered-floor set); θ\* by bisection at 1e-9 with floor-coupled h. Incumbent-dependent return inputs: K (windows, crossover), the δ-cover box, the receipt `incumbent`.
4. **Fixed point** and a **sensitivity scan** in θ_I with the continuum (ODE) faces (`dB/dL = (B − 10/(15−6q))/(L−1)`, `q = 0.999L/(6B−L)`).

### 3.2 The mechanism in numbers [R/V]

The bootstrap shifts the density flow's start by `ΔL₀ = −0.0041` at the same `B = 0.99999`, which saves `s₀·ΔL₀ = 0.0313·0.0041 = 1.3e-4` in B at the start. The flow contracts it slowly (`B3/ode_sens.py`):

| L | B(old start) | B(new start) | ΔB |
|---|---|---|---|
| 2.5673 | 0.9998603 | 0.9999867 | +1.26e-4 |
| 2.4000 | 0.9924605 | 0.9925655 | +1.05e-4 |
| 2.3415 (PR 86 end) | 0.9888934 | 0.9889917 | +9.8e-5 |
| 2.2065 (lowered-floor end) | 0.9788323 | 0.9789163 | +8.4e-5 |

The discrete greedy chains agree (ΔB at the same L: +1.26e-4 at step 5, +1.0e-4 at step 45; `B3/logs/*.jsonl`). With `dθ/dB_C = −5.9e-3`, `dθ/dB_P = −8.0e-3` (B1 §2) the linear estimate is −1.5e-6; the exact price is −1.34e-6.

### 3.3 Exact results

Continuum (ODE) faces (`B3/price_ode_boot.py`): floor 0.65 Collet split 0.873953524 → 0.873952202 (−1.322e-6), single face 0.873954455 → 0.873953149 (−1.306e-6); floor 0.60 Lemma W split 0.873945041 → 0.873943726 (−1.315e-6), single 0.873963550 → 0.873962306 (−1.244e-6).
Discrete chains (`B3/price_chains.py`, `B3/price_chains.json`; best (count, physical) over kc ∈ {70..74}/{44..46}, kp ∈ {36..40}):

| chain | best faces | θ\* |
|---|---|---|
| old, floor 0.65 | count k=46 (L 2.3415, B 0.9888174), physical k=38 (L 2.3815, B 0.9913205) | 0.873954805 |
| new, floor 0.65 | count k=46 (L 2.33738, B 0.9885615), physical k=37 (L 2.38238, B 0.9914781) | 0.873953441 |
| old, floor 0.60 | count k=73 (L 2.2065, B 0.9787244), physical k=38 | 0.873946251 |
| new, floor 0.60 | count k=73 (L 2.20238, B 0.9784525), physical k=37 | 0.873944910 |

(PR 86's own exact faces give 0.873954831 and the lowered-floor scenario 0.873946275, `B1`; the model offsets are ≤ 2.6e-8.) Remaining distance to 0.8739358: **9.11e-6** (was 1.045e-5).

### 3.4 Fixed point and scale

`B3/price_iter.py` (continuum): A: θ_I = 7/8 → 0.873945041; θ_I = θ_rec → 0.873943726; θ_I = 0.873943726 → 0.873943710; stop. B: 0.873953524 → 0.873952202 → 0.873952197. A second stage is worth 5e-9 to 2e-8.
`B3/price_sens.py`: gain (scenario A) for θ_I = 0.8747 / 0.8744 / 0.8741 / 0.8739558 / 0.8737 / 0.8735: −3.7e-7 / −7.5e-7 / −1.13e-6 / −1.32e-6 / −1.64e-6 / −1.90e-6, i.e. **1.04–1.06e-4 per unit K**, linear.

### 3.5 Effects checked and found to be zero

* **K in the return** (`B3/return_side.py`, `return_side_check*.py`): θ\* unchanged at 1e-9 for K = 6κ' = 4.48747 and for every K ∈ {4.2, 4.3, 4.4, 4.45, 4.49, 4.5, 4.6} (Collet and Lemma W windows, PR 86 faces 46/38 and 46/46, lowered-floor 73/38, and the new bootstrapped faces); K = 4.8 gives +1.6e-4 (Collet windows). The guards that contain K (`M_H`, crossover `m_X`, `N`-tail) are slack at the binding window.
* **δ-box** `[0, 2θ_I−1]` instead of `[0, 3/4]`: 0.0.
* **q-cap** `κ'` instead of 3/4 in the density gates: identical chain (V1 = V2); `q_upper` is never the binding gate.
* **HIGH range** `[q, κ']`: no effect (§1.2).

### 3.6 Not modelled

* Lean elaboration of the κ'-priced native step; replay time and memory of a closure that contains PR 86's chain **and** a new 46–75-file density chain.
* The chain is a float replica of `HybridGates` (validated against PR 86's 46 steps to 2.3e-6 in B). The differential old − new is robust (the same replica, same ε), +1.0e-4 ± 0.05e-4 in B at the chain end.
* A genuinely new use of `β ≤ θ_I` (a sharper zero-density statement near the edge of the HIGH range would be new analysis; no file in the closure does this). Re-deriving PR 74/76's initial face with κ' (washed out by the native chain).
* The other levers of `lemmaW.md` §4.3 are unchanged; the bootstrap gain adds to them (−1.32e-6 in both scenarios).

---------------------------------------------------------------------------------------------------

## 4. Precedents (question 4)

**Lewko `2026-10-23-lewko-acyclic-bootstrap-874772906` (PR 70, θ = 437386453/500000000 = 0.874772906)** [V]. `dependencies: ["openai-baseline"]`, Collet's tree vendored (3547 Lean files) plus 113,105 lines of its own (`LW/Lewko/QRH/{Stage1,Stage2}`: each 221 source `Node` files, 224 `Return` + 38 `Admission` files). Two stages of the *same* Collet machinery: `LW/Lewko/QRH/Endpoint.lean`
* Stage 1 at `naturalK = finalK = 11243277/2500000 = 4.4973108` proves `β ≤ 87477291/10^8` (`first_family_beta`);
* `new_natural_cost : 6(2β−1) ≤ 112431873/25000000 = 4.49727492` (ΔK = −3.59e-5) feeds Stage 2, which proves `β ≤ 437386453/5·10^8`.
Changes in Stage 2 vs Stage 1: `c`, count slope `countCL` 3.14793054 → 3.14792403 (−6.5e-6), `physicalLambda` −3.7e-6; the return's `naturalK` constant is **unchanged**. **Gain of the bootstrap step: 4.0e-9** (1.1e-4 per unit K). Over Collet's 0.8747729897 the whole submission gains 8.4e-8, of which 8.0e-8 is the Stage-1 re-tuning (faces `countCL` 3.148132 → 3.147931).
Collet's PR 69 itself is a two-stage bootstrap on our PR 67 (`HC/Record1252270103Bootstrap/Incumbent.lean:11`, `incumbent_beta : β ≤ 174963413/2·10^8 = 0.874817065`; `seedK = 4.49782692 → finalK = 4.4973108`, `GraphContract.lean:21-22`), so 7/8 had already been replaced by the previous record in the Collet-era chain.

Other data points (notes, not re-derived here) [I]: PR 75 (Runbo Li) re-fed Sil's PR 74 (ΔK = −3.6e-3) and gained 6.6e-7 (1.8e-4 per unit K; there K entered through Collet's windowed return, which the all-shift return of PR 76/83 no longer has, §3.5); PR 72 (Das) 1.64e-6 from a 21k-node graph, re-feed ≈ 1e-8 (`LOG.md` 1098-1106, 90-95, 1573-1577).

**Sanity check:** the Collet-era chains give 1.1e-4 (Lewko) to 1.8e-4 (PR 75) per unit K; the density chain gives 1.05e-4. With ΔK = −0.0125 that predicts −1.3e-6 to −2.3e-6; the direct computation is −1.34e-6. The result is not an artefact of the replica.

---------------------------------------------------------------------------------------------------

## 5. Lean cost (question 5) [I]

Only if tracks A1–A3 (lowered floor, role split, regenerated return) are executed anyway and the remaining distance becomes ≲ 1.3e-6.

| item | size | note |
|---|---|---|
| κ'-priced native step: `nativeData'` (`κ := 3/4` kept for `StepGates.kappa`, `price := parentPrice κ'`), `native_retention_aux'`, `native_ledger'`, `native_reference'`, `stepGates_of_native'` (copy-edit of `S83/CubeFree/StepData.lean:180-390`) | ≈ 200 lines | κ-free helpers (`native_cap_aux`, `native_defect_aux`) are imported |
| `native_priced_source'` (`Leaf/Native.lean`, 154 lines), `parent_priced_source'` (`Leaf/Parent.lean`, 260 lines; `canonical_partial_delete` already takes κ), `native_leaf'` (`Assembly/Leaves.lean:55-88`), `native_step'` (`Step.lean:40-52`), `NativeGates'` (+30 explicit steps) | ≈ 300–600 lines | replace `(3/4)` by `κ'`, `native_kappa_bound` by `hκ' : 2β−1 ≤ κ'` |
| bootstrap plumbing (§2) | ≈ 10 lines | |
| native-chain generator (30 steps) | Python, `B3/native_chain.py` is a prototype | |
| density chain | **all** HybridK files regenerated from the new boot face (46 files at floor 0.65, ≈ 73 at 0.60; PR 86's are 66 KB each, 3.06 MB for 46) | PR 86's files cannot be reused: they start at `L₀ = 2.5715`. Same generator as A1 |
| return | regenerated rows/admissions for the shifted faces | same as A3 |
| reuse | `Second/*` (18.9k lines), `Density/*`, root chain, `diag_supply`, `contrary_raw_side_provider` | generic in `StepGates` **[I: not compiled]** |
| closure | PR 86's 7813 files / 70.3 MiB + new files; caps 16384 files / 128 MiB (`process.md` §2.2, §4) | fits |

Effort: 1–2 days of agent implementation plus Lean runs (one at a time) on top of A1–A3; a full replay of the closure is the unknown (12 h budget). Risk: moderate (copy-edit of ledger proofs, no new mathematics). Value: −1.3e-6.

---------------------------------------------------------------------------------------------------

## 6. Verified vs inferred

**Verified (read in Lean/paper or computed exactly):** the table of §1 (every site, class and line); that the analytic native cost is `κ ≥ 2β−1` with no lower bound (`canonical_energy`, `natural_slot_product`); that the density price, gates and certificates are independent of the HIGH cap; that `Hecke β ≤ θ_rec` is a theorem inside PR 86 and the Dirichlet theorem is weaker; the exact return is flat in K ≤ 4.6 and in the δ-box; the 30 native steps for κ' pass all gates exactly; exact prices of §3.3–3.4; Lewko's stage structure and constants.
**Replica ([R]):** the density chain (float gates), validated against PR 86.
**Inferred ([I]):** that the κ'-priced native step plugs into the unchanged `Second/*` provider (signatures `Provider.frame_leaves:309`, `SideInstance:57-77` read, nothing built); the Lean line counts; the replay time; PR 72/75 gains (taken from earlier notes).

## 7. Files

`$SCRATCH/analysis/B3/`: `closure86.py/.json` (import closure), `ode_sens.py` (flow sensitivity), `native_chain.py` (native recipe), `chain_greedy.py` + `logs/*.jsonl` (discrete chains, 5 runs), `price_ode_boot.py`, `price_chains.py/.json`, `price_iter.py`, `price_sens.py` (exact pricing), `return_side.py`, `return_side_check.py`, `return_side_check2.py`, `final_check.py` (return-side incumbent effects), `lewko/` (extracted Lewko tree).
