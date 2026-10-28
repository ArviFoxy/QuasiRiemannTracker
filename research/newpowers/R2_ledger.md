# R2 — Ledger of amplifiers: generalised chain steps, combination law, and pricing on PR 83's density step

Date 2026-10-28. Python only (no `lake`/`lean`; nothing committed, pushed or posted). Scripts and raw output: `research/newpowers/r2/` (section 8).
Siblings: `R1_algebra.md` (exact Gauss identities over ℤ[ω], 20 605 numerical comparisons, used below), `R3_return.md` (return side).

**Rule followed.** Earlier notes (`mixed-step/ADVERSARIAL_REVIEW.md`, `MIXED_STEP_LEMMA.md`, `B2_source_slope.md`, `lemmaW.md`) are treated as hypotheses; every
ledger entry below is re-derived from Lean statements and the exponent model of section 2.1. That PR 83 pays `6 = 4 + 2` shows what *its proof uses*; whether a smaller cost is
possible is decided in section 2.4 (it is not, for twist-free transfers) and section 4 (cheaper types exist only for twisted transfers, which have no source theorem).

**Tags.** **[L]** theorem read in a Lean file (file:line; "built" = an `.olean` exists under `/home/user/lean-env/qrh/.lake/build/lib/lean/Submissions/…`; I did not recompile and did not re-check axioms).
**[D]** my own derivation from [L] facts + the exponent model (checkable by hand). **[N]** numerics (script named). **[R1]**/**[R3]** taken from the sibling reports.
**[H]** needs an analytic lemma that is not in the library.

**Path shorthand** (all under `/home/user/lean-env/qrh/Submissions/`): `S83/` = `sil_density_split_20261026/`, `COL/` = `hailey_collet_1252270103/`,
`MS/` = `arvi_mixed_step/`, `RMS/` = `arvi_repeated_marks_on_sil_face_20261025/`. `P69/` = `/home/user/ext/hillclimb/paper69/`.

---

## 0. Verdict (read this first)

1. **Rigidity [D, on R1's identities].** A twist-free amplifier that peels a block `Dᵐ` (`0 ≤ m ≤ 5`, `m = 0` = pool prime) off the columns has scale cost
   `c = 2m + s ≡ 0 (mod 6)`, hence **`c = 6` for every `m`**; the RAW room is `e = 1` for `m ≤ 1` and **`e = 2` for `m ≥ 2`**; the width it removes from the parent is `r = 0` (pool) or `1`
   (per unit of block volume `d = log_U #{D}`). The design space is {pool (1,6,0), simple block (1,6,1), squared-or-higher block (2,6,1)}. `6 = 4 + 2` is the case `m = 1`; the squared block
   pays the same 6 as `2·2 + 2`. No twist-free amplifier is cheaper in `c`.

2. **The doubled block `D²` (m=2, k=2) has twice the room at the same cost [D].** Its residual is *the same simple family at the same radius* as the residual of the simple `D⁴` transfer applied to a
   simple family of equal volume (section 2.3), so `c = 6` is forced; but `g(D²,h) ≠ 0` only for `D ∥ h` (R1; Lean `square_row`), so the Cauchy–Schwarz runs over a divisor-bounded set
   (Lean `collision_family_energy_div`, built): `E_full ≤ U^{−2d}·E_res` instead of `U^{−d}·E_res`. **The frequency sparsity is a gain, not a cost**: radius `+2d` instead of `+4d`,
   no count `W`. Unit LOW payment at the floor wall `(q,β) = (0.6, 0.444)`: **`+1.001` vs `+0.001`** for the simple block (the `0.001` is the `f = 0.999` slack; the simple block sits exactly on its barrier).

3. **No current source supplies squares [D, L-backed].** Collision columns have relative volume `U^{−w_C}` and are absorbed by the restoration induction (`RestorationCollisionEnergy`); PR 83's cube-free squares live in the
   *common* support, not in the selectable block; "repeated marks" is a HIGH-count device, not squares in the Gauss columns. A positive-density doubled slot is a *new source family*;
   section 3.3 gives what it needs and how little of it is needed (≈ 1.3 % of the transferred width, ≈ 1e-3 absolute `log_U` in the object, consumed along the chain).

4. **Twisted types [D, partly H].** A twist of conductor `N(D) = U^d` is not a ray label of the fixed modulus over which `ActualLow` quantifies (`∀ rayM … ∃ C, ∀ᶠ Z`), so a twisted residual
   has no source theorem. Lean's route (`twistDict`) turns the twist back into a dilation = the canonical type (c = 6). Bounding the twisted residuals one by one loses the count `W`:
   idealised `(e,c,r)` = `D¹`: `(0, 2+j, 1)`, squared: `(1, 3+j, 1)` (table in section 4). `D¹` with the **quadratic** twist is `(0,3,1)`: payment `−0.20` — dead; `p³`, `p²` pools: `−0.80`, `−0.53` — dead.
   The squared twisted types `(1, 3+j+κ, 1)` are **dominated by the canonical `(2,6,1)`** for every conductor charge `κ ≥ 0` (payment `0.80 − 0.27κ` vs `1.00` at the operating point). The only twisted type that would beat the simple block is
   `D¹` cubic with `j = 0`, `(0,2,1)` (payment `+0.067 − 0.27κ`, no squares needed), and it needs a conductor-uniform source theorem (lemma T, section 4.5) with `κ < 0.25` — implausible.

5. **Pricing with the exact Lean-return toolchain (floor 3/5, role split) [N].** Baseline chain: θ = 0.873945041 (continuum), 0.873946250 (ΔL = 0.005 discrete); bar 0.8739358.
   Distance to the bar in single-knob currencies (continuum): «DISTANCE_SENTENCE». Full doubling saturates the return's transport box at θ = 0.8739166667 (−1.9e-5 vs the bar).

6. **Ranking (section 6).** (1) native doubled-slot source with the doubled transfer: clears the bar at ≈ 1.3 % doubled share; all ingredients of the *step* are algebraic and mostly in the library, the *source* and the return accounting are new.
   (2) conductor-uniform twisted source theorem (lemma T): only `D¹`-cubic `(0,2,1)` could profit, and only for a conductor charge `κ < 0.25`; squared twisted types are dominated by (1). (3) knob-level improvements of the simple chain (f → 1 gives −8e-7).
   Dead: pools of any power, `D¹` twisted types with `j ≥ 1` (including the quadratic one), `D²` discounts in pools.

7. **Not settled (section 7):** terminal gate charges for doubled units; how a doubled slot is counted in the face (`r = 1` vs `2`); the return-side cost of carrying doubled slots in the final object; the RC3 reading for `m = 3`.

### 0.1 Status of each conclusion (Lean vs own derivation)

| conclusion | status |
|---|---|
| simple block `(e,c,r) = (1,6,1)`; unit payment `1+q−6qβ`; `6 = 2a−k` arithmetic | **[L]** PR 83's own constants (`envelope_identity`, `ds_defect_aux/ds_low_aux/ds_high_aux`, `HybridGates`); the *reading* of `e, c, r` as ledger entries is my formalisation [D] |
| pool `(1,6,0)` | [L+] pool identity in Collet's tree / paper (CA3–CA6), R1 §5; the ledger entry is [D] |
| squared-block Gauss identity, support `D ∥ h`, norm `√N`, divisor-bounded CS | **[L]** `square_twist`, `square_row`, `square_gauss`, `collision_family_energy_div` (built) |
| doubled block `(2,6,1)`, "same residual", rigidity `c = 6`, `e ≤ 2`, `r ≤ 1` | **[D]** on [L] ingredients and [R1] identities; **not** a Lean theorem |
| absence of positive-density squares in the pipeline | [D] on [L] (restoration, correlation vanishing, `UnitFaceSource` quantifiers) |
| twisted residual not covered by `ActualLow`/`UnitFaceSource`; dictionary re-creates the dilation | **[L]** (quantifier order, `twistChar` conductor `N(A)`) + [D] |
| idealised twisted ledgers `(e_ind, c, r)`, break-even `κ*`, lemma T | [D] / [H] |
| mixture law, gate changes, native barriers | [D] (algebra on the three [L] lemmas; symbolic check `ledger.py`) |
| prices, thresholds, capacity scan | [N]: exact-return toolchain of B2/`lemmaW` (not Lean-checked here) + replicas of `HybridGates` |

### 0.2 The inequality that fails, by how much, and what would rescue it

| candidate | exact inequality that fails | by how much | rescue |
|---|---|---|---|
| PR 83/86 chain (simple block) | the unit payment `1 + q − 6qβ` equals only the slack `1−f = 0.001`, so the LOW density is pinned at `q_∞ = f·L/(6B − L)`, which reaches the floor `3/5` at `L = 2.2031` (`B = 0.97855`): the chain cannot go below | θ above the bar by `+9.24e-6` (continuum) / `+1.04e-5` (discrete); the wall must reach `L = 2.1859` (−0.0172) | any of: room `e +1.16 %`, scale `c −0.69 %`, width `r +1.7 %`, slope `s₀ −5.3 %`, «DTHR_FLOOR_RESCUE»; `f → 1` only `−8e-7` |
| doubled block `(2,6,1)` | **availability**, not the step: doubled mass `u_dbl > 0` in the object | `u_dbl = 0` in every current source; need `≈ 1.1e-3` in total (`φ ≥ 1.31 %`), or `≈ 5e-6` per step (section 5.6) | a construction with squared-prime slots + the return-side accounting (D8, D9) |
| `D¹` with the quadratic twist `(0,3,1)` | `π = q(1 − 3β) ≥ 0` | `−0.20` per unit `d` at the operating point (`−0.125` at the start) | `e ≥ 0.2` (recover 20 % of the count `W`), or `c ≤ 2.25` instead of 3 |
| `D¹` with the cubic twist, `j = 0`, `(0,2,1)` | conductor charge `κ < κ* = 0.25` | natural `κ ≈ 1` [inference: the dual length grows with the conductor] | lemma T with `κ < 0.25` |
| twisted squared `(1, 3+j+κ, 1)` | `π ≥ π_canonical = 1.00` | `π ≤ 0.80 − 0.27κ` | none (dominated) |
| pools `p³`, `p²` `(0,k,0)` | `π ≥ 0` | `−0.80`, `−0.53` | none (`e = r = 0`) |
| Lean dictionary route for any twisted type | to be cheaper than canonical it would need `c < 6` | it returns `c = 6` (row shift `N(A)`) | a twisted source theorem (lemma T) |

---

## 1. What the Lean says (anchors)

| fact | where [L] |
|---|---|
| pool identity `g(u,p⁶h) = 1_{p∤u} g(u,h)`; pushforward `(p,h) ↦ p⁶h`, radius `+6a`; average `1/P` | `P69/sources.tex` (CA3–CA6), `P69/foundations.tex` (131), (136); R1 §5 |
| first Poisson block: explicit weights `(q_aq_b)^{-1/2}` times *normalised* Gauss sums `𝔤`, prefactor `H₀/(V q_e √q_r)` | `P69/foundations.tex` (120), (126) |
| MAIN radius `μ = 2A − c − d + R + E − M + (d−c)₊ + 6a + ω` (fixed by the first transform of the whole input) | `COL/Cycle61/Physical/InitialMass/SecondHighPayment.lean:21` (`actual_main_radius_power`) |
| coordinates `x₀ = −a + (μ − (A−c)) + (g₂−t₂−b₂)`, `x₁`, `x₂ = M − R − (c−d)₊ + L_c − 6a − ω + ε`, `x₃ = A − c − b₂` | `COL/Cycle61/Physical/InitialMass/SecondHighCoordinates.lean:20-33` (`actualHighCoordinates`) |
| `x₀ + x₁ + x₂ − labelSide(A) − labelSurplus = rawExcess a …` (A cancels) | `COL/Record12518109Raw/RawWeight.lean:23` (`actual_raw_coordinate_identity`) |
| child scale `x₂ = F − δ − ρ`, independent of the volume | `COL/Record1252270103Source/Coefficient/RegularLowRetainedRadial.lean:23` (`label_radial_coordinate`), `COL/Record1252270103Finite/SourceFormulas.lean:21` (`sourceF = 1 − 6·sourceA`) |
| `D⁴` identity, fifth-free columns, all non-unit cases: `gaussRow a (D⁴k) = (idealRowHom D (span a))²·gaussRow a k` | `RMS/FourthPower/GaussTransfer.lean:98` (`normalized_fourth_power`) |
| selected-row fourth-power transfer, `N(D⁴k) = N(D)⁴N(k)`, D-Cauchy | `S83/CubeFree/Second/FourthTransfer.lean:35,64,71` (`selected_row_fourth_one`, `fourth_scale`, `d_cauchy`) |
| `2a − k + q_C = 1 + t − 6u` for `a = A−c−u`, `k = K+4u` (`ring`); price function `D.price.f g.w g.PC g.s g.H` takes `H` as an argument | `S83/CubeFree/Second/Side.lean:36` (`envelope_identity`), `large_side_exponent` |
| LOW defect `F ≤ (L₀−L)v + (6B₀−L₀)u`; LOW `qF ≤ L₀(u+ε/16)`; HIGH `ν(P_C+s) − k(1+t−6u) ≤ u`; `q(6B₀−L₀) ≤ L₀` | `S83/Density/StepGates.lean:122,134,152,87` (`ds_defect_aux`, `ds_low_aux`, `ds_high_aux`, `dsDens_overshoot`) |
| gates `dens`, `packed = 1−6u`, `highJ`, `gRetainedCap/Width`, `gPrincipal`(9/2), `gSecondRef`(9/2), `gSecondDiag`(4), `gRefUpper`(3), `HybridGates` | `S83/Source/HybridGates.lean:48,58,62,71-94,114` |
| squared block: `gaussRow(d²m, dH′) = idealRowHom(d³)(span m)·gaussRow(d², dH′)·gaussRow(m, H′)` (the sign enters squared); `gaussRow(δ²,·)` vanishes off `δ·O`, norm `≤ √N(δ)` | `MS/Collision/SquareGauss.lean:198` (`square_twist`), `:164` (`square_row`), `:81` (`square_gauss`); built |
| divisor-count Cauchy–Schwarz over colliding primes, with factor `N(p_x)` and the twisted residual at `H′` | `MS/Residual/CollisionWeight.lean:34` (`collision_family_energy_div`); built |
| twist absorbed into the Hecke character, conductor `≤ N(τ.modulus ⊓ 12)·N(fixedBadMask)·N(72)·N(A)` (`A = δ³`: grows by `N(D)³`); dictionary `twistDict` | `MS/Collision/CollTwist.lean:27,60`, `MS/Collision/TwistDict.lean`; `MS/Residual/CollisionTransfer.lean:195` (`famEnergy_elim`) |
| what the source theorem quantifies: `∀ rayM H … ∀ η η₀ Q, ∃ degree controls C, ∀ᶠ Z, InitialAffineAt …`; `ActualLow` = zero-maximum `< a+2e` for every `θ ∈ RayQuotient.Characters M H` | `COL/Record12518109Existence/UniformSource.lean:19` (`UnitFaceSource`), `COL/Cycle61/Moment/LowBranch/Gate.lean:19` (`ActualLow`) |
| second correlation of cube-free columns with unequal multiplicities vanishes | `S83/CubeFree/Second/FirstDivisor.lean:208` (`idealCorrelation_cubefree_unequal_zero`) |
| collisions are removed by restoration, not amplified | `S83/CubeFree/FP/RestorationCollisionEnergy.lean` |

Everything not in this table is [D] or [N]. In particular the generalised entries `(e,c,r)` of section 2 are **not Lean statements** for `m ≥ 2`; for `m = 1` they are PR 83's own constants.

---

## 2. The ledger, re-derived and generalised

### 2.1 Exponent model (what is used, what it rests on)

Exponents are `log_U`. A family has **volume** `V = U^A` (number of terms) and column **norm** `U^α` (`q_u`); for simple slots `α = A` (a product of one prime per slot has norm = volume). A block `Dᵐ`
with `W = U^d` choices of `D` has volume `d` and norm `m·d`. MAIN error `E(F;μ) := (H₀/V_F)·𝓜_F(μ)`, `𝓜_F(μ) = Σ_h Ω(Nh/U^μ)|Σ_u b(u) q_u^{-1/2} 𝔤(u,h)|²` with the *true* weights `q_u^{-1/2}` of
(120) and normalised Gauss sums `𝔤 = g/√q_u` (R1's `gaussRow`). The target of every step is `E ≲ U^{M}` (fixed budget). [L: (120), (126), (127) of `P69/foundations.tex`.]

* **Room `e`.** A transfer proves `E_full ≤ U^{−e·d}·E_res(μ′)`, where `E_res` is the error of the residual family at the *pushed-forward* radius `μ′ = μ + s·d`. `e` = volume saving (`V = W·V_res` gives `U^{−d}`)
  plus the Cauchy–Schwarz gain when the block scalar is supported on a thin set. [D]
* **Scale cost `c`.** The residual's child (second-transform) size is `x₂′ = 2α′ − μ′ + const`, which is *independent of the volume* (Lean: `x₂` free of `A`; the first radius `μ` contains `2α`,
  so `2α − μ` is a constant `σ`). Residual columns have norm `α − m d`, radius `μ + s d` ⇒ **`x₂′ = x₂ − (2m + s)·d`**, `c = 2m + s`. This is the scale handed to the parent
  (`Q′ = 1 − 6a − c·d − δ − ρ`; Lean `modified_deficit_and_coordinate`, `x₂ = F − δ − ρ`). [L for m=1 (`envelope_identity`), D otherwise]
* **Width removed `r`.** Selected slots leave the parent's free slot width: `s ≤ S − r·u` in `ds_defect_aux`. Counted per unit of block *volume*, `r = 1` if the face counts a slot by its prime size;
  if the face counted norm, a squared slot would remove `2`. [D; open for m ≥ 2]
* `μ` itself cancels in `x₀ + x₂` (Lean RC3). Everything the step needs is therefore `(e, c, r)`; the three Lean lemmas `ds_defect_aux/ds_low_aux/ds_high_aux` turn them into gates (section 5.2).
* *Check against the earlier notes (re-derived, not trusted).* For the simple block I reach `e = 1, c = 6` independently of `ADVERSARIAL_REVIEW` (its O1): `actual_main_radius_power` makes `μ` a function of the nominal scale `Z^A` of the **whole input**, and `label_radial_coordinate` makes the child scale `x₂` independent of the volume,
  so the residual enters only through the pushforward (`+4d`) and its smaller columns (`2·d` in `2α′`); `COLLET_LOW_TRACE.md:142` ("MAIN radius `−2d + 4d = +2d`", i.e. `c = 4`) recomputes `μ` from the residual's volume and is not supported by the Lean. `e = 1, c = 6` is also exactly PR 83's `envelope_identity`.

**Sanity (diagonal) check of the CS/room bookkeeping [D].** With true weights the diagonal of a doubled family is `diag_full = U^{μ}·Σ_D N(D)^{-2}·Σ_n|a|²/q_n = U^{μ−d}·diag_res(0)`
(density `1/N(D)` of `D ∥ h` times `|𝔤|² = N(D)` times weight `N(D)^{-2}`, summed over `W` choices), while the transfer bound is `U^{−d}·diag_res(μ+2d) = U^{μ+d}·diag_res(0)`: the loss relative to the truth is exactly the radius
enlargement `2d` (for the simple block: `4d`). Neither bound undershoots the truth, and `2d < 4d` is the sparsity gain.

### 2.2 The chain of ADVERSARIAL_REVIEW §1 (steps 0–9), generalised to a block `Dᵐ` with residual at `D^j H′`

Notation: `h = D^{m−1}H′` (support `v_D(h) = m−1` exactly, R1), residual evaluated at `D^j H′`, `s = j − (m−1)` the radius shift, `j_free = (4m mod 6) + m − 1` the twist-free exponent (`4, 3, 2` for `m = 1, 2, 3`).

| step (review numbering) | pool `p⁶` | simple `D` (m=1, j=4) | squared `D²` (m=2, j=3) | cubed `D³` (m=3, j=2) |
|---|---|---|---|---|
| 0 original norm | `μ` from the first transform of the whole input; the block is still in the columns (norm `α = A + (m−1)u_dbl`) | same | same, `α = A + u` for a doubled input | same, `α = A + 2u` |
| 1 identity [R1; L: `normalized_fourth_power`, `square_twist`] | `g(u,p⁶h) = 1_{p∤u}g(u,h)` | `g(Dn,h) = ε·g(D,h)·g(n,D⁴h)`; `ε = ±1` is a bounded dilation (norm ≤ 27, R1) | `g(D²n,h) = g(D²,h)·g(n,D²h)`, no sign (`ε² = 1`); `h = DH′` ⇒ residual at `D³H′` | `g(D³n,h) = ε·g(D³,h)·g(n,h)`; `h = D²H″` ⇒ residual at `h` |
| block scalar (size of `𝔤(Dᵐ,h)`) and weight `q_u^{-1/2}` | – | `1`, `D∤h`; weight `N(D)^{-1/2}` | `N^{1/2}`, supported on `D ∥ h`; weight `N^{-1}`; **product `N^{-1/2}`** | `N`, on `D²∥h`; weight `N^{-3/2}`; **product `N^{-1/2}`** |
| 2 Cauchy–Schwarz | Jensen over `P` pool primes: `1/P` | `Σ_D N(D)^{-1} ≈ 1`; the sum over `D` of residual energies has `W` terms; renormalisation `V = W·V_res` ⇒ net `0` [L: `d_cauchy`] | `Σ_{D∥h} N(D)^{-1} ≤ d(h)U^{-d}` (divisor-bounded, no count `W`) [L: `collision_family_energy_div`] ⇒ **extra `U^{−d}`** | same as `m = 2` |
| 3 pushforward | `(p,h) ↦ p⁶h`, bounded fibres, radius `+6a` | `(D,h) ↦ D⁴h`, radius `+4d` [L: `weighted_pushforward`] | `(D,H′) ↦ D³H′`, `N(H′) ≤ U^{μ}/N(D)` ⇒ radius `μ − d + 3d = μ + 2d` | `(D,H″) ↦ D²H″`, radius `μ − 2d + 2d = μ` |
| `s` (radius shift) | 6 | 4 | 2 | 0 |
| 4 second transform (`x₂` robust; `x₀` reading in 2.3 (g)) | `Δx₀ = +5a`, `Δx₂ = −6a` | `Δx₀ = +5d`, `Δx₂ = −6d`, `Δx₃ = −d` | `Δx₀ = +3d` (volume) / `+4d` (norm reading), `Δx₂ = −2·2d − 2d = −6d`, `Δx₃ = −d` | `Δx₀ = +d` / `+3d`, `Δx₂ = −2·3d − 0 = −6d`, `Δx₃ = −d` |
| 5 RAW room `e` | 1 | **1** (review's `e = 1`; `envelope_identity`) | **2** (volume `d` + CS `d`) | **2** |
| 6 scale cost `c = 2m + s` | 6 | **6** `(= 2 + 4)` | **6** `(= 4 + 2)` | **6** `(= 6 + 0)` |
| 7 LOW/HIGH split | rows of the same source | rows of the residual: `ActualLow` for every ray label of the *fixed* modulus (`Gate.lean:19`) | same rows (twist-free form ⇒ no new labels) | same |
| 8 erasure, passed width | `b − f` | `b − f − d` (`r = 1`) | `b − f − r d`, `r = 1` (volume) or `2` (norm) | same |
| 9 parent call | `G(B₀,Λ₀,h₀)` at `U^{Q′}` | `Q′ = 1 − 6a − 6d − δ − ρ` | same `Q′` (c = 6) | same |
| `(e,c,r)` | (1, 6, 0) | (1, 6, 1) | (2, 6, 1) | (2, 6, 1) |

Higher `m` (R1): `m = 4`: `v_D(h) = 3`, `j_free = (16 mod 6) + 3 = 7 ≡ 1 (mod 6)` (the pool identity removes `D⁶`, needs coprimality masks), `s = −2`, `c = 8 − 2 = 6`; `m = 5`: `j = 0`, `s = −4`, `c = 10 − 4 = 6`;
`m = 6` is trivial-character (Ramanujan sums), `c = 12`. Columns in PR 83 are cube-free (`PowerFree 3`, Collet `ValuationAtMostTwo`), so only `m ≤ 2` matters for this project.

**The twist dimension of the table.** A twisted variant (residual at `D^jH′`, `j < j_free`) changes the rows as follows. Step 1: leftover `χ_n(D)^{j_free−j}` inside the residual coefficients (a character of `n` of conductor `N(D)`); steps 2–3: the same CS, but the pushforward lands at `D^jH′`
(radius `μ − (m−1)d + jd`), and the residual polynomial now depends on `D` (so there is no single pushforward target: the `W` residual energies are summed one by one); step 4: `Δx₂ = −(m+1+j)d`; step 5: `e_ind = [m ≥ 2]` (the count `W` of the one-by-one sum cancels the volume saving);
step 6: `c = m+1+j`; step 7: `ActualLow` is **not** available for the twisted residual (section 4.2); step 8: `r = 1`; step 9 unchanged. The Lean route (`twistDict`) re-expresses the twisted residual as the untwisted one at `D^{j_free}H′`, i.e. returns to the table above.

### 2.3 The doubled block in detail

**(a) Identity and support.** `gaussRow(d²m, dH′) = r³·gaussRow(d², dH′)·gaussRow(m, H′)` with `r = idealRowHom d (span m)`, `r⁶ = 1` [L, `square_twist`: Lean's phase form, residual at `H′` with the quadratic twist `r³`].
Since `gaussRow(m, d³H′) = r^{∓3}gaussRow(m,H′) = r³gaussRow(m,H′)` (unit-scale/dilation identity, `r⁶ = 1`) this is **the twist-free form `g(D²n,h) = g(D²,h)·g(n,D²h)`** with the residual at `D³H′` (R1) — the dilation
lemma at exponent 3 is not stated in the library (only exponent 4, `normalized_fourth_power`) but is the unit-scale identity applied three times [L+]. Support: `gaussRow(d²,·)` vanishes off `d·O` and has norm `≤ √N(d)` [L, `square_row`]. Numerics [R1, `r1/results.txt`]: `|g(D^m,h)| = N^{m−1/2}` exactly at `v_D(h) = m−1` and `0` otherwise (1585 cases, 0 failures; line 21), squared-block identity to 40 digits (line 284).

**(b) Cauchy–Schwarz.** For fixed `h`, `S(h) = Σ_{D∥h} c_D(h) T(D³H′)` with `|c_D| = N(D)^{-1/2}` (weight `N(D)^{-1}` times scalar `N(D)^{1/2}`).
`|S(h)|² ≤ (Σ_{D∥h}N(D)^{-1})·Σ_{D∥h}|T(D³H′)|² ≤ d(h)U^{−d}·(…)`. No count `W` is paid [L: the factor in `collision_family_energy_div` is the divisor bound `B`, not `#T`], and the weights contribute `U^{−d}`.
Only the *upper* bound `‖gaussRow(d²,·)‖ ≤ √N(d)` (Lean `square_row`) and the vanishing off `d·O` are used, so this step is Lean-backed as stated; the exact value `√N` (R1) is only needed for the diagonal sanity check.

**(c) Pushforward.** `h = DH′` with `N(H′) ≤ U^{μ}/N(D)`: **the support shrinks the radius by `d`**; the dilation `D³` enlarges it by `3d`; net `μ + 2d`. Bounded fibres: `(D,H′) ↦ D³H′` has ≤ `d(h″)` preimages.

**(d) Same residual as the simple transfer.** A doubled input of volume `A` has `α = A + u` and first radius `μ_dbl = μ_simple(A) + 2u` (norm-based `2α`). After transferring the doubled block (volume `u`)
the residual is a *simple* family of volume `A − u`, norm `A − u`, radius `μ_dbl + 2u = μ_simple(A) + 4u` — **exactly the residual of the simple `D⁴` transfer of a simple family of volume `A`**. Hence
`E_full,dbl ≤ U^{−2u}E_res` vs `E_full,simple ≤ U^{−u}E_res` with the same `E_res`: same cost `c = 6` (it cannot differ), room `2` vs `1`. [D]

**(e) Gain or cost of the sparsity?** *Gain*: (i) CS over a divisor-bounded set (`−d`); (ii) radius `+2d` instead of `+4d` (this is exactly compensated in `c` by the extra column norm `2m = 4` vs `2`, so it shows
up as the *same* `c`, not as a smaller one). *Cost*: the image set `{D³H′}` is sparse in the ball of radius `μ+2d` (density `U^{−2d}`) and the residual's source theorem bounds the full ball, so the
sparsity is not exploited a second time; exploiting it would need a sparse-row version of the source theorem [H] (the HIGH/LOW analysis is row-by-row over all rows; the bad rows could lie exactly on the multiples of `D`).

**(f) Native penalty / life-cycle.** The packed envelope `H = 2a − k + q_C` uses the residual *volume* `a` and the *norm-based* radius `k`:
a doubled input has `H_native = 1 + t − 2u_dbl` (first radius larger by `2u_dbl`). Transferring `u` of it costs a further `(2+s)u = 4u`: `H_res = H_native − 4u − 6u_simple`. The ledger `c = 6` for doubled units is the
**life-cycle** cost (native `2` + marginal `4`) relative to a simple family of equal volume. Because the price function takes `H` as an argument (`D.price.f g.w g.PC g.s g.H`, gates `H ≥ 0.9`), the faces are uniform in `H` and the
native penalty needs no shift of the start face [L for the signature; D for the conclusion].

**(g) Coordinates (consistency reading).** With the Lean's `x₀ = −a + (μ − (A−c)) + …`, reading `A − c` as the *volume* allowance (the number of terms): `Δx₀ = (s+1)d`: `+5d` (simple), `+3d` (squared);
reading it as the *norm* allowance gives `+(s+m)d`: `+5d`, `+4d`. `Δx₂ = −6d`, `Δx₃ = −d` in both. Only `Δx₂` (hence `c`) and the CS room enter the ledger; the RC3 sum `Δ(x₀+x₂) = −d` (simple) is the review's `e = 1`.
For `m = 2` the norm reading gives `−2d` (= my `e = 2`), for `m = 3` it would give `−3d` while the CS argument gives `2`: **unresolved** whether the Lean's `x₀` is volume- or norm-normalised for non-simple inputs
(the true first-transform weights are norm-based, which favours the norm reading); `m = 3` is outside the cube-free setting, so I use the CS value `e = 2` throughout.

### 2.4 Rigidity (why `c = 6`, `e ≤ 2`, `r ≤ 1` for twist-free amplifiers) [D]

*Claim.* For a block `Dᵐ`, `1 ≤ m ≤ 5`, with the residual evaluated at `D^jH′` (`h = D^{m−1}H′`), twist-freeness forces `j ≡ j_free ≡ −(m+1) (mod 6)`, and then `c = m + 1 + j ≡ 0 (mod 6)`;
since `j ≥ 0` is needed for an integral residual frequency (`j = −(m+1) < 0` would give `c = 0`, impossible), the least admissible choice has `c = 6`: `m = 1..5 ↔ j = 4, 3, 2, 1, 0`.
*Room:* the volume saving is `d`; the only other source in this CS+pushforward scheme is the removal of the count `W`, at most `d`, and it happens exactly when the block scalar is supported on a thin set (`m ≥ 2`). So `e ≤ 2`.
*Width:* `r` counts the block's slots; `r ≤ 1` per unit volume. ∎ Consequences: unit payment `e + qr − cqβ ≤ 2 + q − 6qβ`; any twist-free chain needs `Λ₀ > 6qB₀/(2+q)` (`1.64·B` at `q = ¾`),
`Λ₀ > 6qB₀/(1+q)` (`2.57·B = 18/7·B`) if only `m ≤ 1` is available, `Λ₀ > 6qB₀` for the pool alone.

### 2.5 Per-norm currency

R1's table (corrections used throughout): minimal exact dilation exponent `k(m) = 4m mod 6 = 4, 2, 0, 4, 2, 0` for `m = 1..6`, i.e. **dilation per unit of block norm `k/m = 4, 1, 0, 1, 2/5, 0`**; `g(Dᵐn,h) = εᵐ g(Dᵐ,h) g(n, D^{4m mod 6}h)`;
`g(Dᵐ,h) ≠ 0 ⇔ v_D(h) = m−1` exactly, `|gaussRow| = N(D)^{(m−1)/2}`; `D¹` leaves `(n/D)₂ = ε(D,n)(D/n)₂` (the Dirichlet character of `n` mod `D`, not `(D/n)₂`); the ray sign `ε` is a bounded dilation (`E₀ ∈ {±1, ±λ}`, norm ≤ 27) and
costs nothing in `U`; only `p⁶` is a twist-free pool and `p^k` also selects columns with `v_p(u) ∈ {0, k+1}`.

If doubled slots count by norm in the face (R3: the face counts widths with multiplicity), the right comparison is per unit of norm: simple `(1, 6, 1)`, squared `(1, 3, 1/2)`; with the parent width counted in norm `r = 1`.
Per unit norm the squared block pays `1 + q − 3qβ = +0.80` (operating point) vs `+0.001`: it wins in both currencies. It "beats 6" only per unit norm (`c/m = 3`); per unit volume it ties on `c` and doubles `e`.

---

## 3. Where could squared blocks come from? (Q2)

**3.1 Collision columns in the existing inputs [L + D].** (i) *Slot–slot or plain–slot collisions* (`p_i = p_j`, `p_i | l₁l₂`): a pattern `C` of total width `w_C` forces `D_C | …`, probability `1/N(D_C)` per tuple, so the sub-family has
`V/W_C` tuples: **relative volume `U^{−w_C}`**, `2^{|J|}` patterns, `O(k²)` pairs with overlapping ranges. It is a *separate smaller sub-family* (volume `A − w_C`), not extra capacity inside the parent; even counted as a "doubled share"
its fraction equals 1.3 % only for `w_C ≈ 4.3/ln U`, so at fixed widths it tends to 0 polynomially. With divisor-bounded CS (`collision_family_energy_div`) its energy costs the divisor count instead of `#T`; the twist is absorbed by
`twistChar`/`twistDict` (conductor `N(D)³`, `CollTwist.lean`). Our mixed-step Lean has these lemmas built but not assembled (`LEAN_NOTES.md` (Col): the LOW supply is for one ray modulus fixed before `Z`;
a "LOW twin for twisted dictionaries" is missing — exactly the section 4 obstruction).
(ii) *PR 83's cube-free columns*: `idealCorrelation_cubefree_unequal_zero` kills the second correlation of unequal multiplicities `(1,2)`; squares survive as multiplicity-`(2,2)` **common support** `C, D`, fixed inside each inner sum,
hence in `c, d` of the first-common pair, not in the selectable varying block. (iii) PR 83/Collet remove collisions by *restoration* (`RestorationCollisionEnergy`, induction on the slot count), at zero ledger cost — no amplifier is used.

**3.2 Deliberately doubled slots [L + D].** *Repeated marks* (`repeated-marks/README.md`, Lemma `A_K`): a slot used `K` times in the **HIGH inverse witness**, i.e. products `∏_c Q_i(χ)` of independent prime sums over the same list; the columns are
`p₁⋯p_K` of *distinct* primes with a `1/|pool|` diagonal `p = p′`. The face counts `Λ·width` *with multiplicity* (`hcap` of `finite_physical_pair_affine`, R3 §5.7, [L]): a repeated slot costs `Λ` per copy, neutral for every `K`;
R3 prices a "doubled-copy discount" at 0.91 %. This is a HIGH-count device; it does not put squares into the Gauss columns of a MAIN polynomial. `D²` as the diagonal of `Q²` has mass `1/|pool|` (R3).

**3.3 A native doubled-slot source: what it needs, what it does not need [D, H].**
The object would contain slots `Q₂(χ) = Σ_p ν_pχ(p)²` (columns `p²`, `U^w` choices, norm `U^{2w}`).
* *Not needed:* a HIGH count or LOW erasure bound for the doubled slots themselves. In every step they are **selected for transfer** (review step 7: LOW/HIGH apply to the residual's rows and unselected slots), so the induction
  `G_n(residual) ⇒ G_{n+1}(object)` needs no hypothesis on doubled slots as long as each step consumes the doubled mass present. [D; mirrors `StepData`]
* *Needed:* (i) the families to which the **return** applies the faces must themselves contain the doubled slots — otherwise doubled units never enter a step and nothing improves; i.e. the zero-detecting construction must contain squared-prime slots;
  (ii) enough doubled mass for the whole chain: the object carries the *sum* of what the steps consume (the residual after a step must again be a doubled-containing family for the next step to profit);
  (iii) the selector prefers doubled slots; (iv) the return must carry the doubled slots in its own budgets (R3: faces count widths with multiplicity, a doubled slot's norm is `2w`) — the largest unquantified cost.
* *Amount:* along the baseline chain the per-step transferred width is `u ≈ 0.7e-3 … 7e-3` (sum `0.085` over 74 steps, `results/dch_base_f60.json`). A doubled share `φ* = 1.16 %` (continuum) / `1.31 %` (discrete) of the transferred width crosses the bar,
  i.e. about **`1.1e-3` doubled volume in the object (≈ 1 % of the slot budget `c₀ = 0.1`), ≈ `1.5e-5` per step**; the capacity scan of section 5.6 gives the same order (bar crossed at `UD* ≈ 4.7e-6` per step, `≈ 5.4e-4` consumed in total — half of the share model, 5.6).
  Granularity: the selector takes *whole slots* (mesh `→ 0` as `ε → 0`), and every step consumes its doubled mass (`r = 1`), so the object needs about one doubled slot per step, each of width `≲ UD` — roughly a hundred squared-prime slots of width `≲ 5·10⁻⁶`.
* *Verdict:* the amount is small; what is missing is a construction that contains squared-prime slots, and the return-side accounting, not an analytic ingredient of the step. I found no mechanism in the pipeline that creates positive-density squares
  (plain→slot Buchstab/Ramaré decompositions create simple slots only). Large-sieve side remark: the HIGH count for `Σ_pν_pχ(p)²` would reduce to cubic-character sums (2-to-1 map `χ ↦ χ²`), for which the library has Heath-Brown's cubic sieve — but this is not needed if the slots are always transferred.

---

## 4. Twisted types: `D¹`, `D²`, `D³`, `p³`, `p²` (Q3)

### 4.1 Parametrisation and the ideal ledger [D]

For a block `Dᵐ` with residual at `D^jH′` (`0 ≤ j ≤ j_free`), the leftover twist is `χ_n(D)^{j_free − j}` (order `6/gcd(6, j_free−j)`), a character of the residual columns `n` of **conductor `N(D) = U^d`**.
Scale cost `c = m + 1 + j` (columns `−m d`, radius `−(m−1)d + j d` in `x₂′ = 2α′ − μ′`). Room: if the `W` twisted residuals are bounded one by one (no common polynomial) the count `W` returns:
`e_ind = 1 + [m ≥ 2] − 1 = [m ≥ 2]`; `r = 1`. Pools `p^k`: twist `χ_u(p)^{−k}` and valuation selection (keeps `v_p(u) ∈ {0, k+1}`, R1), `e_ind = 0, c = k, r = 0`.
Payment `π = e + qr − cqβ`; `κ* = (e+qr)/(qβ) − c` is the break-even conductor charge (extra scale cost per unit `d` that a conductor-uniform source theorem may charge before `π < 0`). [`twisted.py`]

| type | j (residual at D^j H') | twist | e | c | r | pi @ q=.60,beta=.444 | pi @ start (q=.75,beta=.389) | kappa* |
|---|---|---|---|---|---|---|---|---|
| D^1 (simple) | 0 | cubic | 0 | 2 | 1 | +0.067 | +0.167 | 0.25 |
| D^1 (simple) | 1 | quadratic | 0 | 3 | 1 | -0.200 | -0.125 | -0.75 |
| D^1 (simple) | 2 | cubic | 0 | 4 | 1 | -0.466 | -0.417 | -1.75 |
| D^1 (simple) | 3 | sextic | 0 | 5 | 1 | -0.733 | -0.708 | -2.75 |
| D^1 (simple) | 4 | none | 1 | 6 | 1 | +0.001 | -0.000 | - |
| D^2 (squared) | 0 | quadratic | 1 | 3 | 1 | +0.800 | +0.875 | 3.00 |
| D^2 (squared) | 1 | cubic | 1 | 4 | 1 | +0.534 | +0.583 | 2.00 |
| D^2 (squared) | 2 | sextic | 1 | 5 | 1 | +0.267 | +0.292 | 1.00 |
| D^2 (squared) | 3 | none | 2 | 6 | 1 | +1.001 | +1.000 | - |
| D^3 (cubed) | 0 | cubic | 1 | 4 | 1 | +0.534 | +0.583 | 2.00 |
| D^3 (cubed) | 1 | sextic | 1 | 5 | 1 | +0.267 | +0.292 | 1.00 |
| D^3 (cubed) | 2 | none | 2 | 6 | 1 | +1.001 | +1.000 | - |
| pool p^1 | - | sextic | 0 | 1 | 0 | -0.267 | -0.292 | - |
| pool p^2 | - | cubic | 0 | 2 | 0 | -0.533 | -0.583 | - |
| pool p^3 | - | quadratic | 0 | 3 | 0 | -0.800 | -0.875 | - |
| pool p^4 | - | cubic | 0 | 4 | 0 | -1.066 | -1.167 | - |
| pool p^5 | - | sextic | 0 | 5 | 0 | -1.333 | -1.458 | - |

(Operating point = the floor wall, `L = 2.2031, B = 0.97855, q = 0.6`; start = `L = 2.5715, B = 0.99999, q = 0.75`.)
Rows with twist "none" are the twist-free types of section 2 (c = 6). `D¹` with the **quadratic** twist (`j = 1`, the cheapest quadratic one) is `(0,3,1)`: payment `−0.20` at the operating point, `−0.125` at the start;
it would need `e ≥ 0.2` (resp. `0.125`), or `c ≤ 1/β = 2.25` (resp. `2.57`) instead of 3, or `β < 1/3` (the chain has `β ∈ [0.389, 0.444]`). Native barrier `L* = cqB/(e+qr)` at `q = ¾`: `D¹` quadratic `3B` (worse than the simple `2.571B`), `D¹` cubic `j=0`: `2B`,
squared quadratic `(1,3,1)`: `1.286B`, cubed cubic `(1,4,1)`: `1.714B`.

### 4.2 What bounds the twisted family in Lean

`ActualLow` (`Gate.lean:19`) requires, for the row `z`, the zero-maximum `< a + 2e` **for every `θ ∈ RayQuotient.Characters M H`**, with `M` fixed *before* `Z` (`UnitFaceSource`: `∀ rayM H … ∀ η η₀ Q, ∃ degree controls C, ∀ᶠ Z`), and the base character `η` also
fixed before `Z`. A quadratic or cubic symbol modulo `D` with `N(D) = Z^d` is not a character of `(O/M)ˣ/H` for any fixed `M`, and `twistChar τ A` (conductor `≲ N(A)`, `CollTwist.lean:60`) is a *new* base character with
`Z`-dependent conductor. **So a quadratic symbol mod `D` is not covered**, and no existing Lean statement charges a conductor cost: the library has no conductor-uniform version.
What exists is the *dictionary*: `twistDict τ A` is the natural row of the same `τ` at the shifted frequency `z = A·w` — the twisted residual is the untwisted source evaluated on the sparse row set `{Aw}` — which
**re-creates exactly the dilation that was avoided** (row cost `N(A)`; for the collision twist `A = δ³`): every twisted type collapses to the canonical twist-free type `(e,c,r) = (1 + [m≥2], 6, 1)` of section 2 in the Lean route.

### 4.3 Why the count `W` cannot be recovered without a new theorem [D, heuristic]

`Σ_D|T_D^{tw}(h′)|²` over the `W` twisted residuals: the second transform turns `E_res` into a child moment over *all characters of the (D-dependent) family*; the child's diagonal is the number of characters,
`W·U^{m′}`, which returns the factor `W`. A large sieve over the twists (`D ↦ (·/D)₂`; Heath-Brown quadratic/cubic sieves are in the library) gives `max(diagonal, trivial)`, which is *no better than the trivial bound* and
therefore useless against the source theorem's strong single-residual bound. A conductor-uniform source theorem with a union bound over the `≈ N(D)` labels of the combined modulus would lose the same `W` again in `ActualLow`'s zero-maximum.

### 4.4 Pools `p³`, `p²`

Idealised `(0, 3, 0)` and `(0, 2, 0)`: payments `−0.80`, `−0.53` (negative for every `q, β > 0`; `e = r = 0`). The pool saving is the Jensen average over a *common* polynomial, which exists only for `k ≡ 0 (mod 6)`;
for `k = 3, 2` the polynomials `S^{tw}_p(h) = Σ_u b(u)q_u^{-1/2}χ_u(p)^{−k}𝔤(u,h)` are different for different `p`, so there is nothing to average. Dead.

### 4.5 The one lemma that would change this (lemma T) [H]

*T (conductor-uniform source).* `UnitFaceSource` for base characters `η·ψ_D` with `ψ_D` a power-residue character of conductor `N(D) ≤ Z^{d}`, `D` in a family of size `W = Z^d`, with the *same* degree/controls and a joint bound
`Σ_D 𝓜^{tw}_D ≲ W·(single bound)`, charging at most `κ < κ*` per unit of log-conductor. `κ*` at the operating point: squared quadratic `3.0`, cubed/squared cubic `2.0`, squared/cubed sextic `1.0`, `D¹` cubic `j=0`: `0.25`;
`D¹` quadratic: none. Status: absent; the constants of `UnitFaceSource` are not tracked in the ray modulus; this is research-level (it is the large-sieve core of the source theorem).
**Even with T the useful range is narrow.** Squared twisted types `(1, 3+j+κ, 1)` have payment `≤ 0.80 − 0.27κ` (`j = 0`) against `1.00` for the canonical squared block, so they are dominated for every `κ ≥ 0` (same at the start: `0.875 − 0.29κ` vs `1.000`);
the twisted types are only interesting where no squares are needed, i.e. `D¹`, and there only `j = 0` (cubic twist, `(0,2,1)`, payment `0.067 − 0.27κ` vs the simple block's `0.001`) survives, for `κ < 0.25`. A natural conductor charge in a large-sieve argument is `κ ≈ 1` (the length of the dual sum grows with the conductor), which kills it.

---

## 5. Combination law, PR 83's step, and the pricing (Q4)

### 5.1 LOW payment and descent for a mixture [D, from `ds_defect_aux`/`ds_low_aux`/`ds_high_aux`]

Types `T` with masses `x_T` (volume), `(e_T, c_T, r_T)`; `H = 1 − Σ c_T x_T`, parent width after selection `S − f − Σ r_T x_T`; `β = B₀/Λ₀`, `X₀ = b + (t−B₀)/Λ₀`:

    LOW :  Σ_T x_T ( e_T + q r_T − c_T q β )  ≥  q X₀ + r                         [PR 83: a(1−6qβ) + d(1+q−6qβ)]
    HIGH:  J(ν) = (1−ρ(ν))(1 − Σ c_T x_T) − ν( B − (Λ−1)w − Σ r_T x_T ) + Σ e_T x_T ≥ 0,   ν ∈ [q, ¾]

*Check against Lean:* `ds_defect_aux` with `H = 1 − c u`, `s ≤ S − r u` gives `F ≤ (Λ₀−Λ)v + (cB₀ − rΛ₀)u`; `ds_low_aux` with price `≤ e u` gives `q[(Λ₀−Λ)v + (cB₀−rΛ₀)u] ≤ Λ₀ e u`.
`(1,6,1)` is PR 83 verbatim; `ledger.py` checks symbolically that `F − [(Λ₀−Λ)v + (cB₀−rΛ₀)u] = 0` and that `2a − k + q_C = 1 + t − (2m+k)u`. The HIGH derivative gate generalises as
`∂J/∂ν ≥ (25/24)(1−cu) − (B − (Λ−1)w − ru)` (the minimum of `−ρ′` on `[½,¾]` is `25/24`).
Payments and scales **add**; there is no synergy between types. **Descent:** some available type with positive unit payment, `Λ₀ > min_T c_T q B₀/(e_T + q r_T)`. The *mass* of the best type is not binding as `ΔL → 0` (LOW needs `Σx_Tπ_T ≥ q ΔL v/Λ₀`, proportional to `ΔL·v`).
Unit payments `π = e + qr − cqβ` along the chain [N, `ledger.py`]:

| L | B | q_∞ | β | pool (1,6,0) | simple (1,6,1) | squared (2,6,1) |
|---|---|---|---|---|---|---|
| 2.5715 | 0.99999 | 0.749 | 0.389 | −0.748 | +0.0010 | +1.0010 |
| 2.34 | 0.98880 | 0.651 | 0.423 | −0.650 | +0.0010 | +1.0010 |
| 2.2031 (wall) | 0.97855 | 0.600 | 0.444 | −0.599 | +0.0010 | +1.0010 |

The pool is never used at the operating point (needs `Λ > 6qB`); a pool term is a pure cost `a(1 − 6qβ)` in the mixture.

### 5.2 Which gates of `HybridGates` change (`S83/Source/HybridGates.lean`, `Density/StepGates.lean`)

| gate / lemma | PR 83 (`e,c,r = 1,6,1`) | general `(e,c,r)` |
|---|---|---|
| `dens`, `densE`, `lowDefect`, `low_identity` | `f·Λ₀A / ((Λ₀−Λ)(1+Dv) + (6B₀−Λ₀)A)`, `f = 0.999` | `min(¾, f e Λ₀A / ((Λ₀−Λ)(1+Dv) + (cB₀ − rΛ₀)A))` (LOW holds for every smaller `q`; `q_upper` forces the cap) |
| `packed` | `1 − 6u` | `1 − c u` |
| `highJ` | `… − (6(1−ρ) − ν − 1)u` | `… − (c(1−ρ) − ν r − e)u` |
| `gRetainedCap/Width`, `gHighDeriv` | `w − u`, `B − (L−1)w − u` | `w − r u`, `B − (L−1)w − r u` |
| `ds_defect_aux`, `ds_low_aux`, `ds_high_aux` | `(6B₀−Λ₀)u`; price `≤ u` | `(cB₀−rΛ₀)u`; price `≤ e u` |
| `gPrincipal`(9/2), `gSecondRef`(9/2), `gSecondDiag`(4), `gRefUpper`(3) | per-unit charges of the transfer (they come from the second-step geometry of the PR 74–83 papers, which is not in the Lean: "arithmetic only") | **not derived** for the squared block [H]. Minimum reserves along the replica of the baseline chain: `0.0088` (principal, at the wall), `0.092`, `0.049`, `0.111`; with a doubled mass `≤ 1.5e-5` per step a charge change of `≳ 600` per unit would be needed to bind, so for the small shares of 5.5/5.6 they cannot. (For full doubling the principal gate does bind, near `L ≈ 1.8`.) The review's O3 ties the zero-frequency/diagonal charge to the radius shift (pool `5` per `a`, transfer `4` per `d`, the `4` of `gSecondDiag`); for `D²` the shift is `2`, so if the other charges are radius-driven as well, doubled units load these gates *less* than simple ones [inference, not checked]. |
| `gQLower/Upper/Floor`, `gHLower` | ½, ¾, 13/20, 9/10 | unchanged (the brief's floor 3/5 is a one-constant change of `gQFloor`) |
| `StepData` price contract, `Selection` | unchanged | unchanged (selector acts on widths) |

### 5.3 ODE, native barrier, slope

Continuum step (`B2_source_slope.md` §1.2, re-derived from the three Lean lemmas): `dB/dL = (B − 10/(15−6q))/(L−1)`, `q = min(¾, f e L/(cB − rL))`, started from PR 86's boot face `(0.99999, 2.5715)`.
Native barrier at `q = ¾`: `L* = cqB/(e+qr)`: pool `4.50B`, simple `2.571B (= 18/7·B)`, squared `1.636B`, mixture with doubled fraction `φ`: `4.5B/(1.75+φ)`. For the simple type the chain stays on `L = 6qB/(1+q)` as `q` falls
(`q = 0.65` at `L = 2.34`, `0.60` at `2.20`). With `q ≡ ¾` the slope is `s₀ = (B − 0.95238)/(L−1)`, a straight line `B = 0.95238 + 0.0303(L−1)` (constant `s₀ = 0.0303`).
[N] `ode_amp.py` reproduces B2 (`B(2.3415) = 0.98889`, `s₀ = 0.0651`, wall(0.60) `= 2.2031`, `B = 0.97855`); `dchain_amp.py` (replica of `HybridGates` with the generalised constants) reproduces PR 86's chain (74 steps to `L = 2.2015`, floor 0.60).

### 5.4 Prices (exact Lean-return toolchain `r3/tc` = `lemmaW/tc`, floor 3/5, role split; `pricing2.price_cd`) [N]

*Role split* (lemmaW §3.3): the count role and the physical-face role of the return may read different faces of the chain, `θ(L_C, L_P) = f(L_C) + g(L_P)`; each row gives the best pair
(count face at `L_C`, physical face at `L_P`; both are faces `G(B(L), L, ·)` of the continuum chain of that row; θ is the exact least value from the 6-branch window toolchain, resolution `1e-9`).
The baseline row reproduces B2's `0.873945041`.

| scenario | wall `L` | `s₀` at L=2.34 / 2.2 / 2.0 (q) | count face `(L_C, B_C)` | physical face `(L_P, B_P)` | θ | θ − bar |
|---|---|---|---|---|---|---|
| PR 83 gate `(1,6,1)`, f = 0.999 | 2.2031 | 0.0654 (0.65) / 0.0847 (0.60) / 0.1116 (0.53) | (2.2031, 0.97855) | (2.3800, 0.99130) | 0.873945041 | +9.24e-06 |
| same, f = 1 | 2.2016 | 0.0652 (0.65) / 0.0845 (0.60) / 0.1115 (0.53) | (2.2016, 0.97849) | (2.3775, 0.99119) | 0.873944247 | +8.45e-06 |
| `e = 1.0116` (doubled share 1.16 %) | 2.1859 | 0.0632 (0.66) / 0.0830 (0.61) / 0.1104 (0.54) | (2.1859, 0.97793) | (2.3625, 0.99075) | 0.873935815 | +1.50e-08 |
| `e = 1.02` (2 %) | 2.1736 | 0.0617 (0.66) / 0.0818 (0.61) / 0.1096 (0.54) | (2.1736, 0.97748) | (2.3525, 0.99051) | 0.873929147 | -6.65e-06 |
| `e = 1.03` (3 %) | 2.1591 | 0.0598 (0.67) / 0.0802 (0.61) / 0.1085 (0.55) | (2.1591, 0.97696) | (2.3400, 0.99018) | 0.873922021 | -1.38e-05 |
| `e = 1.05` (5 %) | 2.1307 | 0.0558 (0.68) / 0.0771 (0.63) / 0.1064 (0.56) | (2.1307, 0.97593) | (2.3800, 0.99306) | 0.873916667 | -1.91e-05 |
| `e = 2` (all doubled), `(2,6,1)` | none | 0.0303 (0.75) / 0.0303 (0.75) / 0.0303 (0.75) | (2.0000, 0.98268) | (2.3800, 0.99419) | 0.873916667 | -1.91e-05 |
| `c = 5.9587` | 2.1867 | 0.0633 (0.66) / 0.0831 (0.60) / 0.1106 (0.54) | (2.1867, 0.97800) | (2.3625, 0.99076) | 0.873935781 | -1.90e-08 |
| `c = 5.9` | 2.1634 | 0.0601 (0.67) / 0.0807 (0.61) / 0.1091 (0.54) | (2.1634, 0.97721) | (2.3400, 0.99013) | 0.873923084 | -1.27e-05 |
| `r = 1.0171` | 2.1881 | 0.0634 (0.66) / 0.0833 (0.60) / 0.1109 (0.54) | (2.1881, 0.97810) | (2.3650, 0.99092) | 0.873935783 | -1.70e-08 |
| `r = 1.05` | 2.1597 | 0.0592 (0.67) / 0.0804 (0.61) / 0.1094 (0.54) | (2.1597, 0.97726) | (2.3800, 0.99264) | 0.873920066 | -1.57e-05 |

(`s₀` and `q` at `L` below the row's wall are the formal ODE continuation with `q` below the floor; the chain stops at the wall, those entries are shown only to compare the slopes. `L_C` is the count face, always at or near the wall; `L_P` the physical face.)

Discrete `ΔL = 0.005` chains (replica of `HybridGates`, `dchain_amp.py` + `eval_discrete.py`; count face among all steps, physical face among `L ∈ [2.2, 2.6]`): baseline (74 steps to `L = 2.2015`) **0.873946250** (`+1.04e-5`);
`e = 1.012`: **0.873936717** (`+9.2e-7`); `e = 1.02`: **0.873930389** (`−5.41e-6`). (`results/disc_eval.log`.)

Sensitivities (continuum): `dθ/de ≈ −8.0e-4` per unit (−8.0e-6 per +1 %), `dθ/dc ≈ +2.2e-4` per unit, wall moves by `−0.0149` in `L` per +1 % of `e`. The discrete `ΔL = 0.005` chain sits `1.1–1.3e-6` above its continuum.
**Box saturation:** when the faces are good enough that the return's `ℓ < 0.171` box (lemmaW: "θ ≥ 0.8739167 is the hard floor of this box", `lemmaW.md:76`) is the active limit, θ stops at `0.8739166667`; a source improvement beyond that
is invisible to the return unless the box is re-widened (a return-side change, outside R2). So `−1.913e-5` vs the bar is the most any amplifier can show with the current return.

### 5.5 Distance to the bar in every currency [N]

<!--THR_START-->
| currency (knob) | baseline | value reaching the bar (continuum) | for the discrete `ΔL = 0.005` chain | change | `dθ/d knob` (bar value) |
|---|---|---|---|---|---|
| room `e` per unit (= 1 + doubled share) | 1.0 | 1.01161 | 1.01312 | +1.16 % | -7.96e-04 |
| scale cost `c` | 6.0 | 5.95875 | 5.95358 | -0.69 % | 2.24e-04 |
| width removed `r` | 1.0 | 1.01705 | 1.01926 | +1.71 % | -5.42e-04 |
| density slope `s₀ → (1−eps)s₀` | 0.0 | 0.0531 | – | +0.05309 | -1.74e-04 |
| HIGH threshold `T(q) → T(q) + dthr` | 0.0 | 0.00407 | – | +0.004075 | -2.27e-03 |
| density floor `q ≥ floor` | 0.6 | (not run) | | | |
| LOW slack `f` | 0.999 | `f = 1` reaches only `θ = 0.873944247` (`−8.0e-7`, 9 % of the gap) | | | |
<!--THR_END-->

Reading: the baseline chain is `9.2e-6` (continuum) / `1.04e-5` (discrete) above the bar; every currency needs a *percent-level* change (`+1.2 %` room, `−0.7 %` scale, `+1.7 %` width removed, `−5 %` density slope), which is also the size of the return-side
demands in `R3` (`−0.9 %` on a slot cost). The doubled share needed is `φ* = e* − 1 = 1.16 %` (continuum) / `1.31 %` (discrete) of the transferred width; with `Σu = 0.085` over the 74 steps that is `1.0e-3` / `1.1e-3` of absolute doubled volume.
Cross-check with `B2_source_slope.md` §0: B2 states that the bar needs `s₀` lowered by `5.3 %` (equivalently `6 → 5.93…5.95`, `10/(15−6q)` up by `0.5…0.6 %`); my independent solve gives `eps* = 5.31 %` and `c* = 5.9587` (B2's `c` used an uncapped `q > ¾`, section 7).
If the face counted a squared slot by norm (`r = 2` for doubled units) the linear estimate `dθ ≈ −(7.96e-4 + 5.42e-4)·φ` gives `φ* ≈ 0.7 %`. `f → 1` is worth `−8.0e-7` only.

### 5.6 Capacity-limited doubled mass (absolute, per step) [N]

Model (`dchain_cap.py`): in each step the first `UD` of the selected width `u(v) = A v/(1+Dv)` is doubled (type `(2,6,1)`), the rest simple `(1,6,1)`; `q(v) = min(¾, f L₀(u + ud)/((L₀−L)v + (6B₀−L₀)u))`, `highJ += ud`, all other gates as in PR 83;
`(A, D)` re-optimised in every step (Nelder–Mead on `s₀`), exact discrete `ΔL = 0.005` chain, count face among all steps with `L ≤ 2.5`, physical face among `L ∈ [2.2, 2.6]`, floor 0.60.

<!--CAP_START-->
| doubled capacity per step `UD` | steps (end `L`) | consumed doubled mass `Σ min(UD,u)` | count / physical face `L` | θ (discrete) | θ − bar | Δθ vs baseline |
|---|---|---|---|---|---|---|
| 0 (baseline) | 74 (2.2015) | 0 | 2.2065 / 2.3815 | 0.873946250 | +1.04e-05 | 0 |
| 3e-06 | 110 (2.0215) | 3.30e-04 | 2.2065 / 2.3665 | 0.873939585 | +3.78e-06 | -6.67e-06 |
| 5e-06 | 114 (2.0015) | 5.70e-04 | 2.2065 / 2.3615 | 0.873935215 | -5.85e-07 | -1.10e-05 |
| 1e-05 | 114 (2.0015) | 1.14e-03 | 2.2065 / 2.3065 | 0.873925286 | -1.05e-05 | -2.10e-05 |
<!--CAP_END-->

Reading. (i) The bar is crossed at **`UD* ≈ 4.7e-6` per step** (linear interpolation between `+3.78e-6` at `3e-6` and `−5.9e-7` at `5e-6`), i.e. about **`5.4e-4` of consumed doubled volume** over the ≈ 114-step chain (0.5 % of the slot budget `c₀ = 0.1`) —
half of the `1.0–1.1e-3` of the proportional-share model, because the re-optimised `(A, D)` lets the doubled units carry the LOW payment with a much smaller simple width (at `q = 0.6` a simple unit costs `c(1−ρ) − νr − e = 1.56` in the HIGH bracket, a doubled one `0.56`).
(ii) Diminishing returns: `Δθ` vs the baseline is `−6.7e-6, −1.10e-5, −2.10e-5` for `UD = 3, 5, 10 ×10⁻⁶`. (iii) Shape of the chains: in the early and middle steps they look like the baseline with a higher `B` (`B(2.3015) = 0.98658 / 0.98690 / 0.98765` vs `0.98609` for the baseline);
below `L ≈ 2.17` the doubled capacity alone carries the chain along the floor (`u ≈ UD`, `s₀ ≈ 0.098`, `q` = floor) — this extension is not used, the best count face stays at `L = 2.2065` and the gain is the higher `B` there (`0.97936 / 0.97976 / 0.98072` vs `0.97872`).
(iv) Upper-bound character: the capacity is re-supplied every step (the object must carry the sum, section 3.3), terminal charges are unchanged, `r = 1`, and nothing is charged on the return side.

### 5.7 Caveats on the pricing model

(1) The doubled-share model gives every transferred unit the *life-cycle* ledger `(2,6,1)` or `(1,6,1)` (section 2.3 (f)); the faces are uniform in `H`, so the native penalty is already in the per-unit `c`.
(2) The per-step capacity model re-supplies the doubled mass every step; the induction of section 3.3 needs the *sum* in the object (≈ 110× the per-step value for the capacity chains).
(3) The return-side cost of carrying doubled slots in the final object (R3, `2Λ`-type accounting) is not in any number here.
(4) Terminal gates and the `r = 1` vs `2` convention (section 2.1) are not derived; the discrete chains keep the PR 83 terminal charges (4.5/4.5/4/3) for all units.

---

## 6. Ranking (by Δθ and plausibility) and the lemma list (Q5)

| rank | candidate | Δθ (vs baseline 0.873946250 discrete) | plausibility | what is missing |
|---|---|---|---|---|
| 1 | **native doubled-slot source + doubled transfer** `(2,6,1)` | up to `−2.96e-5` (cap `0.8739167`); bar at `φ ≥ 1.31 %` | low: a construction + return-accounting question (the mass needed is small: ≈ 1.3 % of the transferred width, or ≈ 5e-6 per step / 5e-4 in total) | D6–D9 |
| 2 | conductor-uniform twisted source (lemma T): only `D¹`-cubic `(0,2,1)` can profit (squared twisted types are dominated by rank 1), needs charge `κ < 0.25` | same cap if it works | very low (research-level, `κ ≈ 1` expected) | lemma T |
| 3 | knob-level gains on the simple chain | `f → 1`: `−8.0e-7`; others in 5.5 | n/a (each alone below the bar) | – |
| 4 | cubed block `(2,6,1)` (cube-full columns) | same as 1 | very low (outside cube-free) | D1–D9 for `m = 3` |
| – | **dead**: pools of any power (`π < 0`), twisted pools, `D¹` twisted types with `j ≥ 1` (incl. the quadratic one), `D²`-discount in pools (R3), the `A = D³`-conductor route | ≤ 0 | – | – |

**Lemmas for the best candidate (doubled transfer), with library status.**

| id | statement | status |
|---|---|---|
| D1 | `gaussRow(d²m, dH′) = gaussRow(d²,dH′)·gaussRow(m, d³H′)` (twist-free form); vanishing off `d·O`, norm `≤ √N(d)` | `square_twist`, `square_row`, `square_gauss` **built** (`MS/Collision/SquareGauss.lean`); the dilation at exponent 3 is mechanical (unit-scale ×3) |
| D2 | divisor-bounded CS in the dilated form (residual at `p³H′`, no phase) | `collision_family_energy_div` **built** with the phase form; copy with the dilation, mechanical |
| D3 | pushforward `(D,H′) ↦ D³H′`, `N(H′) ≤ U^μ/N(D)`, fibres ≤ `d(h″)`, with the weights `N(D)^{-1}` | `RMS/FourthPower/PositiveFamily.weighted_pushforward` is the `D⁴` version; **absent** for `D³`, mechanical but real work |
| D4 | weight sum `Σ_{D∥h}N(D)^{-1} ≲ U^{−d+ε}` for a family of `W` choices | `MS/Residual/CollisionWeight.collisionWeight_sum`-type facts **built**; adapt |
| D5 | ledger algebra with `(e,c,r)`: generalise `ds_defect_aux/ds_low_aux/ds_high_aux`, `HybridGates` (section 5.2) | **absent**, mechanical (verified symbolically in `ledger.py`) |
| D6 | Seam B / `envelope_identity` for a squared first-common pair: `2a − k + q_C = 1 + t − 6u` with norm-based `k`; `SideGeometry` with squared columns; compatibility with `idealCorrelation_cubefree_unequal_zero` | **absent** (identity is `ring`; the geometry is the work) |
| D7 | terminal gates `gPrincipal/gSecondRef/gSecondDiag/gRefUpper` for doubled units | **unknown** |
| D8 | the source: squared-prime slots in the object, selector preference, total doubled mass ≈ `1.1e-3` | **new** (no library) |
| D9 | the return: faces/budgets for objects containing doubled slots (R3: repeated copies cost `Λ` each; a doubled slot's norm is `2w`) | **absent**; R3 §5.7 |

For the twisted candidates the single missing lemma is T (section 4.5).

**Recommended next steps.** (1) Decide D8/D9 first (a design question for the source and return authors): can the detecting polynomial carry ≈ 100 squared-prime slots of width `≲ 5·10⁻⁶` (≈ 5e-4 – 1e-3 in total), and what does the return charge for them? If the answer is no, stop here: no
twist-free amplifier can beat the simple block per unit volume, and the twisted ones need lemma T. (2) Only if yes: formalise D1–D5 as one conditional `doubled_step` lemma next to `Side.envelope_identity`/`StepGates` (algebraic, no new analytic input), then D6/D7. (3) Independently of the amplifier question,
the percent-level currencies of 5.5 are the benchmark any competing improvement has to meet: converting B2's exact-return θ's (discrete chain; `B2_source_slope.md` §0.3: black box `0.873938984`, supply 0.12 `0.873934359`, supply 0.09 `0.873929714`) with the discrete slope `−7.94e-4` per unit `e`
gives the e-equivalents `1.009 / 1.015 / 1.021` against the discrete threshold `e* = 1.0131` (B2's marked leaf is not an amplifier; the conversion only compares sizes).

---

## 7. Flags, discrepancies, what I could not settle

* **Discrepancy with B2 on `c < 6`.** B2's `c = 5.95` run used an uncapped `q > ¾`; my capped model (`q ≤ ¾ − 2e-6`, as `gQUpper` requires) gives θ = 0.873933799 at `c = 5.95` (B2: 0.873933396). The thresholds in 5.5 use the capped model.
* **Floor 3/5 vs Lean 13/20.** `HybridGates.gQFloor = dens − 13/20`; the replicas and prices use the brief's floor 0.60.
* **Older `scenarios.py` numbers** (`results/scen.jsonl`) use a mid-grid reference face (≈ 4e-7 bias); the tables in this report come from `pricing2.price_cd` (coordinate descent of count and physical faces).
* **Capacity model fix.** An earlier version of `dchain_cap.py` dropped the doubled part in the `v → 0` limit of the LOW density (`q(0)`), which made the capacity scan look useless; fixed, earlier numbers discarded (`results/cap_eval.log` is from the fixed script).
* **Unresolved:** the Lean `x₀` normalisation for non-simple inputs (volume vs norm) — affects only the RC3 *consistency reading*, not `(e,c,r)`; terminal gate charges; `r = 1` vs `2` for squared slots; the return-side cost of doubled slots.
* **What I need to go further:** (i) the definition of `SideGeometry`/first-common pair with squared columns in the Lean (to prove D6); (ii) the exact `gPrincipal…` derivations to get doubled charges; (iii) R3's statement of how the return counts a slot whose columns are `p²`.

---

## 8. Files (`research/newpowers/r2/`)

* `ledger.py` — `Amp(name,m,k,e,c,r,…)`, twist-free classification, unit payments, native barriers, `qinf`, symbolic checks (PR 83 defect identity, generalised identity, envelope `1+t−(2m+k)u`). `python3 ledger.py`.
* `twisted.py` — the `(m,j)` twisted-type table and the break-even conductor charge `κ*`. `python3 twisted.py`.
* `ode_amp.py` — continuum density-step ODE for a mixture; `wall(floor)`. `price_amp.py` — exact-return θ for a pair of faces (cache `results/theta_cache.jsonl`); needs the toolchain: set `R2_TC` to a directory with `pr86.py`, `best.py`, … (default: sibling `../r3/tc`).
* `pricing2.py` — coordinate-descent role split (count face vs physical face). `scenarios.py`, `thresholds.py` — scenario prices and one-knob thresholds (`python3 thresholds.py e|c|r|eps|dthr`). `final_table.py` — the consolidated table of 5.4.
* `dchain_amp.py` — discrete greedy chain (replica of `HybridGates`) with `(E,C,R)`; `dchain_cap.py` — capacity-limited doubled mass (env `UD`); `eval_discrete.py` — exact-return price of a discrete chain; `run_cap.sh` — the capacity scan.
* `results/` — raw JSON/logs referenced above (`scen.jsonl` (older scenario prices), `final.jsonl` (5.4), `thresholds.jsonl` (5.5), `dch_*.json` (discrete chains), `cap_eval.log` (5.6), `theta_cache.jsonl` (every exact-return θ ever evaluated, keyed by the four face coordinates)).

Reproduce the headline numbers (4 cores; the exact-return θ costs seconds each, everything is cached in `results/theta_cache.jsonl`):
`python3 ledger.py` (barriers, symbolic identities); `python3 twisted.py` (section 4 table); `python3 final_table.py base e1.0116 e1.02 e2 …` (5.4; ≈ 2 min per scenario);
`python3 thresholds.py e|c|r|eps|dthr|floor 0.60 [bar]` (≈ 10–15 min per target); `python3 dchain_amp.py 1 6 1 0.60 2.00 out.json` (baseline discrete chain) then `python3 eval_discrete.py out.json 14`;
`UD=5e-6 python3 dchain_cap.py 1 6 1 0.60 2.00 out.json && python3 eval_discrete.py out.json 0` (5.6).
