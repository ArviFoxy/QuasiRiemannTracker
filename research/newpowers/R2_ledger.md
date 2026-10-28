# R2 — Ledger of amplifiers: generalised chain, combination law, pricing on PR 83's steps

Date 2026-10-28. Python only (no `lake`/`lean`, nothing committed or posted). Scripts and raw output: `research/newpowers/r2/`
(`README` at the end of this file). Siblings: `R1_algebra.md` (exact Gauss identities over ℤ[ω], numerically verified, used
below), `R3_return.md` (return side).

**Rule followed.** Earlier notes (`mixed-step/ADVERSARIAL_REVIEW.md`, `MIXED_STEP_LEMMA.md`, `B2_source_slope.md`, `lemmaW.md`) are
hypotheses. Every conclusion carries a tag:

* **[L]** a theorem I read in a Lean tree (file:line). "built" = an `.olean` exists in `lean-env/qrh/.lake`; I did not recompile.
* **[D]** my own derivation, from [L] facts + the exponent model of section 2.1 (stated, checkable by hand).
* **[N]** numerics (script named). **[R1]/[R3]** taken from the sibling reports (their tags apply).
* **[H]** needs an analytic lemma that is not in the library.

Path shorthand. `S83/` = PR 83 `sil_density_split_20261026/` (merged tree, scratchpad `upstream/submissions/2026-10-26-sil-density-split/src/Submissions/...`),
`COL/` = `lean-env/qrh/Submissions/hailey_collet_1252270103/`, `MS/` = `lean-env/qrh/Submissions/arvi_mixed_step/`, `P69/` = `/home/user/ext/hillclimb/paper69/`.

---

## 0. Verdict (read this first)

1. **Rigidity of the amplifier design space [D on L, R1].** An amplifier saves through a *common* residual polynomial (one polynomial for the
   whole block, which is what makes the Cauchy–Schwarz count cancel). Gauss multiplicativity + sextic reciprocity then force the dilation:
   `g(Dᵐn, h) = εᵐ·g(Dᵐ,h)·g(n, D^{4m mod 6}h)` (R1, 20 605 comparisons), exactly twist-free only for `k ≡ −2m (mod 6)`. The scale cost
   `c = 2m + s` (column term `2m`, MAIN-radius shift `s`, section 2) is therefore `≡ 0 (mod 6)` and **equals 6 in its cheapest form for every
   `m = 0…5`**: pool `0+6`, `m=1: 2+4`, `m=2: 4+2`, `m=3: 6+0`, `m=4: 8−2`, `m=5: 10−4`. The saving is `e = 1` (pool, `m = 1`) or `e = 2`
   (`m ≥ 2`); the removal from the parent's slot width is `r = 0` (pool) or `1`. **The whole design space is
   {pool (1,6,0), simple block (1,6,1), squared-or-higher block (2,6,1)}** in the notation `(e,c,r)` per unit of block volume `d = log_U #{D}`.
   `c = 6` is not an accident of Sil's proof; `e = 2` is the ceiling.

2. **The doubled-block transfer does save at twice the rate, and the frequency sparsity is a *gain*.** `g(D²,h) ≠ 0` iff `D ∥ h`
   (R1; Lean: vanishing off `D·O`, norm `≤ √N(D)`, `square_row`), so for a fixed `h` the Cauchy–Schwarz runs over a divisor-bounded set, not over
   `W = U^d` terms (`collision_family_energy_div`, built): the count factor `W` is **not paid** while the renormalisation `V → V/W` **is** gained,
   `+d` on top of the volume saving `d` of the simple transfer. The pushforward is `(D,h′) ↦ D³h′`, `h = Dh′`: image radius `μ+2d` (not `μ+4d`).
   Ledger `(e,c,r) = (2,6,1)` per unit of `d`; per unit of the squared block's *norm* `2d`: saving 1, scale 3 (simple: 1 and 6). Payment per unit
   `2 + q − 6qβ` instead of `1 + q − 6qβ`; descent `Λ₀ > 6qB₀/(2+q)` (1.64·B at q=3/4) instead of `6qB₀/(1+q)` (2.57·B, the native barrier 18/7).
   Along PR 83's chain the simple transfer sits exactly on its barrier (payment `+0.0010` = the 0.999 slack); the squared block would pay `+1.0010`.

3. **But the input must contain squared columns of positive volume, and it does not.** Collision columns have relative volume `U^{−w_C}`; Collet/PR 83
   absorb them by the `(10a)` restoration (induction on the slot count), not by an amplifier; "repeated marks" is a HIGH-*count* device (a K-fold slot in the
   inverse witness), not squares in the Gauss columns; a source family with squared-prime slots `Σ_p ν_p χ(p)²` would be a new theorem family (new base case,
   new HIGH count, new return) in which each doubled slot costs `2Λ` in the face budget (R3 §5.7, [L]). Section 3.

4. **Twisted types are dominated [D, partly H].** `D¹` leaves `(n/D)₂`; `D²`/`D³` leave cubic/sextic twists; `p³`, `p²` pools leave quadratic/cubic ones.
   The twist is a character of `n` of conductor `N(D)`, **not** a ray character of the fixed modulus over which `ActualLow` quantifies; Lean's route is the dictionary
   `twistDict` (the twisted residual is the *same* source at the shifted row `z = A·w`, row cost `N(A)`), which re-creates exactly the missing dilation, i.e. the canonical
   type. Treating the twisted residuals one by one loses the count `W` (so `e ≤ 0`), and inside the second-transform method the child's diagonal equals the number of
   characters, so no large sieve over the twist family can recover it. Section 4.

5. **Pricing (exact Lean-return toolchain, floor 3/5, role split) [N].** One-parameter equivalents of "the bar": `e ≥ 1.0116` (continuum chain; `1.0131` for the
   `ΔL = 0.005` chain), or `c ≤ 5.9587`, or `r ≥ «r*»`, i.e. the effective LOW threshold `q_∞ = f·e·L/(cB − rL)` must rise by ≈ 1.1–1.2 %. A doubled
   fraction of the *transferred* volume of 1.2–1.3 % does it, which is an absolute doubled width of ~1e-5…1e-4 in `log_U` (section 5.5). Full doubling
   (`e = 2`): the return's transport box `ℓ < 0.171` becomes the limit, θ = 0.8739167 (−1.9e-5 vs the bar). **Nothing available supplies the 1.2 % for the
   simple-source chain**; B2's marked HIGH leaf is worth `e_eq ≈ 1.009` (black box) to `1.015` (supply 0.12) in this currency, the 0.999→1 slack `1.001`.

6. **Ranking / lemmas (section 6).** Best conceivable: the doubled-slot family (all analytic ingredients of the *step* are in the library except a D³-pushforward copy of
   `PositiveFamily`; the *family* is a new theorem). Best realistic on the amplifier side: nothing; the nearest real lever stays B2's marked leaf (not an amplifier).

---

## 1. What the Lean says (anchors) and what is derived

| fact | where [L] |
|---|---|
| pool identity `g(u,p⁶h) = 1_{p∤u} g(u,h)` (CA3/CA5); average over the pool; pushforward `(p,h) ↦ p⁶h` | `P69/sources.tex` (CA3–CA6), `P69/foundations.tex` (131), (136); Collet `GaussMask` (R1 §5) |
| MAIN radius `μ = 2A − c − d + R + E − M + (d−c)₊ + 6a + ω` | `COL/Cycle61/Physical/InitialMass/SecondHighPayment.lean:21` (`actual_main_radius_power`) |
| coordinates `x₀ = −a + (μ − (A−c)) + (g₂−t₂−b₂)`, `x₁`, `x₂ = M − R − (c−d)₊ + L_c − 6a − ω + ε`, `x₃ = A − c − b₂` | `COL/Cycle61/Physical/InitialMass/SecondHighCoordinates.lean:20` |
| `x₀ + x₁ + x₂ − labelSide(A) − labelSurplus = rawExcess a …` (the `A` cancels) | `COL/Record12518109Raw/RawWeight.lean:23` (`actual_raw_coordinate_identity`) |
| child scale `x₂ = M − 6a − max(d−c,0) − (ω+reserve) + err`, independent of `A`; `= sourceF − δ − ρ`, `sourceF = 1 − 6·sourceA` | `COL/Record1252270103Source/Coefficient/RegularLowRetainedRadial.lean:23,38`; `COL/Record1252270103Finite/SourceFormulas.lean:21` |
| `D⁴` identity for fifth-free columns, all non-unit cases: `gaussRow a (D⁴k) = (idealRowHom D (span a))² · gaussRow a k` | `arvi_repeated_marks_on_sil_face_…/FourthPower/GaussTransfer.lean:98` (`normalized_fourth_power`) |
| `Σ_v A B_v [(D,n_v)=1] G(D n_v; k) = Σ_{χ,ξ} c(χ,ξ)(A χ(D) G(D;k)) P_ξ(D⁴k)`, `N(D⁴k) = N(D)⁴N(k)` | `S83/CubeFree/Second/FourthTransfer.lean:35,64` |
| `2a − k + q_C = 1 + t − 6u` with `a = A−c−u`, `k = K+4u` (`6 = 4+2`, proved by `ring`) | `S83/CubeFree/Second/Side.lean:36` (`envelope_identity`) |
| LOW defect `F ≤ (L₀−L)v + (6B₀−L₀)u`, LOW payment `qF ≤ L₀(u+ε/16)`, HIGH payment `ν(P_C+s) − k(1+t−6u) ≤ u`, `q(6B₀−L₀) ≤ L₀` | `S83/Density/StepGates.lean:122,134,152,89` |
| gates `dens`, `packed = 1−6u`, `highJ`, `gRetainedCap/Width`, `gPrincipal`(9/2), `gSecondRef`(9/2), `gSecondDiag`(4), `gRefUpper`(3) | `S83/Source/HybridGates.lean:48,58,62,…` |
| squared block: `g(d²m, dH′) = (d/m)₂·g(d²,dH′)·g(m,H′)` (the reciprocity sign enters squared, `= 1`); `g(δ²,·)` vanishes off `δ·O`, norm `≤ √N(δ)` | `MS/Collision/SquareGauss.lean:198` (`square_twist`), `:81,164` (`square_gauss`, `square_row`); **built** |
| divisor-count Cauchy–Schwarz over the colliding primes | `MS/Residual/CollisionWeight.lean:34` (`collision_family_energy_div`), `:98`; **built** |
| twist absorbed as a character, conductor `≤ N(τ.modulus ⊓ 12)·N(fixedBadMask)·N(72)·N(A)`; dictionary `twistDict` = natural row of `τ` at `z = A·w` | `MS/Collision/CollTwist.lean:60`, `TwistDict.lean`; `MS/Residual/CollisionTransfer.lean:195` (`famEnergy_elim`) |
| what the source theorem quantifies: `∀ rayM H … ∀ η η₀ Q, ∃ degree controls C, ∀ᶠ Z, InitialAffineAt …` (η fixed **before** `Z`); `ActualLow` = zero-maximum `< a+2e` for every `θ ∈ RayQuotient.Characters M H` | `COL/Record12518109Existence/UniformSource.lean:19`, `COL/Record12518109Source/InitialMoment.lean:94`, `COL/Cycle61/Moment/LowBranch/Gate.lean:19` |

Everything else in this report is [D] unless tagged. In particular **the earlier review's "e = 1, c = 6, c = 4 refuted" is re-derived here independently** (section 2.1):
the reason is the Lean fact that `x₂` is independent of `A` (the radius is fixed by the first transform of the *whole* input) combined with `envelope_identity`.

---

## 2. The ledger, re-derived and generalised

### 2.1 The exponent model (what is derived from what)

Exponents are `log_U`. Input: `V = U^A` terms (volume), columns `u = f·B·n` of norm `U^α`; for simple inputs `α = A`. `B = D^m`, `D` a squarefree
product of selected slot primes, `W = U^d` choices of `D` (`N(D) ≈ W`). `q_u^{−1/2}` are the explicit Poisson weights of the first transform
(`P69/foundations.tex` (120), (126): the `(q_aq_b)^{−1/2}` of the kernel). MAIN norm `𝓜(μ) = Σ_h Ω(Nh/U^μ) |Σ_u b(u) q_u^{−1/2} 𝔤(u,h)|²`;
the target of the step is `𝓜 ≲ U^{A}` ((127)/(MF3.55), since `E = (H₀/V)·𝓜`).

* [L] The first radius is `μ = 2α − …` (column norms); the second transform gives a child family of size `m′ = 2α′ − μ′` for a MAIN
  norm of columns `α′` at radius `μ′` (MF3.60, (138)–(139)), and `𝓜(μ′) ≲ U^{μ′−2α′}·V′·E′` with `E′ ≲ U^{M′}`, `M′ = m′ + q′`. Hence
  **`x₂ = 2α′ − μ′ + const` and `x₀ + x₂ = −a + A_vol′ + const`**: independent of the radius and of the column norm, only the *volume* of the object that is transformed matters.
  The Lean confirms the pool case (`x₂` free of `A`, `A` cancels in RC3).
* [D] **A transfer changes the transformed object, not the first transform.** `μ` was fixed by the first transform of the whole input and can only be enlarged by
  the pushforward. The residual has volume `A − d`, column norm `α − md`, radius `μ + s·d`. Therefore
  `x₂′ = x₂ − (2m + s)d` (column term `2md` — the residual's columns are smaller by `md` and `x₂` contains `2α′` — plus the radius shift `sd`),
  `x₀′ + x₂′ = −a + (A−d) + const`, while the *target* `labelSide(A)` still carries the original volume ⇒ **RC3 drops by `d`**. The "trace" claim
  `MAIN radius −2d + 4d = +2d` of `COLLET_LOW_TRACE.md` §3 recomputes `μ` from the residual and is wrong for this reason; the `c = 4` reading is refuted (agrees with the review's O1).
  The identity `H = 2a − k + q_C = 1 + t − 6u` of PR 83 (`envelope_identity`) is exactly `2(A−c−u) − (K+4u)`.

### 2.2 The chain of ADVERSARIAL_REVIEW §1 (steps 0–9) for a block of type (m,k) and for the pool

Block `B = Dᵐ` in the column, `h` the MAIN frequency; `γ = 1` if `m ≥ 2`, else `0`.

| step | pool `p⁶` (m=0) | simple `D` (m=1, k=4) | squared `D²` (m=2, k=2) | cubed `D³` (m=3, k=0) |
|---|---|---|---|---|
| 1 identity [L/R1] | `g(u,p⁶h)=1_{p∤u}g(u,h)` | `g(Dn,h)=ε·g(D,h)·g(n,D⁴h)` (`ε=±1` ray sign, a bounded dilation `E₀³`, norm ≤ 27, R1) | `g(D²n,h)=g(D²,h)·g(n,D²h)` (no sign, `ε²=1`) | `g(D³n,h)=ε·g(D³,h)·g(n,h)` |
| block scalar `g(Dᵐ,h)` [R1] | – | `‖·‖=1`, `D∤h` | `≠0 ⇔ D∥h`, `‖gaussRow‖=N^{1/2}` | `≠0 ⇔ D²∥h`, `‖gaussRow‖=N` |
| weight × scalar (`q_u^{−1/2}·|g|`) [D] | – | `N(D)^{−1/2}` | `N(D)^{−1/2}` | `N(D)^{−1/2}` |
| 2 Cauchy–Schwarz | Jensen over `P` primes: `1/P` | over all `W` choices: `Σ_D N(D)^{−1} ≈ 1`; count `+d`, renormalisation `V→V/W` `−d`, net 0 [L: `d_cauchy`, `weighted_pushforward`] | over `D∥h` only: `≲ d(h)/W = U^{−d+ε}` [L: `collision_family_energy_div`]: **no count, renormalisation kept: net `−d`** | same as `m=2` (`D²∥h`) |
| 3 pushforward | `(p,h)↦p⁶h`, radius `+6a`, fibres ≤ `(C+6a)/(a/2)` | `(D,h)↦D⁴h`, radius `+4d` | `h=Dh′`, `(D,h′)↦D³h′`, radius `μ−d+3d = μ+2d` | `h=D²h″`, residual at `h` itself: radius `+0` |
| radius shift `s` (per `d`) | 6 | 4 | 2 | 0 |
| residual | same polynomial, same columns | volume `A−d`, columns `α−d` | volume `A−d`, columns `α−2d` | volume `A−d`, columns `α−3d` |
| 4 coordinates | `Δx₀ = +5a` (6a radius, −a density), `Δx₂ = −6a`, `Δx₃ = 0` | `Δx₀ = +5d`, `Δx₂ = −6d`, `Δx₃ = −d` | `Δx₀ = +4d`, `Δx₂ = −6d`, `Δx₃ = −d` | `Δx₀ = +4d`, `Δx₂ = −6d`, `Δx₃ = −d` |
| 5 RAW saving `e` | 1 | 1 | **2** | **2** |
| 6 scale cost `c = 2m + s` | 6 | 6 (= 4 + 2) | 6 (= 2 + 4) | 6 (= 0 + 6) |
| 7 LOW/HIGH split | rows of the same source | rows of the residual (a Collet source, same fixed `η`); ray labels `ξ` as before | rows `z = D³h′·…` of the same source; **no ray labels** | likewise |
| 8 width passed to the parent, erasure cap | unchanged; cap `min(z′, h₀Q′)`, `z′ = (B₀Q′ − P₁)/Λ₀`, `Q′ = 1 − 6a − δ − ρ` | `b − f − d` (selected slots leave); `Q′ = 1 − 6a − 6d − δ − ρ` | `b − f − d`; same `Q′` | same |
| `r` | 0 | 1 | 1 | 1 |
| HIGH value shift `Δx₀+ρΔx₂+νΔx₃` | `5 − 6ρ` | `5 − 6ρ − ν` (matches the review's O3 row) | `4 − 6ρ − ν` | `4 − 6ρ − ν` |
| 9 parent call | `G(B₀,Λ₀,h₀)` at `U^{Q′}` | same | same | same |

Higher `m` (R1's `κ` table, [N]): `m=4`: residual point `D¹h″` with `h=D³h″`, shift `−2`, `c=8−2=6`; `m=5`: `D⁰h″`, `h=D⁴h″`, shift `−4`, `c=10−4=6`; both need the explicit coprimality mask
and are outside the cube-free setting; `m=6` is the trivial-character case (Ramanujan sums) and costs `c=12`. For the project only `m ≤ 2` is relevant (columns are cube-free: PR 83 `PowerFree 3`, Collet `ValuationAtMostTwo`).

**Why the squared block's support is a gain, not a cost [D].** Per fixed `h` the *number of terms* collapses from `W` to `d(h)`, but each surviving term is `N(D)^{1/2}` times larger
(`‖gaussRow(D²,·)‖ = N^{1/2}`) and the explicit weight is `q_u^{−1/2} = N(D)^{−1}q_n^{−1/2}`: weight × scalar `= N(D)^{−1/2}` for every `m`, so
`Σ_{D ∥ h} N(D)^{−1} ≲ d(h)/W` (simple block: `Σ_D N(D)^{−1} ≈ 1`). The mean square of `g(D²,·)` over a period is `1 − 1/N` as for every `m` (Parseval, R1 §0.8):
spiky, not larger. The radius shrinks by `d` (only `h ∈ D·O` contribute), which exactly offsets the extra `D` in `D²·(Dh′)`. Net radius shift `2d` (R1's "κ = 3" form).

### 2.3 Results

Per unit of block volume `d` (the number of choices `U^d`); in brackets per unit of the block's norm `md`:

| type | (e, c, r) | dilation k [R1 cost k/m per unit norm] | status |
|---|---|---|---|
| pool `p⁶` (Collet) | (1, 6, 0) | 6 | [L] |
| simple block `D` (Sil) | (1, 6, 1) [(1,6,1) per norm] | 4 [4] | [L] identity + arithmetic; ledger [D] = review |
| squared block `D²` | (2, 6, 1) [(1, 3, ½)] | 2 [1] | identity [L] (`square_twist`, built; R1 450 + 58 cases); C–S [L] (`collision_family_energy_div`, built); ledger [D] |
| cubed block `D³` | (2, 6, 1) [(⅔, 2, ⅓)] | 0 [0] | [D], R1 [N]; not cube-free |
| `m = 4, 5` | (2, 6, 1) | 4, 2 (reduced κ: −2, −4) | [D], R1 [N], mask needed |

**Proposition (rigidity) [D].** For a twist-free amplifier of multiplicity `0 ≤ m ≤ 5` (`m=0`: pool): (a) `c = 2m + s ≡ 0 (mod 6)` and `c ≥ 6`; (b) `e = 1 + [m ≥ 2] ≤ 2`;
(c) `r = [m ≥ 1] ≤ 1`. *Proof.* (a) twist-freeness is `s + (m−1)·0 … ≡ −2m (mod 6)` on the dilation relative to `h` (R1 table) and the integrality of the residual frequency
(`D^{κ}h″`, `κ ≥ 0`) bounds `s ≥ 1 − m`; the smallest admissible `s` gives `c = 6` for each `m ≤ 5`; `c = 0` would need `s = −2m ≥ 1−m`, impossible for `m ≥ 1`. (b) the volume saving is `d`;
the only other source of saving is the removal of the count `W` from the Cauchy–Schwarz, at most `d`, and it occurs exactly when the block scalar is supported on a thin set (`m ≥ 2`).
(c) the parent's slot width counts volume. ∎ Consequence: the unit payment `e + qr − cqβ ≤ 2 + q − 6qβ` for every twist-free amplifier, so
**any chain built from them has `Λ₀ > 6qB₀/(2+q)` as a necessary condition**, `Λ₀ > 6qB₀/(1+q)` if only `m ≤ 1` is available, `Λ₀ > 6qB₀` for the pool alone.

---

## 3. Where could squared blocks come from? (Q2)

**3.1 Collision columns in the existing inputs.** (i) *Plain–slot or slot–slot collisions* (`p_i | l₁l₂` or `p_i = p_j`): a pattern `C` of total width `w_C` forces `D_C | l₁l₂`, probability `1/N(D_C)`
per tuple, so the family has `V/W_C` tuples: **relative volume `U^{−w_C}`** (finitely many patterns, `2^{|J|}`). The theorem is asymptotic in `Z` with fixed widths, so this fraction tends to zero
polynomially; the 1.2 % needed in section 5 would require `w_C ≲ 4.4/ln U`. (ii) *Squared common primes of the first-common pair* (types `(1,2),(2,1),(2,2)` with widths `B₁₂, C₂₁, D`, `P69/sources.tex` (10),(12)):
they carry credit `−B₁₂ − D` in RC3 ([L] `actual_raw_coordinate_erasure` + (G12)) but the binding geometry is the generic coprime pair (`A = B₁₂ = C₂₁ = D = f = 0`). (iii) PR 83's cube-free columns:
`idealCorrelation_cubefree_unequal_zero` (`S83/CubeFree/Second/FirstDivisor.lean:208,222`) kills the second correlation of columns with unequal multiplicities `(1,2)`; the squares that remain are in the
*residual* columns, not in the selected block. (iv) Collisions are *removed* from the amplifier analysis by the `(10a)` restoration (`S83/CubeFree/FP/RestorationCollisionEnergy.lean`: "restore the full original
natural-slot product from its injective singleton families"), an induction on the slot count at zero ledger cost. Our own `MS/Collision/` (identity, divisor C–S, twist characters) was never assembled:
`LEAN_NOTES.md` records (Col) as an open design gap (the LOW supply is for one ray modulus fixed before `Z`; a "LOW twin for twisted dictionaries" is missing).

**3.2 Deliberately doubled slots.** *Repeated marks* (`repeated-marks/README.md`, Lemma A_K) use a slot K times in the **HIGH inverse witness**: the objects are the K-fold products `∏_c Q_i(χ)` of independent prime sums over the same
list — columns `p₁⋯p_K` of distinct primes with a `1/|pool|` diagonal — and the face counts `Λ·width` *with multiplicity* ([R3 §5.7, L]: `hcap` of `finite_physical_pair_affine`), so a repeated slot costs `Λ` per copy.
That gives HIGH-count gains (it produced the earlier −2.2e-5), not squares in the Gauss columns of a MAIN polynomial. R3 prices the "`D²` discount" in the return at 0.91 %: neutral otherwise.

**3.3 A positive-density construction would be a new source family.** The input would carry slots `Q^{(2)}(χ) = Σ_p ν_p χ(p)²` (columns `p²`, `U^w` terms of norm `U^{2w}`). Costs elsewhere: (a) the first transform's radius grows by `2w` and the trivial bound of `𝓜`
by `U^{w}` (columns `VW` vs volume `V`); the direct (non-transfer) treatment has the *same* RC3 as a simple input of equal volume, since `x₀ + x₂` depends only on the volume; (b) the face budget: a doubled slot of width `w` has length `2w`,
so `Λ₂ ≥ 2Λ` unless the sparsity is exploited (R3, [L]); (c) the natural base theorem `G(1,K,h₀)`, the LOW erasure bound `|Q^{(2)}|² ≲ Z^{qw}` and the HIGH count for the cubic-character polynomial `χ²` are new; (d) the return consumes only
simple-slot faces (R3 §1), so a doubled-family chain would not enter θ. **No source in the pipeline produces squares with positive density**, and plain→slot (Buchstab/Ramaré) decompositions create *simple* slots only.

---

## 4. Twisted types: D¹, D², D³, p³, p² (Q3)

**4.1 Leftovers (R1, exact).** Block `Dᵐ` with dilation `D^k` leaves `εᵐ·χ_n(D)^{2m+k}`; for `m=1`: `k=1: (n/D)₂ = ε(D/n)₂` (the Dirichlet character of `n` mod `D`, **not** `(D/n)₂` as in the hypotheses), `k=2: cubic`, `k=3: sextic`, `k=4: ε only`. Pools `p^k`:
twist `χ_u(p)^{−k}` (`k=3` quadratic `(p/u)₂`, `k=2,4` cubic, `k=1,5` sextic), and `p^k` is a valuation selector (keeps `v_p(u) ∈ {0, k+1}`); only `p⁶` is twist-free.

**4.2 What bounds the twisted family [L].** `ActualLow` (`Gate.lean:19`) is a condition on the row `z` for **every ray label `θ ∈ RayQuotient.Characters M H`**, `M` a ray modulus fixed before `Z` (`UnitFaceSource`: `∀ rayM … ∃ degree controls C, ∀ᶠ Z`). A quadratic or cubic symbol mod `D` with `N(D) = U^d` is a character of conductor `U^d`,
not of `M`: **not covered.** Moreover the base character `η` of `InitialAffineAt` is fixed before `Z`, so `twistChar τ A` (conductor `≲ N(A)`, `CollTwist.lean:60`) cannot be fed to the source theorem as a new base character. What the library does instead is the *dictionary*
(`TwistDict.lean`): `twistDict τ A` is the natural row of the **same** `τ` at the frequency `z = A·w`, so the twisted residual is the untwisted source evaluated on the sparse row set `{A w}`, and its LOW/HIGH classification is the original `ActualLow(z)`. The price is the row size `N(A)` in the scale (for the collision twist `A = δ³`: `N(δ)³`). That is the dilation by `D^{s}`, `s ≡ −j` for a leftover `χ^j`:
**the twisted type collapses onto the canonical twist-free type (m, k+s)**.

**4.3 Treating the twisted residuals individually [D].** `|F(h)|² ≤ (Σ_D N(D)^{−1}…)·Σ_D |G_D(·)|²` and each `G_D` needs its own source bound: `𝓜 ≲ Σ_D 𝓜_{res,D} ≈ W·V_res` for `m = 1` (the count `W` is not absorbed
by a common pushforward): `e = 1 − 1 = 0`; for `m ≥ 2` the count is already divisor-bounded and the same route gives `e = 2 − (cost of the twist)`; in all cases the best is `e ≤ 0` plus a scale `c = 2m + s_actual + τ` with `τ ≥ 0` the twist's scale cost. Inside the method the reason is structural
([D]): the second transform turns `𝓜` into `U^{μ′−2α′}·V′·E′` with `E′` a child moment over **all** characters of the (D-dependent) family; its diagonal is the number of characters, `W·U^{m′}`, which gives back the factor `W`. A common residual is what
makes the child family a single one; a D-dependent twist destroys it. Unit payments of the best conceivable twisted types (`τ = 0`): `D¹`: `(0, 3, 1)` ⇒ `q(1 − 3β) = −0.20` at the operating point (`q=0.6, β=0.444`); `p³` pool: `(0, 3, 0)` ⇒ `−0.80`; `p²` pool: `(0, 2, 0)` ⇒ `−0.53`.

| type | leftover | route A: row shift (Lean) | route B: individual residuals | rescue would need |
|---|---|---|---|---|
| `D¹` (m=1,k=1) | `(n/D)₂` | `D^{1+3}` ⇒ (1,6,1) | `(0, 3+τ, 1)` | a *joint* twisted source theorem with child diagonal `U^{m′}` (not `W U^{m′}`) — contradicts the diagonal |
| `D²` (m=1,k=2) | cubic | `D^{2+2}` ⇒ (1,6,1) | `(0, 4+τ, 1)` | same |
| `D³` (m=1,k=3) | sextic | `D^{3+1}` ⇒ (1,6,1) | `(0, 5+τ, 1)` | same |
| `p³` pool | `(p/u)₂` | `p^{3+3}` ⇒ (1,6,0) | `(0, 3+τ, 0)` | same |
| `p²` pool | cubic | `p^{2+4}` ⇒ (1,6,0) | `(0, 2+τ, 0)` | same |
| `D²` with `k=0,1` (m=2) | `c⁻¹`-type / sextic | `D^{k+s}` ⇒ (2,6,1) | `(≤2, 4+τ, 1)` | same |

The hypothetical lemma that would change this is a **conductor-indexed** source theorem charging `N(D)` instead of the row size `N(D)^{s}` (e.g. `d` instead of `3d` for the quadratic twist); even then `e = 0` for `m = 1` and the payment `q(r − cβ) < 0` once `β > 1/c`.

**4.4 Sign.** The ray sign `ε(D,n)` is a mod-4 object: `ε(B,n) = (E₀/n)₂ = χ_n(E₀)³`, `E₀ ∈ {1,−1,λ,−λ}` (R1 §3.5.1) so it is a bounded dilation (norm ≤ 27), replacing Sil's ray-character expansion by one common vector. It does not change `(e,c,r)`; for `m = 2` it is absent.

---

## 5. Combination law, PR 83's step and the pricing (Q4)

### 5.1 LOW payment and descent for a mixture [D, from `ds_defect_aux`/`ds_low_aux`]

Types `T` with masses `x_T` (volume), `(e_T, c_T, r_T)`; `F′ = 1 − Σ c_T x_T`, parent slot width `b − f − Σ r_T x_T`. With `β = B₀/Λ₀` and `X₀ = b + (t−B₀)/Λ₀ = (Λ₀−Λ)(b−s₀)/Λ₀`:

    Σ_T x_T ( e_T + q r_T − c_T q β )  ≥  q X₀ + r            [PR 83: a(1−6qβ) + d(1+q−6qβ)]          (LOW)
    J(x) = (1−ρ(ν))(1 − Σ c_T x_T) + Σ e_T x_T − ν( B − (Λ−1)W − Σ r_T x_T ) ≥ 0,  ν ∈ [q, ¾]          (HIGH)

*Check against Lean.* `ds_defect_aux` with `H = 1 + t − c u`, `s ≤ S − f − r u` gives `F ≤ (Λ₀−Λ)v + (cB₀ − rΛ₀)u`; `ds_low_aux` with price `≤ e u` gives `q[(Λ₀−Λ)v + (cB₀−rΛ₀)u] ≤ Λ₀ e u`. `(e,c,r) = (1,6,1)` is PR 83 verbatim (`generalised defect identity` and the PR 83 identity both reduce to 0 in `ledger.py`).
No synergy between types: payments add, scales add. **Descent** (the analogue of `Λ > 6qB/(1+q)`): some available type with positive unit payment, i.e.
`Λ₀ > min_T c_T q B₀/(e_T + q r_T)`. The *mass* of the best type is not binding in the limit `dL → 0`: LOW needs `Σ x_Tπ_T ≥ q dL v/Λ₀`, proportional to `dL·v`.

Unit payments `π_T = e + qr − cqβ` along PR 83's chain [N, `ledger.py`] (`q = q_∞`, `β = B/L`):

| L | B | q_∞ | β | pool | simple | squared |
|---|---|---|---|---|---|---|
| 2.5715 | 0.99999 | 0.7493 | 0.3889 | −0.748 | +0.0010 | +1.0010 |
| 2.34 | 0.98880 | 0.6507 | 0.4226 | −0.650 | +0.0010 | +1.0010 |
| 2.2031 (wall) | 0.97855 | 0.6000 | 0.4442 | −0.599 | +0.0010 | +1.0010 |

The pool is never used at the operating point (needs `Λ > 6qB`); the simple transfer is exactly at its barrier (the `0.001` is the 0.999 slack); a squared block would be 1000× above it.

### 5.2 Which gates of `HybridGates` change (with `(e,c,r)` per unit `u`)

| gate / object (`S83/Source/HybridGates.lean`, `Density/StepGates.lean`) | PR 83 | with (e,c,r) |
|---|---|---|
| `dens`, `densE`, `lowDefect`, `low_identity` | `f·Λ₀A / ((Λ₀−Λ)(1+Dv) + (6B₀−Λ₀)A)`, `f = 0.999` | `min(¾, f·e·Λ₀A / ((Λ₀−Λ)(1+Dv) + (cB₀ − rΛ₀)A))` (LOW holds for every smaller `q`; `q_upper` forces the cap) |
| `packed` | `1 − 6u` | `1 − c u` |
| `highJ` | `… − (6(1−ρ) − ν − 1)u` | `… − (c(1−ρ) − ν r − e)u` |
| `gRetainedCap`, `gRetainedWidth`, `gHighDeriv` | `w − u`, `B − (L−1)w − u` | `w − r u`, `B − (L−1)w − r u` |
| `ds_defect_aux`, `ds_low_aux`, `ds_high_aux` | `(6B₀−L₀)u`; price `≤ u` | `(cB₀−rL₀)u`; price `≤ e u` |
| `gPrincipal`(9/2), `gSecondRef`(9/2), `gSecondDiag`(4), `gRefUpper`(3) | per-unit charges of the transfer (review O3) | **not derived** for the squared block [H]; reserves 0.014/0.09/0.047/0.13 at L≈2.2 (`dchain` replica), the charges would have to grow by > 2 per unit of `u` to bind at `u ≈ 7e-3` |
| `q_lower/upper/floor`, `H_lower` | ½, ¾, 13/20→3/5, 9/10 | unchanged |
| `StepData` price contract, `Selection` (whole-slot selector, one mesh) | unchanged | unchanged (selector acts on widths) |

### 5.3 ODE, native barrier and slope

With `(e,c,r)` the continuum density step (`B2 §1.2`, re-derived from the three Lean lemmas above) is
`dB/dL = (B − 10/(15−6q)) / (L−1)`, `q = min(¾, f·e·L/(cB − rL))`, started at PR 86's boot face `(0.99999, 2.5715)`.
Native barrier at `q = ¾`: `L* = cqB/(e + qr)`: **pool 4.50·B, simple 2.571·B (= 18/7), squared 1.636·B, blend with a squared fraction φ: 4.5·B/(1.75+φ)**. For the simple type the chain stays on `L = 6qB/(1+q)` as `q` falls (q = 0.65 at L = 2.34, 0.60 at 2.20).
Replica checks [N]: `ode_amp.py` reproduces B2 (B(2.3415) = 0.98889, s₀ = 0.0651, wall(0.60) = 2.2031 / B 0.97855); `dchain_amp.py` (the PR 83 gate replica with the generalised constants) reproduces PR 86's chain (74 steps to L = 2.2015 at floor 0.60, count step 73 `s₀ = 0.0837`, discrete price 0.873946250 vs `lemmaW.md` 0.873946275).
With full doubling `q` stays at ¾: `s₀ = (B − 0.95238)/(L−1)` = const 0.0303 (the chain is a straight line), and the terminal `gPrincipal` gate (charge 4.5 unchanged) becomes tight only near L ≈ 1.8 (replica, `results/dch_doubled_long.json`).

### 5.4 Prices (exact Lean-return toolchain of `lemmaW/tc`, floor 3/5, role split; continuum chain unless "disc.") [N]

Sensitivities (continuum): `dθ/de ≈ −7.96e-4` per unit (−8.0e-6 per +1 %), `dθ/dc ≈ +2.2e-4` per unit (−1.35e-5 per −1 %), the wall moves by −0.0149 in L per +1 % of `e`; the count role's break-even slope is 0.0857, so the chain extends from L = 2.2031 until `s₀` returns to it.

«TABLE_PRICES»

### 5.5 How much is needed, and what absolute doubled mass that is

«TABLE_THRESHOLDS»

---

## 6. Ranking and lemma list (Q5)

«RANKING»

---

## 7. Flags, discrepancies and what I need

«FLAGS»

---

## 8. Files (`research/newpowers/r2/`)

«FILES»
