# Formalization plan for the mixed source step (2026-10-25)

Synthesis of `FORMAL_MAP_COLLET.md` and `FORMAL_MAP_SIL.md`, with two of their open points settled
here on paper: the booking of the saving, and the collision columns.

## 0. Value at stake

The exact model (`README.md` §10) gives:
- the fan (46 steps), the junction and the 8-piece family pass the draft gates;
- the return, with `dMinus > 1/2`, `s_P = s_C = 0.058`, caps 0.075 and `h ≈ 0.8044`, gives
  **θ\* ≈ 0.87427**, i.e. −3.4e-4 against PR 76.

All of it depends on one new theorem: the mixed step (`NFStep3` with `SourceValid3`).

## 1. The two settled points

### 1a. The saving is e = 1 if the residual is booked against the original target

Collet's coordinates (`SecondHighCoordinates.lean:20`) are
- `x0 = −a + (μ − (A − c)) + (g₂ − t₂ − b₂)`, where the −a is the pool's `1/|P|`;
- `x2 = 2(A − c) + E + Lc + ε − μ`;
- `x3 = A − c − b₂`;

with `μ = 2A − c − d + R + E − M + (d − c)₊ + 6a + ω`.

**For the residual of a transfer of width δ**
- The volume becomes `A − δ`, the radius `μ + 4δ`, and there is no cardinality factor.
- So `x0 + 5δ`, `x2 − 6δ`, `x3 − δ`.
- The C-S count (+δ) cancels the renormalization `V → V_res` (−δ). So
  `𝓜(normalized by V) ≤ C·Z^ε·Σ_ξ 𝓜_res(normalized by V_res, μ + 4δ)`.
- Collet's second-transform bound for an `Input` of volume `A′` has the form
  `Z^{RC3 + labelSide(A′)}`, with `labelSide` of slope 1 in `A′` (the normalized off-diagonal is
  `≈ V·χ(V²/R)`).
- Applied to the residual it gives `Z^{RC3_res + labelSide(A − δ)}`, where
  `RC3_res = (x0 + 5δ) + x1 + (x2 − 6δ) − labelSide(A − δ) − S = RC3`.
- Against the original target `Z^{RC3 + labelSide(A)}` that is a saving of exactly δ. **e = 1.**

**Collet's formula evaluated at `(A − δ, a + δ)`** gives `x0 + 4δ` with `labelSide(A − δ)`. Its
RC3 and HIGH excess are the same. So the LOW payment lemma `modified_low_coordinate_payment` can
be reused at the virtual amplifier `a + δ`, width `b − δ` and scale `F′ = 1 − 6a − 6δ`. It then
reads `a(1 − 6qβ) + δ(1 + q − 6qβ) ≥ qX₀ + r`.

**The trap.** Booking the residual's own target `labelSide(A − δ)` against the actual
`x0 + 5δ` gives e = 0. The formal statement must carry the original first-layer scalar (volume
A) and the residual energy normalized by `V_res`.

### 1b. Collision columns pay better than the transfer

A collision is a selected slot prime `p | v₀v₁` (Collet's projectors allow valuation 2; Sil
restricts these away).

For a collision pattern `C ⊆ J` of width w, with `D_C` the colliding product:
- `𝔤(D_C² m, h) = 0` unless `D_C | h` (baseline `primePowerGauss_support`).
- For `h = D_C h′`, the `D_C²` factor is a cubic Gauss sum mod `D_C` (`primePowerGauss_lift`):
  - `√N(D_C)·χ_{D_C}(h′)⁻²·const` on the sublattice;
  - the `h′`-twist is common to all columns for fixed `D_C`, so it drops out of `|Σ_m|²`;
  - the `m`-twists `χ_m(D_C)^k` are multiplicative in `m`, so they go into the slot weights and the
    row character, as with Sil's `common_height_character`.
- C-S over the `D_C` values (×W_C), then the residual at radius `μ − w`, with `C` removed and the
  plain shortened: `V_res = V/W_C²`. So `𝓜_coll ≤ W_C·𝓜_res,C(μ − w)`.
- **Ledger:** RC3 −w (e = 1), scale −3w (against −6 for the transfer), live width −w, plain
  length −w (capacity +w/Λ₀).
- Pattern `C`: transfer `J∖C`, reduce `C`. That costs at most what transferring all of `J` costs,
  so the certificate gates of the full transfer cover every pattern.

### 1c. Granularity

Collet's analytic inlet `FixedSubsetTruncatedSupplier` quantifies over slot widths `w i ≤ mesh`
with the mesh arbitrarily small (`InitialTruncatedContract.lean:21`). A greedy block then reaches
`Σ_J w ∈ [δ, δ + mesh]`.

### 1d. Live width below δ

Geometries with frozen width f have their own saving `q(1 − 1/Λ₀)f` (G12). Since
`δ = O(qX₀/den3)` and the f-saving grows at rate `q(1 − 1/Λ₀) ≫ den3`, those geometries need no
transfer once `f ≥ den3·δ/(q(1 − 1/Λ₀))`. Certificate gate: for `f ≥ b − δ`, the pool-only payment
`a(1 − 6qβ) + q(1 − 1/Λ₀)f ≥ qX₀ + r`.

## 2. Stages

| stage | content | size (inf.) | depends on |
|---|---|---|---|
| L1 | **Ledger in Lean.** The residual coordinate identities (`x0 + 5δ`, `x2 − 6δ`, `x3 − δ`), RC3 −δ against `labelSide(A)`, the mixed LOW payment (`modified_low_coordinate_payment` at `a + δ`, `b − δ`, `F′`), the HIGH excess with δ, and the collision variants. Pure real algebra over Collet's coordinate functions. | 0.8–1.5k | — |
| L2 | **Transfer lemma** `collet_main_selected_transfer` in Collet's types, under (S) no selected supplier of the seed and (Col) no collisions. Reuses Sil's generic (T) chain (`fixed_supplier_row_fourth`, `first_ray_sq`, `weighted_pushforward`, `frequency_norm_bound`); new residual `Input.restrict`, box split, coefficient factorization. | 1.5–3k | — |
| L3 | **Collision reduction.** Mod-p² sublattice lemma for `sexticGauss` at `p²m`, the twist absorption, C-S over `D_C`, and the residual `Input` with shortened plains. Discharges (Col). | 0.8–1.5k | L2 |
| L4 | **Post-pool MAIN.** Residual twin of `eventual_selected_second`/`allocatedFamily`, the centered complement at `σ = 3a + 2δ`, remainders, and a mixed `balanced_of_regular`. | ~3k | L2 |
| L5 | **LOW/HIGH waist.** Generalize `FirstStage`, `Selection`, `allocatedRegularFamily`, `RegularPointAt`/`RegularLowAt`; split `amp` into pool a and transfer δ; the ray-shift for ξ. Fork with scripted patches, as for the repeated-marks fork. | 8–14k (mostly vendored) | L1, L4 |
| L6 | **Certificate and step.** `SourceValid3` (16 scalar gates with `den3`, `F′`, `a + δ`, `b − 2e − δ`, the live<δ gate, (G11) at `F′`), the HIGH gate with δ, `NFStep3`. Generator updates: fan steps, family pieces, return with `dMinus > 1/2`, `s_P`, caps, `h`. | 1–2k + data | L1, L5 |

**Order.**
1. L1 and L2 in parallel: L1 de-risks the numbers, L2 the analysis.
2. L3.
3. L4 and L5.
4. L6.

**Independent of the step:** return-side patches (the `dMinus_lower` field, `cap = s_P`, `h`, face
caps) can be prepared at any time.

## 3. Ground rules for the Lean work

- **Where.** New modules go in `lean-env/qrh/Submissions/arvi_mixed_step/` and import the PR 76 tree
  `arvi_repeated_marks_on_sil_face_20261025` (Sil's vendored `FourthPower`, the fork), Collet's
  tree and the baseline.
- **Build.** Build module by module with `lake build Submissions.arvi_mixed_step.<Module>` from
  `lean-env/qrh`. Disk is tight (about 7 GB free), so do not clean `.lake`.
- **Axioms.** No `sorry`, no new axioms. `#print axioms` must show only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Records.** Keep every lemma proved or disproved during the work in `research/lean-lab/` or the
  module tree. Failed attempts are recorded in `research/mixed-step/LEAN_NOTES.md`.
