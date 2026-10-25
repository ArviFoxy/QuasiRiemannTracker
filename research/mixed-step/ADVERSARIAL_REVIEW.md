# Adversarial review of the mixed fourth-power source step (2026-10-25)

Read-only: nothing was edited or built. "(inf.)" marks my own inference; every other claim is cited.

Path prefixes:
- `C/` = `lean-env/qrh/Submissions/hailey_collet_1252270103/`
- `S/` = `C/Record1252270103Source/`
- `F/` = `…/arvi_repeated_marks_on_sil_face_20261025/FourthPower/`
- `src` = `paper69/sources.tex`
- `fnd` = `paper69/foundations.tex`

## Verdict

**CONFIRMED with e = 1 and c = 6. The c = 4 reading is REFUTED.**

The ledger books "column size −2d" as an RC3 saving. That term belongs to the RAW-scale coordinate itself, so the earlier face is called at Q − 6d, not Q − 4d.

With c = 6 the transfer prices exactly like a pool of the same width: it saves 1 and costs 6 of scale. It also removes the selected slots from the width passed to the parent, and that removal is the whole gain: Λ > 6qB/(1+q) instead of 6qB.

Of the float runs, `cont_c6` is the relevant one (slopes 2.32 down to 2.17 over s = 0.040–0.054). `cont_c4` (≈1.57) should be discarded. I found no first-order obstruction; the analytic lemma (§3) is still unproved.

## 1. The LOW-branch chain

Scope: one orientation and one first-common geometry.

Notation:
- A = log_U V, where V = X₁X₂∏Pᵢ includes the selected volume W ∈ [U^d, U^{d+ω}].
- μ = 2A − c − c̄ + R + E − 1 + (c̄−c)₊ + 6a + ω is the first MAIN radius (`src`:1529; `C/Cycle61/Physical/InitialMass/SecondHighCoordinates.lean`:32 with M = 1). Here c̄ is the Lean's d.

The chain:

0. **Original norm.** 𝓜 = Σ_h Ω(Nh/U^μ)|V^{−1/2}Σ_u b(u)𝔤(u,h)|². The radius μ was fixed by the first transform of the whole input, with the block still in it (K₀ = 2A − … − m, `fnd`:4330).
1. **Transfer.** Write u = f·D·n, with f the frozen supplier, D the selected product and n the residual. CRT, the ray split and the fourth-power identity give
   V^{−1/2}Σ_u b𝔤(u,h) = Σ_{χ,ξ} π_{χξ} Σ_D [W^{−1/2} c(D) χ(fD) 𝔤(fD,h)] · G_ξ(D⁴h),
   with G_ξ(k) = V_res^{−1/2} Σ_n β_ξ(n) 𝔤(n,k) and V = W·V_res (`F/MixedSupplierKernel.lean`:141, 174; `F/GaussTransfer.lean`:81–102). When n is not coprime to D, both sides vanish (`GaussTransfer`:81–96). So holes and valuation-2 coincidences need no separate argument.
2. **Cauchy–Schwarz over (χ, ξ, D).** The count gives +d and the renormalization V → V_res gives −d, so the net change is 0.
3. **Pushforward.** (D,h) ↦ D⁴h has bounded fibres, so the bound is ≤ C·Σ_ξ 𝓜_res,ξ(μ + 4d), on residual columns of size A − d.
4. **Second transform.** In the Lean coordinates (`SecondHighCoordinates`:32–34; x2 + MAIN = 2(A−c) + E + Lc + ε by `C/Record12518109Raw/RawWeight.lean`:23–33):
   - outside scalar: x0′ = (μ+4d) − (A−c−d) + (g₂−t₂−b₂) = x0 + 5d;
   - retained frequency cap: x2′ = 2(A−c−d) + E + Lc + ε − (μ+4d) = x2 − 6d;
   - remaining raw volume: x3′ = x3 − d;
   - x1, labelSide and labelSurplus are unchanged, because the target keeps V.
5. **RAW excess.** RC3′ = x0′ + x1 + x2′ − labelSide − labelSurplus = RC3 − d, or −a − d with a pool as well. **So e = 1.**
6. **Scale.** x2 is the scale handed to the parent: `modified_deficit_and_coordinate` (`S/Coefficient/RegularLowRetainedRadial.lean`:38) sets x 2 = F − δ − ρ. So Q′ = 1 − 6a − 6d − δ − ρ. **So c = 6.**
7. **LOW/HIGH split.** ActualLow is a predicate on the row's whole twisted family, for every ray label (`C/Cycle61/Moment/LowBranch/Gate.lean`:19–29). The erasure bound Z^{qw} is per slot (`C/Record12518109Source/LowGate.lean`:37–46). Both apply verbatim to the residual's rows and its unselected slots.
8. **Erasure.** The passed width is b − f − d. The cap is min(z′, h₀Q′), with z′ = (B₀Q′ − P₁)/Λ₀ and P₁ = t − c + f ((G10), `src`:1572–1578).
9. **Parent call.** G(B₀, Λ₀, h₀) is applied at U^{Q′}.

**Result.** The z-branch follows (G12)–(G13) exactly (`src`:1593–1612). With β = B₀/Λ₀:

E_c ≤ −[a(1−6qβ) + d(1+q−6qβ)] + q(b + (t−B₀)/Λ₀) − (q/Λ₀)(c − B₀δ) − q(1−1/Λ₀)f − B₁₂ − D.

- **Payment:** a(1−6qβ) + d(1+q−6qβ) ≥ qX₀ + r.
- **Descent:** Λ > 6qB/(1+q).
- **Zero branch:** −a − d.
- **h-branch:** closes as in (G13), given z₀′ ≤ h₀F′ with F′ = 1 − 6a − 6d.
- `raw_erasure_identity` (`C/Record12518109Source/LowLedger.lean`:59) is affine in a, F and f, so it carries over under these substitutions (inf.).

**Sanity check** (inf.). In large-sieve form:
- pool: (1/P)·𝓜(LP⁶) ≈ LP⁵V + (V²/P)·χ(V²/LP⁶);
- transfer: W·𝓜_res(LW⁴) ≈ LW⁴V + (V²/W)·χ′(V²/LW⁶), where χ′ has d fewer slots.

The RAW saving and the RAW scale are identical. The transfer has the cheaper diagonal and passes fewer slots.

## 2. Objections

### O1 (decisive against c = 4): the column term is the scale

The ledger keeps "RC3: column −2d" and "Q: −4d" together, and the two are incompatible.
- In the Lean, x2 is both an RC3 summand and the parent's scale (step 6).
- The column size enters RC3 only through x2.
- MAIN cancels in RC3 (x0 against x2) but not in Q.

The trace line "MAIN radius −2d + 4d = +2d" (`COLLET_LOW_TRACE.md`:142) re-derives MAIN from the residual's column size. But μ is set by the first transform of the full input, and the pushforward can only enlarge it.

Sil's ledger agrees:
- the residual is evaluated at Rdecl = Q − 2·log selectedVolume − … (`F/OuterFreshRootAdmission.lean`:87–92);
- it then pays 4d inside its own gate P + 2S + 4d < R (`F/MixedFirstPaidCosts.lean`:127);
- that is 6 of scale per selected unit.

So the "−2d" is not an extra cost on top of e = 1; it is the same term that produces e = 1. The proposal's "c = 6" alternative is right, though for this reason rather than as an extra charge.

### O2 (minor): "replace" fails, "supplement" works

Selected slots must still be live after the first common allocation, so d ≤ b − f. The frozen width f can reach b (0 ≤ f ≤ min(c, b), `src`:1570).

Consider a geometry with f ≈ b and B₁₂ = D = 0. A pure transfer leaves E_{c,0} = −B₁₂ − D − d ≈ 0. That leaves no reserve for the scheduled losses, and (G13) relies on min(a, g) for that (`src`:1614). So a pool with a ≥ r must stay.

Its own regress a(6qβ − 1) is harmless (inf.):
- At the pivot X₀ ≈ e, so (G10) gives the pre-dilation excess X = −f(1 − 1/Λ₀) − (c − B₀δ)/Λ₀ ≤ 0.
- Geometries without live slots therefore have a margin of at least f(1 − 1/Λ₀), which is much larger than a, and they create no excess.
- Geometries with X ≈ 0 have f ≈ 0, so about b of live width is available to the transfer. Its surplus d(1+q−6qβ) absorbs a(6qβ − 1).

Also required: (G11) at F′, i.e. B₀F′ − t − b > 0. At the pivot this reads 6Bd < (Λ−1)b.

### O3: the other components cost O(d), each no more per unit than the pool

| component | pool, per unit a | transfer, per unit d (inf.) |
|---|---|---|
| zero frequency / true diagonal | 5 (`src`:1115–1124; gate 1−T−5a, `C/Record1252270103Finite/SourceFormulas.lean`:34) | 4: radius only. Equals Sil's W³ row P+S−R+3d (`F/MixedLedger.lean`:58) at R = Q−2d with P+S = A−d. |
| fixed-inducing / centered | 4 in the exponent, 9 in (G5) (`src`:1533–1553) | 3: Sil's 7d/3 row at R = Q−2d; same value from the (MF3.74) analogue (`fnd`:4700–4716) |
| HIGH | 5 − 6ρ (`C/Record12518109Natural/HighAllocation.lean`:29–33) | 5 − 6ρ − ν, which is 1.0–2.5 on ν ∈ [½, ¾]. The HIGH value is x0 + x1 + ρx2 + νx3, and x3 falls by d. |

So the convention in `continuum_mixed.py` ("other gates see d as costly as the pool") is conservative. At the pivot, d ≈ r/den ≈ 10⁻⁵ (FINE fees, `faceless-chain/gates.py`:19), so these charges do not move the slope.

### O4: the residual is an admissible instance

- **Common coefficient.** Sil's residual is one vector common to all D (`fixedCommonCoefficient`, `MixedSupplierKernel`:133).
- **Twists.** It carries χ_n(f)² and a ray character ξ. The first is a row shift; the second is covered because ActualLow quantifies over every ray label.
- **Seeds.** The seed survives with (seed, D) = 1 (`commonGate`/`full_gate_split`, :65, :77).
- **Holes.** These are exact (`crossGate`, :58).
- **Fifth-freeness.** Comes from the retained restriction (:228). Collet's columns have valuation ≤ 2 (`S/Collision/Projector.lean`:40).

### O5: the red flag is explained, not refuted

**(a) The natural ledger also closes with c = 6.** In (MF3.60)–(MF3.72) (`fnd`:4447–4669), the transfer has three effects:
- the allowance exceeds the child width by Δ + d;
- the child width drops by 6d;
- the child's length and slots each drop by d.

The capacity defect therefore moves by (6−Λ)d, and deletion pays for it at κ/Λ. This closes iff Λ ≥ 6κ/(1+κ) = 18/7 (inf.).

**(b) The natural induction has a separate wall at Λ = 3.** The centered comparison (MF3.49) needs q_κ = Λ − 1 > 2. Its margins M/3 − t(1+2/q_κ) and M/2 − t(2+2/q_κ), as t ↑ M/6, both equal (q_κ−2)M/(6q_κ) (`fnd`:4253–4269). The choice L = M/4 is forced by (MF3.80) (`fnd`:4777–4783). With the existing centering, the natural analog therefore stops near 3, not 2.57.

Collet's step has no such wall. Its centering is (G4)–(G5), which uses the natural face only for the reference rectangle (`src`:1436–1481), and the current chain already sits at 2.90.

**(c) Sil's 3.72 is no lower bound for an induction.** Sil's nonexceptional bound has no capacity constraint:
- every live slot is deleted;
- the plains are bounded only by a fixed cap;
- the bound is Z^{width + κΣw} (`F/MixedUniformSource.lean`:30–64).

So the dilation never appears there. The 6 per selected unit and the 2 per live unit are paid in terminal gates. Those gates are first order in a direct face (d = 0.43(S + d)), but only O(d) per step in an induction.

**What remains unexplained** is why nobody built the inductive natural face at ≈3. The likely reason is effort: it means re-proving `fnd` §7.2 with the transfer.

## 3. Open: the missing lemma

Two pieces are needed.

**Transfer at Collet's first MAIN layer.** For each first-common geometry and each live block of width d ≤ b − f:
- 𝓜 ≤ C·U^ε·Σ_ξ 𝓜_res,ξ(μ + 4d);
- the residual is a literal Collet source with volume V/W and twist χ_n(f)²ξ;
- its second transform has coordinates (x0 + 5d, x1, x2 − 6d, x3 − d).

**Collet's step on that residual.** Run Collet's three-branch LOW erasure, the HIGH gain (LD2) and the terminal sectors on it, with x2 redefined as 1 − 6a − 6d − δ − ρ.

Finally, add certificate gates with the O3 charges and a pool a ≥ r. In a finite certificate, d per step is finite, so the O3 charges must fit actual slack.
