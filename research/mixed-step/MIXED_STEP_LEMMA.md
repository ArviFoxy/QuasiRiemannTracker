# The mixed source step (MStep): statement, proof chain, gates (draft, 2026-10-25)

Blueprint for the formalization (tasks MStep 1–4). Sources: `ADVERSARIAL_REVIEW.md` (verdict: e = 1,
c = 6), `SIL_LEDGER_TRACE.md`, `COLLET_LOW_TRACE.md`. The Lean maps are pending
(`FORMAL_MAP_COLLET.md`, `FORMAL_MAP_SIL.md`).

## 1. Statement

Notation. A face `G(B, Λ, h)` says: the ordinary initial moment is `≪ U^{1+ε}·H^J` whenever
`m₁ + m₂ + Λs ≤ B` and `0 ≤ s ≤ h` (paper69 (G1)). A node `n = (B, Λ, h, q, e, r, f)` follows
Collet's `Source` record, with `e` the allowance, `r` the low fee and `f` the high fee. Its LOW
parent is `low = (B₀, Λ₀, h₀, …)`, and β = B₀/Λ₀.

**MStep.** Suppose
- `G(low)` holds, the HIGH parent face holds (as in NFStep2), and the natural face holds;
- the mixed gates `SourceValid3(n, low, high)` of §3 hold.

Then `G(n)` holds.

Compared with Collet's step (NFStep2):
- **Amplifiers.** A pool of width `a = r` (fresh primes, sixth powers) is kept, plus a selected
  block of the input's live slots of total width `d(b)` (Sil's fourth-power transfer).
- **LOW payment** (G9 replaced):
  `a(1 − 6qβ) + d(1 + q − 6qβ) ≥ q(b + (t − B₀)/Λ₀) + r`.
  With `a = r` this reads `d = (q(b + (t − B₀)/Λ₀) + 6qβr)/(1 + q − 6qβ)`.
- **RAW scale:** `F′ = 1 − 6a − 6d`. The earlier face is called at `Q′ = F′ − δ − ρ`.
- **Descent:** `1 + q − 6qβ > 0`, i.e. `Λ₀ > 6qB₀/(1+q)`. Collet's step needs `Λ₀ > 6qB₀`.

## 2. Proof chain (per first-common geometry; review §1)

0. **Original MAIN norm** `𝓜` at radius μ. The radius is fixed by the first transform of the
   whole input, with the selected block still in its columns.
1. **Transfer.** Select a live block J of width `d ≤ b − f` by width (greedy with mesh,
   `GlobalSlotSelection`). Split each column `u = f·D·n`. The CRT, the ray split and the
   fourth-power identity (`MixedSupplierKernel.fixed_supplier_row_fourth`,
   `GaussTransfer.normalized_fourth_power`) give
   `V^{−1/2}Σ_u b𝔤(u,h) = Σ_{χ,ξ} π_{χξ} Σ_D [W^{−1/2} c(D) χ(fD) 𝔤(fD,h)]·G_ξ(D⁴h)`.
   Non-coprime `n, D` vanish on both sides.
2. **Cauchy–Schwarz** over `(χ, ξ, D)`: the count `#D ≈ W` is cancelled by the renormalization
   `V → V_res = V/W`.
3. **Pushforward** `(D, h) ↦ D⁴h` with bounded fibres (`PositiveFamily.weighted_pushforward`):
   `𝓜 ≤ C·U^ε·Σ_ξ 𝓜_res,ξ(μ + 4d)`. The pool's own identity (CA5) acts before or after; the two
   commute, since the pool primes avoid every slot.
4. **The residual is a Collet source** with slot type `ι \ J`, extra row twist `χ_n(f)²` and ray
   label ξ. ActualLow quantifies over every ray label.
5. **Second transform.** The coordinates become `(x0 + 5d, x1, x2 − 6d, x3 − d)`, so
   `RC3′ = RC3 − d` and the parent's scale is `x2′ = F′ − δ − ρ`.
6. **LOW branch (G12–G13 with d).** Erase the unselected excess, at rate `q` per unit, on the
   ActualLow rows. The width passed to the parent is `b − f − d`, and the cap is
   `min(z′, h₀Q′)` with `z′ = (B₀Q′ − P₁)/Λ₀`:
   - `E_{c,z} ≤ −[a(1−6qβ) + d(1+q−6qβ)] + q(b + (t−B₀)/Λ₀) − (q/Λ₀)(c − B₀δ) − q(1−1/Λ₀)f − B₁₂ − D ≤ −r`;
   - `E_{c,0} ≤ −a − d ≤ −r`;
   - h-branch as (G13) at `F′`.

   Geometries with `f > 0` have pre-dilation excess `X₀ − f(1 − 1/Λ₀)`, so they need less `d`
   and offer `b − f` (review O2).
7. **HIGH branch and terminal sectors** on the residual. The `O(d)` charges are at most the pool's
   per unit (review O3).

## 3. Gates `SourceValid3` (draft; mirrors Collet's `Record1252270103Finite/SourceFormulas.lean`)

With `t = B − Λ(b − e)`, `T = t + b`, `a = r`,
`den3 = 1 + q − 6qB₀/Λ₀`, `X₀ = b + (t − B₀)/Λ₀`:

- `d = (q·X₀ + 6q(B₀/Λ₀)·r)/den3` and `F′ = 1 − 6a − 6d`.
- The 16 scalar gates of `scalarGate`, with:
  - `den → den3`;
  - `F → F′`;
  - every pool charge `ka → ka + kd` (conservative; the review's per-unit transfer charges are
    smaller);
  - the amplifier range `1/75 − a → 1/75 − a − d`.
- New: `b − 2e − d ≥ 0` (the selected block is live width).
- `weakCap` at `F′`.
- `densityGate` (HIGH, sectors), with:
  - `a → a + d`;
  - `F → F′ − e`;
  - the HIGH slot width `S = b − 2e − d` (fewer marked slots for the gain; conservative).

**Continuum check.** `continuum_mixed.py` uses this convention (with `a = 0`; the `a = r` term
is O(1e-12)). From Sil's face at s = 0.016 it gives faces with slope 2.52 → 2.17. With the Lemma D
return at `s_P = 0.052`, `s_C = 0.054`, θ* = 0.8744022.

## 4. Open items for the formal proof
- (T) at Collet's columns: an adapter from Sil's supplier records to Collet's
  `finiteColumnCoefficient … sourceModifier … β · Γ`.
- Collet's downstream on the residual source (generic in ι?) with the coordinate shifts.
- The f-dependent choice of `d` per geometry, and the greedy selection's mesh loss.
