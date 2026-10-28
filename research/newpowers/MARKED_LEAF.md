# The marked HIGH leaf (theory and build spec, 2026-10-28)

**Target.** θ ≤ 0.8739358 (2e-5 below PR 86). Route: density floor 3/5 (Collet's `a ≥ 4/5`
lemma) + longer density chain + count/physical role split + **marked HIGH leaf** (+ floor 0.55,
`0.999 → 1`, incumbent bootstrap as margin). Numbers below: my own computations unless marked;
B2/B3/lemmaW numbers are models, not proofs.

## 1. What PR 83's HIGH branch pays (Lean)

- Rows of the packed energy that are not LOW at the cut `q` are HIGH; each sits in a buffered
  bin `b ≥ (q+1)/2`, `ν = 2b − 1 ∈ [q, 3/4]` (`Density/LeafRows.lean`, `selectBin_high`).
- Pointwise: `|row|² ≤ K·Z^{ν(P₁+P₂+Σ_k w_k)+small}` (`LeafHighRow.lean:58`, `high_row_bound`,
  from Collet's `actual_high_retained_row`): **every slot counted at full amplitude**.
- Count: `#rows(bin) ≤ C(1+T')^J (bΦ Z^M)^{ρ(ν)+loss}`, `ρ(ν) = 1 − 10ν/(15−6ν)`
  (`LeafHigh.lean`, `high_row_count` ← `fixed_natural_dictionary_raw_density`): **unmarked**.
- Price: `highTerm ν P s M = ν(P+s) − (1−ρ(ν))M`; ledger `ν(P_C+s) − (1−ρ)H ≤ u`
  (`Density/StepGates.lean:152`, `ds_high_aux`), with `P_C + s ≤ B − (L−1)W − u` and the root
  constraint `P_C + (c_g − f) + L·S ≤ B` (`ds_defect_aux`). Gate `highJ` (`Source/HybridGates.lean:62`).

## 2. The marked bound

Classify HIGH rows also by the amplitude bins `g_k ∈ [0, ν/2]` of their marked prime slots (as the
return's detector does; bins are fixed per fibre, `DetectorRawFiber.lean`, `fixed_bin`). For a class
with slot amplitude mass `a = Σ_k w_k g_k = x·ν·s`, `x ∈ [0, 1/2]`:
- pointwise: `|row|² ≤ Z^{νP + 2a + small}` (plains-only high bound × slot amplitudes);
- count: `#rows ≤ Z^{M·R(ν, p) + loss}` with `R = countingR κ ν p`
  (`Cycle61/Arithmetic/Bernstein/Feedback.lean:17`), `p` = the class mean amplitude relative to `ν`.
  Identity (checked by algebra): `countingR κ ν 0 = (15−16ν)/(15−6ν) = ρ(ν)`; `R` decreases in `p`.

Marked price: `sup_{ν∈[q,3/4]} sup_x [νP + 2xνs − (1 − R(ν, p(x,s)))M]`.

**Where the gain is forced.** Because `P_C ≤ B − L·S − (c_g − f)` (root constraint), plains cannot
absorb slot width: with `s` the retained slot width, `P_C + s ≤ Ψ − (W − u − s)`. The marked price
is increasing in `s` and in `x` on the relevant range, so the binding row has `s = W − u` and `x = 1/2`:
gain `(ρ(ν) − R(ν, p*))·H` with `p*` set by `s = W − u` (≈ the step's crossing width `s₀` at `v = 0`).
Gate: `highJ` with `1 − ρ(ν)` replaced by `1 − R(ν, p*)`.

## 3. The count's supply and the three variants

The count selects a sub-block of slots of width `z ≤ z* = (1−r)/2 − ν` (or the plain analogue); the
fibre field `supply : 7/37 ≤ Σ widths` only guarantees such a sub-block exists
(`DetectorBranchBudget.lean:52-69`). The leaf's slots have width `s ≤ 1/10`.
- **(a) black box:** pad with zero-amplitude dummy slots to `7/37`; `select_physical_product`
  guarantees `2·(mean bin)·z`, so the amplitude is diluted to `p = s/(2·7/37)` (relative widths,
  row scale `d ≈ M ≈ 1`). Example `ν = 0.6, s = 0.07`: `ρ − R = 0.0046`.
- **(b) limited supply:** the count re-derived with supply `= s` (real slots, `p = 1/2`). Example:
  `ρ − R = 0.0066` (B2's re-derivation: supply 0.12 already reproduces the full count for `ν ≥ 0.6`).
- **(c) face-based count:** plain-marked moment from the parent face `G(B₀, L₀, c₀)` instead of the
  natural theorem (κ = 3/4), as the return's `CountScheme` windows do (`branch_affine`): at
  `ν = 0.62` the count drops by a further ≈ 0.0006 (p = 0.2) to 0.0017 (p = 1/2).

Model prices (B2, floor 3/5, role split; to be re-checked with the final gate): (a) 0.8739390;
(a) + floor 0.55 + `0.999→1` 0.8739356; (b) ≈ 0.8739344; plus bootstrap −1.3e-6.

## 4. Build order

1. Floor fork (`Submissions.arvi_density`, floor parameter, `qf = 3/5`) — in progress.
2. Bridge (leaf HIGH rows → detector fibres; slot conversion `positiveSlotRow` ↔ `canonicalPrimeAmplitude`;
   zero guard → `SupportedWitness`; the four count moments from the natural theorem / parent face and
   the inverse marked moment; padding) — map in `BRIDGE_MAP.md` (in progress).
3. Marked HIGH energy theorem and the new price `markedDensityPrice`; `PricedPackedSource` for it.
4. Gate `highJ_marked`, step gates, certificate generator (two-parameter in `(v, x)` unless
   monotonicity in `x` is proved), chain to the new wall, two-source return, package.
5. Then (b)/(c) for margin.
