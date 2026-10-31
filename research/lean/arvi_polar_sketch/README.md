# arvi_polar_sketch: the polar theorems with `sorry`, and what they buy downstream

**Sketch package — contains `sorry` on purpose.** At Arvi's request (2026-10-31), the polar theorems are stated first
with `sorry`, to see what they give downstream before anyone commits to proving them. Nothing that a submission
imports may import this package.

- The only `sorry` is `polarInput` (`Polar.lean`).
- Every consequence takes the polar input as a hypothesis (`PolarInput`). So every theorem below is proved outright,
  with standard axioms only (`#print axioms` at the end of each file).

## Files

| file | content |
|---|---|
| `Polar.lean` | `thetaCorr` (full-range twisted theta correlation of a radial weight); `PolarInput k q W v₁ ε`; **`polarInput` (sorry)**; `mellin_zero_bounds`; `heightTwist`, `mellin_heightTwist`, `height_meanvalue` |
| `Bessel.lean` | `twistNorm_pos`, `mem_twistBox_of_norm_le`, `shell_bounds`; `weighted_dyadic` (pure analysis); `weighted_bessel` |
| `KWall.lean` | `FullRangeCorrected k q γ` (input C, full-range form, an open hypothesis); `kwall_source_term`; `source_exponent_le` |

## The stated input (`polarInput`)

For order `q ∈ {6, 3}` (`k = 6/q`), a smooth weight `W` supported in `[v₀, v₁] ⊂ (0, ∞)` and `ε > 0`, there are
residues `ρ(m)` of polynomial size such that:
- **pointwise:** `Σ_{N n ≤ v₁X} W(N n/X) g̃_k(n) conj χ_n(m)^k = ρ(m) W̃(s₀) X^{s₀} + O(X^{1/2+ε} (1 + N m)^A)`, with
  `s₀ = 1/2 + 1/q`;
- **on average over twists:** the errors have mean square `≪ (M X)^{1+ε}` over twists of norm `≤ M`.

For `q = 3` this is Patterson's theory plus David–de Faveri–Dunn–Stucky (Lemmas 6.6–6.7). For `q = 6` it is the
Kazhdan–Patterson theory of the 6-fold cover. Neither exists in any proof assistant; the baseline has only the
pole-free cubic reflection.

## What it buys (proved, given the input)

1. **Mellin-zero vectors are off the spikes** (`mellin_zero_bounds`): square-root size, pointwise and on average.
2. **The K-wall's source term is absorbed** (`kwall_source_term`, `source_exponent_le`).
   - Input C (`FullRangeCorrected`) carries the spike strengths `(B/N m)^{1/q}`.
   - With it, a Mellin-zero radial vector has energy `≤ C B^{1+γ+ε}‖v‖² + O(log M · B^{1/q} M^{1+ε−1/q} X^{1+ε})`.
   - With `M ≤ B^{1−qγ}` the second term's `B`-exponent is at most `1 + ε`, below the diagonal `B^{1+γ}` times
     `‖v‖² ≈ X`.
3. **The low-height remainder is explicit** (`height_meanvalue`).
   - For the weight `W(t) t^{−iγ}` of a plain block at a zero of height `γ`, the polar term survives with the factor
     `W̃(s₀ − iγ)`.
   - A zero of `W̃` at `s₀` removes it only at `γ = 0`.

## What the exploration found (interface findings)

1. **The spike family must be full range.**
   - `arvi_kwall/SourceSpike.lean`'s `GradedTwoSided` corrects by twisted thetas cut into sharp dyadic windows with
     power profiles `(2^w/N)^{j/2}`.
   - A Mellin-zero vector inside one window meets profile `j` with the factor `W̃(s₀ − j/2) ≠ 0`. Across windows it
     meets partial Mellin integrals that do not vanish. So the rescue cannot work against that family.
   - Input C must therefore be stated with full-range spikes, one per twist (and height): `FullRangeCorrected`. That
     is also what a Poisson step produces: dual frequencies give twisted thetas over the whole source range.
2. **Heights from the coupling.**
   - Separating the Poisson coupling `Ŵ(A N h/(N b N b′))` by Mellin gives corrections twisted by `N^{it}` with `t`
     spread over `|t| ≲ 1`. By (3) above, a single zero at `s₀` does not kill those.
   - The numerics (`rip/theta/theta_level_profile.py`) say the actual dual polar part is rank one in the radial
     direction at an effective pole near `s₀`, with a bounded 2.5% floor.
   - So the correction functionals of input C should be the actual dual polar functionals, and their rank-one radial
     structure has to be proved. It is a Rankin–Selberg-type statement for the theta residues. This is not yet in
     any written plan.
3. **Leaf vectors are convolutions.**
   - The K-wall leaf (R1) and the reference's vectors are convolutions of smooth factors with prime slots.
   - The polar input for convolutions follows from the single-sum input only in the dilation aspect (twists
     `m · b₂^{±k}` for the short factor `b₂`). That is numerically supported (`theta_twist_meanvalue_conv*.log`) but
     not derived.
4. **Where the walls enter the banked chain.**
   - K-wall: `SelectedRootEnergy K` (`arvi_selected_leaf/R1Statement.lean`), proved for `K ∈ [0.500001, 3/4]`. The bar
     needs `K ≈ 0.488`, i.e. Λ ≈ 1.967.
   - Reference wall: `ReferenceAt` clause 1, `ρ ≤ (1 − B) + (L − 2)S − (9/2) sel S`
     (`sil_density_split_20261026/CubeFree/StepData.lean`). It is consumed in `CubeFree/RootParameters.lean`
     (`interval_gap`) to keep the centred root exponent below `upperOne`. Relaxing the `2` means forking
     `RootParameters` and the files that apply the reference large sieve below `upperOne`, with target 2 supplying
     the new range.

## Verdict so far

- The polar input is a small, clean interface (one statement per order). Downstream it delivers exactly the K-wall's
  source-spike term and the reference's spike term.
- θ still needs:
  - input C in full-range form, with its correction functionals shown to be rank one in the radial direction;
  - the convolution (dilation-aspect) version of the polar input;
  - a separate argument for the low-height slice;
  - the two bank-chain forks.
