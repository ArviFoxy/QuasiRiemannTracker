# D8: the face region. Cauchy–Schwarz closure, consumers, true-region properties

Notation: a configuration is (m₁, m₂, s), meaning plain lengths m₁, m₂ and total slot length s, all in
units of the family exponent M = 1. A face k proves the configurations with

  m₁ + m₂ + Λ_k s ≤ B_k,  s ≤ cap_k,  0 ≤ m_i ≤ plainHi.

E(s) = max_k (B_k − Λ_k s) is the envelope, taken over the faces with s ≤ cap_k.

## 1. The Cauchy–Schwarz rule (valid)

**Rule.** If (m₁, m₁, 2s_A) and (m₂, m₂, 2s_B) are proven, then (m₁, m₂, s_A + s_B) is proven.

**Why it is legitimate [Lean, read].**
- The face energy is `CenteredMomentInductionEnergy.energy`:
  Σ'_z [keep z]·Re Φ(‖z‖²/K)·|W₁-sum·W₂-sum·∏ rowSlot|²/(X₁X₂∏P), with Re Φ ≥ 0 by hypothesis.
  Cauchy–Schwarz over z gives
  energy(F₁, F₂, S_A ⊔ S_B) ≤ energy(F₁, F₁, S_A ⊔ S_A)^{1/2} · energy(F₂, F₂, S_B ⊔ S_B)^{1/2},
  and the normalization squares exactly.
- The squared configurations are legal face inputs: any profile pair, any finite slot type (∀ α),
  and duplicated pools with the same θ, σ, v.
- `Profiles.control` = c(W₁)·c(W₂), so the controls combine exactly. The constants, the degree, ε
  and "for all large Z" combine too.

## 2. Two propositions (proved here)

**Proposition 1: no gain for equal plain lengths.** If m₁ = m₂ = m, the rule proves (m, m, s) only when
2m ≤ E(s).

*Proof.*
1. The endpoints are (m, m, 2s_A) and (m, m, 2s_B). They need 2m ≤ E(2s_A) and 2m ≤ E(2s_B).
2. E is non-increasing, so min(E(2s_A), E(2s_B)) = E(2·max(s_A, s_B)) ≤ E(s), because max(s_A, s_B) ≥ s/2. ∎

**Proposition 2: one step gives the whole closure.**

*Proof.* Every endpoint of the rule has equal plain lengths. By Proposition 1 such a point is proven
by the rule only if a face already proves it. So a second application adds nothing. ∎

Hence the proven region after Cauchy–Schwarz is exactly

  R_CS = faces ∪ {(m₁, m₂, s) : ∃ s_A ∈ [0, s], 2m₁ ≤ E(2s_A), 2m₂ ≤ E(2(s − s_A))}.

**Other interpolations add nothing.** Hölder with other exponents needs each factor, raised to its
power, to be a face configuration. That allows at most two plain slots, so each plain must sit in an
exponent-2 factor, and Cauchy–Schwarz is the only option.

## 3. Size of the gain (the 130 faces) [numerical]

Best total P = m₁ + m₂ at slot length s:

| s | face envelope E(s) | Cauchy–Schwarz | gain | split (s_A, m₁, m₂) |
|---|---|---|---|---|
| 0.02 | 0.94856 | 0.94889 | +0.0003 | (0, 0.500, 0.449) |
| 0.04 | 0.89779 | 0.90414 | +0.0064 | (0, 0.500, 0.404) |
| 0.05 | 0.87364 | 0.88483 | +0.0112 | (0, 0.500, 0.385) |
| 0.06 | 0.85058 | 0.85911 | +0.0085 | (0.010, 0.474, 0.385) |
| 0.07 | 0.82875 | 0.83372 | +0.0050 | (0.020, 0.449, 0.385) |

The gain always comes from an unbalanced split: one plain near ½ with few or no slots, the other
plain shorter and carrying the slots.

## 4. Consumers: why the current return gains nothing [Lean + derived]

- **Count.** `AffineMarkedMoment` (Collet `Record12518109Count/MarkedFiber.lean:20`) uses the same
  length F.m for both plains (2m + Λ·Σw ≤ B). That is balanced, so Proposition 1 applies: no gain.
- **Physical numerator.** `affine_fourier` (`ReturnD/PhysicalDirect/Fourier.lean`) needs the bound
  for all pairs X₁, X₂ ≤ U^n. The geometry applies it at (n₀+t, n₀+t, z) (`PhysicalDirect/Geometry.lean`).
  The binding case is the balanced corner, so again no gain.
- **Count lower bounds.** The count keeps only slots with positive amplitude bins, with a pointwise
  lower bound on every counted row (`select_physical_product`, `Hecke/DetectorPhysicalSelection.lean:32`).

**What would use the rule.** A consumer whose binding configuration is unbalanced. For example, the
numerator could be restructured into two pieces of unequal maximal length. At the binding edge newTop
(plain total 0.851, physical face) the Cauchy–Schwarz capacity is about 0.0631 per unit d, against 0.0597
for the face [numerical]. But the second capacity term, numeratorCap·d = 0.0483, binds only 0.4 % behind
the face term (0.0481). So without lifting numeratorCap too, the gain is only about −4e-6 [rough].

**Open.** What fixes numeratorCap = 3/50, and can a redesigned numerator lift both?

## 5. Properties of the true region T (the set where the face-type bound is actually true)

1. T contains R_CS [proved, as above].
2. T is closed under the Cauchy–Schwarz rule [same argument, applied to true bounds].
3. For fixed m, the set {s : (m, m, s) ∈ T} is midpoint-convex: take the endpoints (m, m, u) and
   (m, m, v) with s_A = u/2, s_B = v/2. So it is an interval if it is closed [proved].
4. Outer limit: a row on which all factors align makes the energy at least of size U^{m₁+m₂+s}, so
   T ⊆ {m₁ + m₂ + s ≤ 1} up to ε, *if* the family keeps such near-principal rows [heuristic; check
   what `initialKeep` excludes].
5. Conjecture: an optimal large sieve for the structured sextic family, Lindelöf-on-average type,
   would give T = {m₁ + m₂ + s ≤ 1}. That is the ideal face G(1, 1, ·).

## 6. Next

- D8b: the continuum ODE of the density chain, i.e. the method's limit.
- D8a′: a numerator design with an unbalanced binding configuration, and the origin of numeratorCap.
