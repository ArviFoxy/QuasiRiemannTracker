# Sub-square-root selection for the sextic row family (thread SR)

Status: **closed** [numerical, model]. A Guth–Maynard-strength bound for the sextic rows would give count 0.6199 at the
binding point, worse than the return's 0.6072 (`zd_calibration.py`; journal 2026-10-30, "zero-density calculator").
The plan below needs large values beyond Guth–Maynard. Nothing here is proved.

## 1. Why this is the next lever

After the selected-leaf PR (#97, θ = 0.87341198) the return binds at the newTop edge, at δ ≈ 0.452, p = 1/2
(`journal/JOURNAL.md`, 2026-10-30). The binding rows are zeros at real part ≈ 0.726 whose marked prime slots are at full
amplitude, so the slots have selection slope δ_sel = ν = 0.452. That is just below the square-root threshold of PR 93's
selected norm, whose iteration (amplify and reflect, `SelectedNormIteration`) contracts only for δ_sel > 1/2.

The return's count there is ≈ 0.602. PR 93's three-word minimax (`subroot/word_count.py`) gives:

| selected-norm exponent g(w) on rows of slope 0.452 | count |
|---|---|
| ideal fixed point max(w, 1 − δ + δw) | 0.548 (density hypothesis) |
| needed for θ ≤ 0.87336198 (with the banked −2.83e-5: about half of this) | ≤ 0.6063 |
| one amplification against the sextic sieve Θ₆ | 0.715 |
| plain Θ₆ = A + B + A^(5/6)B^(1/3) + A^(1/3)B^(5/6) | 0.747 |

In ideal-slope terms the requirement is an effective slope of ≈ 0.23, i.e. a selected norm
Σ_{u selected} |Σ_{N n ≤ Y^w} b_n χ_u(n)|² ≲ Y^ε (Y^w + Y^(1−0.23) Y^(0.23 w)) ‖b‖² on rows selected at slope 0.452.

## 2. The analogue in the literature

- Guth–Maynard (arXiv 2405.20552): large values of D(t) = Σ_{n~N} a_n n^{it} at V ≈ N^(3/4), i.e. at the
  square-root selection threshold. The method bounds the top singular value of M_{t,n} = n^{it} on the large-value
  set W through tr((MM*)³) minus its diagonal part. Poisson in the three n-sums gives the transform
  R(v) = Σ_{t ∈ W} v^{it} on z₁z₂z₃ = 1. A new bound for such sums then uses the additive energy of W.
- Chen–Gupta–Li (arXiv 2507.08296): the same for D(t, χ) = Σ a_n χ(n) n^{it} over all characters χ mod a fixed q.
  Poisson is taken mod q, with transform R(v, b) = Σ_{(t,χ) ∈ W} v^{it} χ(b) and a "GCD twist". Large values:
  |W| ≤ (N²V⁻² + q q₁^(−1/2)T^(1/2)N³V⁻⁴ + q q₁^(1/3)TN²V⁻⁴ + qTN^(12/5)V⁻⁴); zero density exponent 7/3.

## 3. What is different for our rows

- Rows are sextic symbols χ_u = (·/u)₆ of varying modulus u ∈ Z[ω], N(u) ≤ Y. This is a thin family, and its mean
  value is not Y + N but Θ₆, cross terms included (de Faveri; Sil's Lean `SieveOptimal.optimal_bound`).
- In the trace method the off-diagonal kernel χ_{u₁}χ̄_{u₂}(n) has modulus u₁u₂, which varies with the pair. By
  sextic reciprocity the n-sums become sums over moduli n of (u₁ū₂…/n)₆. That is Heath-Brown's large-sieve setting,
  where the dual side carries Gauss sums and Kubota series.
- #96's graded inverse theorem (GS1, `pr96/`) decomposes the sextic large-sieve operator S*S into a diagonal part, a
  residual and positive block operators that carry the excess over A + B. In the trace method, these block terms
  play the role that additive energy plays in Guth–Maynard.

## 4. Plan

1. **Exact need.** Price partial bounds through PR 93's iteration and the return. If the sub-barrier norm is used only
   in the count's marked fibers, check which (δ, p) region and which word lengths actually need it.
2. **Heuristics and numerics.** For small Y, compute the selected sets {u : |T_u|² ≥ X^δ} for random and prime-supported
   slot polynomials over Z[ω], and the restricted sieve constants. Do they behave like the ideal Y^(1−δ)L^δ at
   δ ≈ 0.45? This is a plausibility check, not evidence for exponents.
3. **Theory.** Run the third-moment trace bound for M_{u,n} = χ_u(n) on the selected set:
   - Poisson in n via the sextic Gauss sums (baseline `SexticRadialPoisson`);
   - the dual transform R(b) = Σ_{u∈W} χ_u(b) on the dual set;
   - its energy, or GS1's block terms, in place of additive energy.
   Goal: a bound below Θ₆ at slope 0.452 with effective slope ≥ 0.23.
4. **Lean.** Only after 3 closes on paper. The inputs that exist: sextic Poisson and Gauss sums, the sextic sieve, PR
   93's iteration.

Risk: high. This is open research (a Guth–Maynard-type theorem for a thin fixed-order family). The payoff is
correspondingly large: up to Δcount −0.055 at the binding point.
