# D8b: a certificate-free density chain (blueprint)

Goal: replace the 129 per-step certificate files (6.2 MB) with
- generic lemmas, proved once, that derive every gate of one density step from closed-form scalar
  inequalities in the step's rationals; and
- a chain given by a formula: faces on the continuum curve lowered by η (`CONTINUUM.md` §7), step h, and
  one selection (A, D).

Tags: **[Lean]**, **[exact]**, **[derived]**, **[numerical]** as in `CONTINUUM.md`.
Scripts: `uniform/` (relative paths; run from that directory).

## 0. Result so far

- **The design works at every step [numerical, `uniform/pipeline3.py`].**
  - Chain: η = 1e-4, h = 5e-4, A = 0.42, D = 100 (the same for every step).
  - Faces at Λ_k = 2.5715 − k·h on the η-curve, k = 0…1289, ending at (Λ, B) = (1.9270, 0.96243668).
  - All 1289 steps pass every scalar condition below.
  - Worst margins:

    | condition | margin |
    |---|---|
    | V12 | +2.55e-5 |
    | V10 | +2.62e-5 |
    | q_floor | +7.5e-5 |
    | q_upper | +9.6e-4 |
    | ret_cap | +1.1e-3 |
    | principal | +2.4e-3 |
    | C02 | +1.3e-2 |
    | C00 | +1.7e-2 |
    | C01 | +2.0e-2 |
    | C0 | +2.2e-2 |
    | second_diag | +4.2e-2 |
    | H_lower | +7.8e-2 |
    | N | +7.7e-2 |
    | second_ref | +8.2e-2 |
    | ref_upper | +0.12 |
    | P10 | +0.61 |
    | P11 | +1.03 |
    | P12 | +1.93 |

- **The end face implies today's final face [exact arithmetic].**
  - The end face (1.9270, 0.96243668) dominates today's final face (1.9265, 0.96232839) on the whole cap
    range: 0.96243668 − 0.96232839 = 1.08e-4 > 0.0005·s for every s ≤ 1/10.
  - So every configuration admissible for the old face is admissible for the new one.
  - The last step from 1.927 to 1.9265 fails on the density floor (q is 0.50033 there). It is not needed.
- **On real chain steps, the reduced form equals the full gate [numerical, `uniform/pair.py`].** For steps
  1, 41, 81, 121 and 129, the minimum of the full gate over (v, ν, p, six facets) equals
  min_v min(Γ₁₀, Γ₁₂)(v, q(v)) to every printed digit.

## 1. Notation

- Parent (B₀, Λ₀). Child (B, Λ) = (B₀ − s₀h, Λ₀ − h). Caps: c₀ = c = h₀ = 1/10. K = 8, q_f = 1/2.
- Excess v ∈ [0, v_max], v_max = c − s₀.
- u(v) = Av/(1 + Dv), w_v = s₀ + v, S = w_v − u, Q = 1 − 6u.
- q(v) = 0.999·Λ₀A/(h(1 + Dv) + (6B₀ − Λ₀)A).
- Density ν ∈ [q(v), 3/4], with w = 5 − 6ν, x = w/(2(5 + w)), y = x/(1 + x) = w/(10 + 3w).
- σ(ν) = (B₀ − 1 + y)/(Λ₀ − 1 + y).
- R(ν) = (Λ₀ − 1 + xB₀)/(Λ₀ − 1 + xΛ₀).

Lean facet form (`Gain/Gain.lean`, `branchRoot_eq`, `facetVal`) [Lean]:

    facetVal_k = (1 − 2p)νS + ν[(5Q + w(offS_k S + offQ_k Q))/((15 − 6ν)/2 + w·slopeExcess_k) − 10Q/(15 − 6ν)].

It is linear in (S, Q) (`facetVal_linear`). Write φ_k = facetVal_k/ν.

## 2. The HIGH gate reduces to a binding pair

**(a) p-reductions [exact factorizations, `uniform/facets_exact.py`, `facets_cond.py`].**

- Facet (1,0):
  - φ₁₀(p) − φ₁₀(½) = 2(1 − 2p)·N₁₀(p)/((3w + 10)(w(1 + p) + 10(1 − p))).
  - N₁₀ = S[(3w² − 5w − 50)p + w² + 15w + 50] − Qw² is affine in p.
  - Condition **P10**: N₁₀(½) = 2.5S(w² + 5w + 10) − Qw² ≥ 0. N₁₀(0) ≥ N₁₀(½) holds automatically for w < 4.97.
- Facet (1,1):
  - φ₁₁(p) − φ₁₁(½) = (1 − 2p)·N₁₁(p)/((3w + 10)(w(1 + p) + 10(1 − p))), with N₁₁ affine in p.
  - Condition **P11**:
    - N₁₁(0) = S(3w² + 40w + 100) − Qw(h₀w + 10h₀ + 2w) ≥ 0;
    - N₁₁(½) = S(4.5w² + 30w + 50) − Qw(2w + 5h₀ − h₀w/2) ≥ 0.
- Facet (1,2):
  - φ₁₂(p) − φ₁₂(½) = (1 − 2p)·N₁₂(p)/(D₁D₂).
  - D₁ = Λ₀(3w + 10) − 2(w + 5) > 0.
  - D₂ < 0 on [0, ½]: D₂ is increasing in p, and D₂(½) = −(Λ₀ − 1)(1.5w + 5) − w/2.
  - N₁₂ is a concave quadratic in p, with leading coefficient 4S(w − 5)D₁.
  - Condition **P12**: N₁₂(½) + max(0, −N₁₂′(½))/2 ≤ 0 (tangent bound at p = ½).
- Eight-copy facets:
  - φ₀₀ − S = 4Sp(8w − 5)/(w + 10) and φ₀₁ − S = 2p(Qh₀w + 15Sw − 10S)/(w + 10), both affine in p.
  - φ₀₂ − S = 2p·N₀₂(p)/((w + 10)(20p − Λ₀(w + 10))), with N₀₂ affine in p and the denominator negative.

**(b) Comparisons [exact].**
- At p = ½, φ₁₀ = (Q + xS)/(1 + x) − base·Q, so:
  - φ₁₁(½) ≥ φ₁₀(½) ⟺ S ≤ h₀Q. This is automatic, since c = h₀ and u ≥ 0.
  - φ₁₀(½) ≥ φ₁₂(½) ⟺ S ≥ Q·σ(ν). This is **not** imposed: both facets are kept as the binding pair.
- Eight-copy facets must stay above φ* = φ₁₂(½) = Q(R − base):
  - **C0**: S ≥ φ*.
  - **C00**: 17Sw/(w + 10) ≥ φ*.
  - **C01**: φ₀₁(½) ≥ φ*.
  - **C02**: S − max(N₀₂(0), N₀₂(½), 0)/((w + 10)(Λ₀(w + 10) − 10)) ≥ φ*.

**(c) The binding pair [exact algebra].**

    Γ₁₂(v, ν) := highJ + ν φ₁₂(½) = ν(Λ₀ − 1)(s₀ − σ(ν)) + ν(Λ₀ − 1 − h)v − u·C₁₂(ν),   C₁₂ = 6νR − ν − 1,
    Γ₁₀(v, ν) := highJ + ν φ₁₀(½) = ν(Λ₀ − 1 + y)(s₀ − σ(ν)) + ν(Λ₀ − 1 − h + y)v − u·C₁₀(ν),   C₁₀ = 5ν(1 − y) − 1.

The child's (B, Λ) enters highJ and the parent's (B₀, Λ₀) enters the gain. At v = 0 both reduce to the
parent's continuum gate.

**(d) N: increasing in ν.**
- |dσ/dν| = 60(Λ₀ − B₀)/((Λ₀ − 1 + y)²(10 + 3w)²) increases with ν. So its minimum on [q_min, ¾] is at
  ν = q_min, where q_min = q(v_max).
- C₁₂ and C₁₀ increase in ν.
- Condition **N**: q_min(Λ₀ − 1)|σ′|_min ≥ (Λ₀ − 1)(σ(q_min) − s₀)⁺ + u_max·max C′.

**(e) V: the dip in v [derived].** Here q₀ = q(0) and E₀ = h + (6B₀ − Λ₀)A.
1. Take the Lipschitz constant L_σ = |dσ/dq| at q₀ (where it is largest on [q_min, q₀]).
2. Then s₀ − σ(q(v)) ≥ (s₀ − σ(q₀)) − L_σ·q₀hDv/E₀.
3. So X(v) ≥ m₀ + βv, with m₀ = (Λ₀ − 1)(s₀ − σ(q₀)) and β = (Λ₀ − 1 − h) − (Λ₀ − 1)L_σq₀hD/E₀ ≥ 0.
4. Split the range at v₁ = k₁/D.
5. On [0, v₁] the bound is q(v)X(v) − uC ≥ q₁(m₀ + βv) − (q₀ − q₁)(−m₀)⁺ − C(q₀)·Av/(1 + Dv). Write
   z = 1 + Dv; then bz + γ/z ≥ M for any M ≥ 0 with M² ≤ 4bγ, so the minimum over v is at least
   q₁m₀ + (M − b − γ)/D. This form needs no square roots.
6. On [v₁, v_max], using q ≥ q_min and u ≤ min(A/D, u_max), the bound is q_min(m₀ + βv₁) − C(q₀)·min(A/D, u_max).

Condition **V12** says both pieces are ≥ r > 0. **V10** is the same with Γ₁₀'s coefficients.

**Worst corners.** Every condition is monotone in (S, Q): linear, with known signs. The corner is
S = s₀ (since u ≤ v when A ≤ 1) and Q = 1, or the four corners for P12/C02.
- P10 and P11 are concave quadratics in w, so the w-range [½, w_max] reduces to its endpoints.
- P12 and C0x have margins 1e-2 to 2, so crude interval bounds in w suffice.

## 3. One-variable gates

These are delegated: `Submissions/arvi_uniform_chain/Gates1D.lean`, agent in progress.
- q_lower, q_floor: q(v_max) > q_f.
- q_upper: q(0) < 3/4.
- H_lower: 6u(v_max) < 1/10.
- retained_cap: value at v_max.
- retained_width: s₀ > 0.
- ref_upper: 1/3 − 2c − 3u(v_max) > 0.
- principal, second_ref, second_diag: α + βv − γu with u ≤ min(Av, A/D); four breakpoint values.
- The identities low_identity, low_div_eq and sel_hasDerivAt.

## 4. Lean plan

1. `Gates1D.lean` (agent): `hybridGatesM_of_scalar … (hhigh) : HybridGatesM …`.
2. `HighReduce.lean` (lead):
   - the explicit facet forms from `branchRoot_eq`, and the (1 − 2p) factorizations;
   - P10/P11/P12/C0x lemmas;
   - the binding-pair identities;
   - N and V;
   - `high_marked_of_scalar`.
3. `ChainUniform.lean`:
   - the curve sampled as rationals, or a rational polynomial β below the η-curve;
   - Λ_k, A, D;
   - the scalar conditions as a computable ℚ-valued check with a soundness lemma;
   - one `decide +kernel` over k ≤ 1289, and induction on k with `density_step_marked`;
   - the final face, plus a face-inclusion lemma to today's final face, or re-tuned return constants
     (`return-tuning/`).

Fully uniform variant (no list): prove each scalar condition for all Λ on the curve by one-variable
arguments in Λ. With the reductions above, every condition is an explicit inequality in (B₀, Λ₀, s₀, h, A, D).

## 5. Files (`uniform/`)

| file | content |
|---|---|
| `facets_exact.py`, `facets_cond.py`, `facets_sym.py` | exact facet forms, the (1 − 2p) factorizations, N₁₂ coefficients, the eight-copy differences |
| `ratios.py` | critical ratios S/Q per facet along the chain |
| `pair.py` | binding pair vs full gate on real steps |
| `conditions.py` | scalar conditions (spec of the Lean lemmas); grids in w and numerical derivatives are still to be replaced by exact bounds |
| `pipeline3.py` | all steps of the η-curve chain with one (A, D) |
| `endface.py` | the last steps near the floor |
