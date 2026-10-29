# D8b: the continuum density chain, solved exactly

This note gives an analytic characterization of the region that the marked density chain proves in the limit
of infinitely many steps. It also sets out what a single uniform proof (no per-step face certificates) has to
establish.

Tags: **[Lean]** read in Lean source, **[exact]** exact rational/symbolic computation, **[derived]** our
derivation (not formal), **[numerical]** floating point. Scripts and logs: `continuum/`.

## 0. Summary

- **Closed-form slope [derived, exact check].** In the continuum limit the marked HIGH gate binds at p = 1/2,
  ν = q, on facets (1,0) and (1,2) of the repeated-mark gain, which tie exactly. The least admissible slope is

      σ(B, Λ) = (B − κ)/(Λ − κ),   κ(q) = 4(5 − 3q)/(25 − 18q),   q = 0.999·Λ/(6B − Λ)  (capped at 3/4).

  It equals `ode2.s0_inst` (numerical inf over ν, p and the six facets) to 2e-14 on the chain.
- **Geometry [derived].** In the dual plane (Λ, B), σ is the slope of the segment from the face to the
  diagonal point T(q) = (κ, κ). The diagonal point (t, t) is the face m₁ + m₂ ≤ t(1 − s), i.e. the ideal face
  m₁ + m₂ + s ≤ 1 scaled by t. **Each density step moves the face straight toward the scaled ideal face
  κ(q)·(1, 1).** The cut q depends only on the ray r = B/Λ (q = 0.999/(6r − 1)). As the face's ray turns,
  the target slides down the diagonal from 22/23 (q = 3/4) to 7/8 (q = 1/2).
- **Envelope [derived; discrete chain to 2.6e-6].** At every contact point, E(s) = κ(q(s))·(1 − s). The chain
  proves the ideal region scaled by κ ∈ [7/8, 22/23].
- **Exact solution [derived; ODE to 1e-12].** With r = B/Λ the ODE is a Bernoulli equation in Λ. Hence

      1/(Λ − B) − 𝒢(B/Λ) = constant along the chain,
      𝒢(r) = A₁/(4(1 − r)) + (A₃/120)·log((30r − a)/(1 − r)),

  with d = 0.999, a = 5 + 3d, b = 25 + 18d, A₁ = (150 − b)/(30 − a), A₃ = (5a − b)/(1 − a/30)².
  Numerically A₁/4 = 1.2159478 and A₃/120 = −0.0464287. With d = 1 this is
  𝒢 = 107/(88(1 − r)) − (45/968)·log((30r − 8)/(1 − r)).
- **Floor face in closed form.** From the boot face (0.99999, 2.5715), the curve meets the floor ray
  q = 1/2 (r_f = (1/2 + d)/3) at Λ_f = 1/((1 − r_f)(1/(Λ₀ − B₀) + 𝒢(r_f) − 𝒢(r₀))) = 1.92607179,
  B_f = 0.96239387. The 129-step chain ends at (1.9265, 0.96232839), 1.0e-4 below the curve in B.
- **Uniform proof.** On the region the chain uses, all inner quantifiers of the Lean gate `high_marked`
  (over p, the six facets and ν) reduce exactly to one explicit function of v [numerical, about 2·10⁵
  samples]. The 12 one-variable gates reduce to endpoint checks [derived]. §5 gives the plan.

## 1. The continuum gate

Lean (`Source/HybridGatesMarked.lean`, field `high_marked`) [Lean]:

    r ≤ highJ B L (width v) (sel v) ν + gainC ν B₀ L₀ c₀ (width v − sel v) (packed v)
    for v ∈ [0, c − s₀], ν ∈ [q(v), 3/4]

where `highJ = 1 − ρ − νB + ν(L − 1)w − (6(1 − ρ) − ν − 1)u` with 1 − ρ = ν·base(ν),
base(ν) = 10/(15 − 6ν). The gain `gainC = gainK = inf_{p∈[0,1/2]} min_k gainP_k`, and
gainP_k = (1 − 2p)νS + ν(root_k − base·Q) over the 2 × 3 facets (`newpowers/ta/gainc.py`, a float
replica of `Gain/Gain.lean`).

**Two facts.**
1. **At v = 0 the child's J equals the parent's [exact].** B − (L − 1)s₀ = B₀ − (L₀ − 1)s₀ when
   (B, L) = (B₀ − s₀h, L₀ − h).
2. **base cancels [exact].** The gate per unit ν is gate_k/ν = ΛS − B − 2pS + root_k at Q = 1, u = 0.

**Binding [derived; `continuum/closed_form.py`].**
- Put w = 5 − 6ν, x = w/(2(5 + w)), y = x/(1 + x) = w/(10 + 3w).
- At p = 1/2: root₁₀ = (1 + xs)/(1 + x) and root₁₂ = (Λ − 1 + xB)/(Λ − 1 + xΛ).
- Both give the same threshold s = (B − 1 + y)/(Λ − 1 + y), with equality checked in exact rationals.
- Facet (1,1) is weaker exactly when s ≤ h₀ = c₀ = 0.1 [exact].
- The eight-copy facets (0,·) are weaker when s ≥ ((5 + w/2)·root₁₂ − 5)/(8.5w), which is ≤ 0.0185
  on the chain [derived].
- σ(ν) decreases in ν (∂σ/∂y = (Λ − B)/(Λ − 1 + y)² > 0, and y decreases in ν), so ν = q binds.

**Off the chain the closed form fails [numerical]:**
- s > 0.1: facet (1,1) binds;
- s < 0.015: eight-copy facets or an interior p bind.

The chain uses s ∈ [0.0277, 0.0834].

## 2. Exact solution of dB/dΛ = (B − κ)/(Λ − κ)

1. Write B = rΛ. Then Λ·dr/dΛ = −(1 − r)κ/(Λ − κ).
2. So dΛ/dr = −Λ(Λ − κ)/((1 − r)κ), a Bernoulli equation.
3. Z = 1/Λ satisfies dZ/dr + Z/(1 − r) = 1/((1 − r)κ). The integrating factor is 1/(1 − r).
4. Hence d/dr[1/(Λ − B)] = 1/((1 − r)²κ(r)).

κ(r) = 4(30r − a)/(150r − b) is rational in r, so the integral is elementary (partial fractions, §0).

Check (`continuum/exact_solution.py`, `logs/exact_solution.log`): the quadrature, the closed antiderivative
and a DOP853 solution agree to 1e-12 at Λ = 2.5, 2.3, 2.1, 1.95 and 1.926072.

**What the formula is good for.** The response of the chain's end to any change is a quadrature. This covers:
- a change in the target κ(q) (the gain structure);
- a change in the ray map q(r) = d/(6r − 1) (the LOW identity);
- a change in the boot face or the floor.

Pricing a lever no longer needs a chain run.

## 3. The discrete chain against the continuum [numerical, `continuum/discrete_binding.py`]

- All 129 steps bind at p = 1/2, ν = q(v), facet (1,2).
- The binding point is at a small excess v* ≈ 3–7·10⁻⁴, not at v = 0. Its value is about the scale on which
  u = Av/(1 + Dv) saturates (v ≈ 1/D).
- The step slope exceeds σ(parent, q(0)) by 0.5–1.9e-4; the last, floor-limited step by 3.9e-4.
- Two effects cause this:
  1. the selection u costs u·C(ν) before it saturates;
  2. q(v) falls with v.
- With the binding facet written out (ν fixed):

      gate₁₂(v, ν) = ν(Λ₀ − 1)(s₀ − σ(ν)) + ν(Λ₀ − 1 − h)v − u(v)·C(ν),
      C(ν) = 6νR(ν) − ν − 1,   R(ν) = (Λ₀ − 1 + xB₀)/(Λ₀ − 1 + xΛ₀)   [exact],

  and the dip at fixed ν is (√(A·C) − √(ν(Λ₀ − 1 − h)))²/D [derived].
- Both effects vanish as h → 0 with D ∝ 1/h, while q stays above the floor. The accumulated effect is the
  1.0e-4 gap in B at the end.
- θ cost of that gap [numerical, `twisted/scan_split.py` baseline]: the continuum chain gives θ ≈ 0.873870999
  against 0.87387234, so dθ/dB_f ≈ −0.013.

## 4. Reductions of the HIGH gate on the chain region [numerical]

Sampled region (`continuum/vec.py`):
- (B₀, Λ₀) within 1e-3 of the chain;
- A ∈ [0.4, 0.7], D ∈ [20, 1000], h = 0.005;
- s₀ = σ(q(0)) + [0, 5e-4];
- v ∈ [0, c − s₀];
- ν ∈ [q(v), 3/4].

| claim | evidence |
|---|---|
| **P1**: facets (0,0), (0,1) are affine in p; (0,2) is concave in p | max φ″ = +2e-9 (rounding) and −4.9e-4 (`logs/p_shape.log`) |
| **P2**: facets (1,0), (1,1), (1,2) are strictly decreasing in p | max dφ/dp = −0.027 (`logs/p_shape.log`) |
| **P**: min over p ∈ [0,1/2] and the facets = min(S, min_k φ_k(1/2)) | 158 792 samples, violation 0 (`logs/p_endpoint.log`) |
| **N**: the full gate (highJ + ν·min) increases in ν on [q(v), 3/4] | smallest step between grid points +8.6e-6, i.e. strictly increasing (`logs/nu_reduction.log`) |
| **F**: facet (1,0) ≥ facet (1,2) at p = 1/2 ⟺ S ≥ Q·σ(ν) | exact algebra |

Here φ_k = gainP_k/ν, with Q = 1 − 6u and S = w − u.

Hence, on this region, `high_marked` is equivalent to one function of v being positive:

    g(v) = q(v)(Λ₀ − 1)(s₀ − σ(q(v))) + q(v)(Λ₀ − 1 − h)v − u(v)·C(q(v))  ≥  r  on [0, c − s₀],

plus side conditions (S ≥ Q·σ, the P1/P2/N hypotheses) that hold with margin.

**Concavity in p fails off the chain** (φ″ up to +0.23 for the (1,·) facets), and P2 fails for S ≲ 0.004.
Each lemma needs explicit hypotheses.

## 5. Toward a single uniform proof

What exists today [Lean]: 129 files `ChainF50/Step_NNN.lean`, about 47 KB each (6.2 MB):
- 12 one-variable Bernstein boxes per step;
- six reflective `checkZ` trees for the marked gate;
- `density_step_marked` composes them.

Proposed stages (each one shrinks the certificates):

1. **One-variable gates → scalar conditions [derived].** Every gate other than `high_marked` is linear in
   (w, u, q) along v.
   - q(v) decreases and u(v) is increasing and concave, so each gate is either monotone in v or convex in v.
   - For the convex ones, u(v) ≤ min(Av, A/D) gives a piecewise-linear lower bound.
   - Generic lemmas, proved once, turn each gate into one or two rational inequalities on
     (B₀, Λ₀, c₀, B, Λ, c, A, D), checked by `norm_num`.
   - Expected size: under 2 KB per step.
2. **HIGH gate reductions P and N as lemmas.**
   - Hypotheses: explicit polynomial inequalities with margin.
   - Proof: by hand where possible, otherwise one parametric certificate in 4 variables (p, ν, B₀, Λ₀),
     proved once rather than per step.
   - The gate then becomes the one-variable g(v) above.
3. **Uniform chain.**
   - Faces given by a formula: the exact solution with a margin, or a polynomial below it.
   - Steps Λ_k = Λ₀ − kh.
   - One step lemma for every Λ in the range, and induction on k.
   - With h → 0 (D ∝ 1/h) the chain approaches the exact curve, recovering the 1.0e-4 gap.
   - Real induction would remove h altogether.

A pure engineering alternative, with no new mathematics: make the 12 one-variable gates reflective, as
`return-tuning/` did for the return guards. Each step becomes its rationals plus `decide +kernel`.

## 6. Files

| file | content |
|---|---|
| `continuum/closed_form.py` | exact facet tie; closed form vs `ode2`; trajectory vs chain; envelope relation (`logs/closed_form.log`) |
| `continuum/exact_solution.py` | quadrature and closed antiderivative vs ODE; floor face (`logs/exact_solution.log`) |
| `continuum/discrete_binding.py` | binding (v, ν, p, facet) of the 129 discrete steps (`logs/discrete_binding.log`) |
| `continuum/vec.py` | vectorised facets; sampler of the chain region |
| `continuum/p_shape.py`, `p_endpoint.py`, `nu_reduction.py` | reductions P1, P2, P, N (`logs/`) |
