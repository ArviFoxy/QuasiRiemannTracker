# Why the source chain is the curve it is (2026-10-25)

The user asked, after the face family was in Lean (`../faceless-chain/`): why this curve, is it
fully optimal, and what structure does it come from. Short answers:

- **Why this curve.** The faces are the tangent lines of one envelope `E(s)`, and the source step
  says how fast the tangent may turn. That is a first-order ODE whose right side is the binding
  threshold `6q*`, the maximum over the HIGH count's amplitude classes `p`.
- **Why square roots.** The maximum over classes is an AM–GM balance between a slot term (`4s`) and a
  plain term (`E`). It is an exact sum of squares, so the closed form is the true maximum over all
  classes, not only a critical point.
- **Why Lambert W.** Each class flow is a quadratic vector field in which the zero-length line
  `E = 0` is invariant with multiplicity two. A double invariant line carries an exponential
  factor `exp((5s − p)/E)`, and that factor is what makes the solution `x·eˣ = c`.
- **Is it optimal.** Within the face-map method, yes, up to 0.9e-6. Every admissible envelope stays
  below this flow, tangent faces are the best faces for a given envelope, and the Lean family is
  0.9e-6 above the continuum ceiling. Only the four atoms move it.

## 1. Faces, Legendre duality and the gate surface

A face `(B, Λ)` certifies the half-plane `m₁ + m₂ + Λz ≤ B`. With pivots dense along the chain the
faces are the tangent lines of the envelope:

  `B = E − sE′`, `Λ = −E′`, i.e. `B(Λ) = min_s (E(s) + Λs)` and `dB/dΛ = s`

(`../chain-ode/README.md`). The source step at pivot `s` has two parts:
- the LOW limit `Λ ≥ 6qB` (the LOW denominator `1 − 6qB/Λ` stays positive);
- the HIGH threshold `q ≥ q*(s, E)`, the smallest density at which the HIGH count closes.

Together they give `Λ(1 − 6q*s) ≥ 6q*E`. In the 1-jet space with coordinates `(s, E, Λ)` and contact
form `dE + Λ ds`, the equality `Λ(1 − 6q*s) = 6q*E` is a surface, and the chain is the Legendrian
curve on it through the natural seed. This is the classical picture of an implicit first-order ODE
(a surface in the space of 1-jets, solved by the integral curves of the contact planes on it).

## 2. The binding class is an AM–GM optimum

Class `p` gives `6q_p = 5A_p/D_p` (`../lean-lab/ChainFamilyIntegrable.lean`) with

  `A_p = (3 − p)E + 4ps − 2`, `D_p = (1 + p)E + 4p²s − 2p`.

**Mixture identity.** `D_p = pA_p + (1 − p)²E`, so

  `5/(6q_p) = p + (1 − p)²E/A_p`.

**AM–GM.** Put `w = 1 − p`, `c = E − 4s`, `d = 2(1 − E − 2s)` and `v = A_p = cw − d`. Then

  `5/(6q_p) = 1 − d/c + 2Ed/c² + (4s·v + E·d²/v)/c²`.

The last bracket is at least `2√(4sE)·d = 4d√(Es)`, with equality at `v = d√(E/(4s))`. The square
root is the geometric mean of the slot term `4s` and the plain term `E`.

**Exact form** (`amgm.py`; Lean `../lean-lab/ChainAMGM.lean`). With `E = a²`, `s = b²`, for every
real `p`:

  `(a + 2b)²·[(a − 2b)²D_p − (2 − a² − 4ab)A_p] = 4(bA_p − a(1 − a² − 2b²))²`.

Hence, whenever `D_p > 0` and `2 − a² − 4ab > 0`,

  `6q_p ≤ 5(√E − 2√s)²/(2 − E − 4√(Es))`,

with equality iff `bA_p = a(1 − a² − 2b²)`, i.e. at

  `p* = (E + √(Es) − 1)/(√(Es) − 2s)`

(the same root as `../chain-ode/pstar.py`, in a simpler form). `ChainSwitching.lean` had only shown
that `p*` is a critical point; `ChainAMGM.threshold_le` shows the closed form bounds every class.

**Discriminant view** (`discriminant.py`). As a quadratic in `p`, the class relation
`Q·D_p − 5A_p = 0` (`Q = 6q`) has discriminant

  `X² − 16Es·Y²`, `X = Q(2 − E) − 5(E + 4s)`, `Y = Q − 5`,

a norm form from `ℚ(√(Es))`. The threshold surface is the envelope (discriminant locus) of the class
family, and it splits over `ℚ(√E, √s)` into `Q = 5(a − 2b)²/(2 − a² − 4ab)` and its conjugate
`Q = 5(a + 2b)²/(2 − a² + 4ab)`.

## 3. Where Lambert W comes from

With the cutoff root `ξ = E + 2ps` (the gate reduction of `ChainFamilyIntegrable.lean`):

  `A_p = (1 − p)E − 2(1 − ξ)`, `D_p = (1 − p)E − 2p(1 − ξ)`, so `6q_p = 5(e − 2m)/(e − 2pm)`,

with `e = (1 − p)E` and `m = 1 − ξ`. After a change of time the class flow is the quadratic field
`X = (ṡ, Ė) = (D_p − 5A_p s, −5A_p E)` (`lambert_origin.py`; Lean
`../lean-lab/ChainLambertOrigin.lean`):

- `E = 0` is invariant with cofactor `−5A_p`, and `L_p = 0` is invariant with cofactor
  `−5A_p − 2(5 − 2p²)`, where `L_p = (3 − 2p)(5 + p)E + 4p(5 − 2p²)s − 2(5 − 2p²)`.
- Because `D_p − pA_p = (1 − p)²E`, the function `(5s − p)/E` has **constant** Lie derivative:
  `X((5s − p)/E) = 5(1 − p)²`. So `exp((5s − p)/E)` is an exponential factor.
- The extactic polynomial for lines is `10(1 − p)²E²L_p`: the line `E = 0` has multiplicity two.
  By the theory of multiple invariant curves (Christopher–Llibre–Pereira), a double invariant line
  is exactly what produces an exponential factor.
- Counting the exponential factor, there are `m(m + 1)/2 = 3` invariant objects with independent
  cofactors for degree `m = 2`, which is the Darboux count for an integrating factor; it is
  `1/(E²L_p)`.

In the flow's own time, `(5s − p)/E` grows linearly and `L_p/E` decays exponentially, at rates that
cancel in `I_p = log(L_p/E) + κ(5s − p)/E`, `κ = 2(5 − 2p²)/(5(1 − p)²)`. Solving `I_p = c` for `E`
is `x·eˣ = const`, the Lambert W function. So the transcendence of the chain (`../chain-ode`:
"its ceiling is transcendental, not algebraic") traces back to one identity, `D_p − pA_p = (1 − p)²E`:
on the zero-length line the HIGH threshold is the constant `6q = 5/p`.

## 4. The switching flow itself is not integrable at low degree

With `E = a²`, `s = b²` the switching flow is the degree-4 field
`ȧ = −5ab(a − 2b)²`, `ḃ = 2 − a² − 4ab − 5b²(a − 2b)²` (`switching_darboux.py`, log
`switching_darboux.log`):

- The degree-1 extactic polynomial factors as `a · (a − 2b) · (degree 7)`. Only `a = 0` is invariant,
  now with multiplicity one. `a = 2b` and the degree-7 factor are inflection loci of trajectories.
- The degree-2 extactic polynomial has, besides powers of `a` and the two inflection factors, one
  irreducible factor of degree 29, so there are no invariant conics.

So the closed-form Lambert structure belongs to each fixed class. When the binding class moves
continuously, the double line and its exponential factor are lost, and there is no Darboux first
integral built from curves of degree ≤ 2. This is why the Lean family follows the ODE with cubic
pieces instead of a closed-form curve.

## 5. Is it optimal?

Within the face-map method, yes, up to 0.9e-6:

1. **Per step.** The threshold is the exact maximum over classes (section 2). The full 16-gate
   continuum solver, with fees, caps and Lemma F self cells, agrees with the closed form to 6e-7
   (`../chain-ode/README.md`), so no other gate or class binds.
2. **Along the chain.** The descent rate `F(s, E) = 6q*E/(1 − 6q*s)` increases with `E`, since `6q*`
   increases with `√E` when `√E > 2√s`. So by the comparison principle
   (`../lean-lab/MaximalEnvelope.lean`) every admissible envelope stays below the equality solution
   from the natural seed.
3. **Faces.** For a given envelope, the tangent lines maximize `B(Λ)` pointwise (Legendre).
4. **Endpoints.** θ* is flat in the count-face position near the end of the chain (moving it by 2000
   grid steps changes θ* by 1e-7), and the physical face sits at `Λ ≈ 3`.
5. **Formal versus ceiling.** Lean family 0.8747250 versus continuum ceiling 0.8747241. The 0.9e-6
   gap is the slope reserve `φ = 1e-4`, the LOW denominator `2⁻¹⁵`, the mesh `2⁻¹⁶` and the fees.

What the curve is made of: the unmarked count `ρ(ν) = 1 − 10ν/(15 − 6ν)` (the `5`, `3` and `2` in
`A_p`, `D_p`), the slot-supply facet `2pS` (the `4ps` and `4p²s`), the exchange rate `6` (the LOW
limit `Λ = 6qB`) and the natural seed slope `K`. Any improvement of θ through the chain must change
one of these four inputs; refining the faces cannot.

## Files

- `discriminant.py` (`.log`): the `p`-discriminant as a norm form; its two roots.
- `amgm.py` (`.log`): mixture identity, the sum-of-squares identity, the equality class.
- `lambert_origin.py` (`.log`): cutoff forms, `D − pA = (1 − p)²E`, constant `X((5s − p)/E)`,
  the cofactor of `L_p`, the first integral, the extactic polynomial `10(1 − p)²E²L_p`.
- `switching_darboux.py` (`.log`): extactic polynomials of degree 1 and 2 of the switching field.
- Lean: `../lean-lab/ChainAMGM.lean`, `../lean-lab/ChainLambertOrigin.lean` (both proved).
