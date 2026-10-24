# Mixed prime/plain slots (round-4 architecture proposal), 2026-10-24

## The proposal

A fresh-perspective agent (round 4, architecture lens) read the binding case as **the zero
amplifying itself through the slots**. The main slot of a bad row is the prime sum
`−Σ_p w(p)p^{z−1}ψ̄_u(p)`. By the explicit formula, the row's own zero makes this sum coherent, of
normalized size `P^{δ/2}`, so `p = 1/2` is available to the adversary for free. At the binding
point (`δ = 0.4546`) the agent's balance is:
- slot amplification `δpℓ ≈ 0.038`;
- marks win back `≈ 0.015` through the count and `≈ 0.004` through the numerator;
- net, the adversary gains `≈ 0.019` by saturating the slots.

If saturation were impossible (worst case `p = 0`), θ would drop by about 2.5e-3.

**Proposal.** Replace part of the prime slot length by squarefree-plain slots
`Σ_d |μ(d)| ψ̄_u(d) d^{z−1} w(q_d/P′)`, whose generating function is `L(s,ψ)/L(2s,ψ²)`. Three
claims go with it:
- a zero does not force these slots large;
- the principal row still gains `P′^{1/6}` (with a convergent Euler factor, no log loss);
- plain slots could be marked in the P line at a cost `c_S ≈ 1`, because "plain polynomials
  reflect".

The agent's toy model gives `Δθ ≈ −3.8e-4` at prime fraction `f = 0.8`.

## Verdict: closed (it needs a new diagonal three-plain moment)

**1. Under an honest budget, equal cost makes things worse.** `cs_threshold.py` is the agent's toy
with one face budget shared by every mark in the P line: `2m + Λz_P + c_S z_S ≤ B`, with
`B = 0.951` and `Λ = 2.77`. Logs: `cs_threshold_I0.log`, `cs_threshold_I1.log`. Results at
`f = 0.9`, relative to all-prime slots in the same toy:

| plain mark cost `c_S` | 2.77 | 2.6 | 2.4 | 2.2 | 2.0 | 1.5 | 1.0 |
|---|---|---|---|---|---|---|---|
| Δθ | +9.7e-5 | +9.7e-5 | +5.4e-5 | +4.0e-5 | +1.7e-5 | −4.1e-5 | −9.3e-5 |

At `f = 0.8` and `c_S = Λ`: `+1.9e-4`.

- At equal cost the mixed design is **worse**. Two independently saturable slot groups enlarge the
  adversary's choice set (`(p_prime, p_plain)` ranges over a product), and nothing is gained back.
- Break-even is `c_S ≈ 1.85`, and −1e-5 needs `c_S ≈ 1.8`, about a third below the face's
  prime-slot cost `Λ = 2.77`.
- Giving plain slots I-line marks at MI cost 2 (`IPLAIN=1`) changes nothing, because the binding
  is in the P line.

**2. Most of the agent's gain is a budget assumption.** The agent's toy lets plain marks use the
unit budget `2m + c_S z_S ≤ 1`, while prime marks use `B − 2m` separately. That assumption alone
gives `Δθ = −1.5e-4` at `c_S = Λ` (`cs_threshold_I0_unit.log`). It amounts to assuming a diagonal
moment with three plain factors (two long, one short) at total length 1, outside any face.

**3. The paper's induction prices a third plain factor exactly like a prime slot.** In 7/8 paper
§18 (Lemma 18.1):
- **Slotless case.** It is unrestricted, but only because the padded core
  (`A ≤ M + δ`, eq. 18.10) is extended by reflecting **at most its two plains**: "The unrestricted
  zero-slot assertion follows once from the padded core by reflecting at most its two plains" (§18.8).
- **Children leave the core.** The children of a product have `A′ ≤ A` while the width drops by at
  least σ (eq. 18.38 with `ℓ = 0`; the zero-slot proof has no amplification).
- **Why a third plain factor cannot be reflected away.** After both main plains are reflected to
  at most `M′/2 + ξ`, a child with a third plain of length `z′` can still exceed its core by `z′`.
  Reflecting the short factor gives the long dual `M′ − z′`. So its only exit is pointwise
  deletion.
- **Pointwise deletion costs the same.** Deletion is exactly the slot mechanism: a slot of length
  `d` releases `6κd` of affine room and costs `κd` (eq. 18.39). That rate is what pays the
  amplified children's excess `6(w + ℓ)`.
- **The plain slot has the same pointwise bound.** In the zero-free half-plane `Re s > (1+κ)/2`,
  Littlewood's bound `L ≪ Q^ε` gives `|S_z|² ≪ Z^{κz+ε}`. That is identical to the prime slot's
  (18.12). So a squarefree-plain slot gets cost `6κ`, improved by the source chain to `Λ`, the same
  as a prime slot. "Plain polynomials reflect" applies only to the two long plains.

So lemma (a), `Σ_u |S_m(u)² S_z(u)|² ≪ U^{1+ε}` for `2m + c_S z ≤ B` with `c_S ≤ 1.85`, is a
**diagonal three-plain moment** for the sextic family. It is not in the paper, and it is the same
object as the "plain fourth moment with slot cost below Λ" in `../barriers/README.md`. That object
is blocked by the Patterson bias of plain duals, which is what forces the amplified descent. Its
classical analogue (quadratic family) is immediate from Heath-Brown's diagonal-sharp large sieve.
The sextic large sieve is not diagonal-sharp at length `U` (extra term `U^{7/6}`), and that is the
whole difficulty.

## What survives

- **The mechanism reading is correct and useful.** Self-saturation of prime slots by the row's own
  zero is what makes `p = 1/2` bind. It is worth about 2.5e-3 in θ if it could be prevented.
- **A new quantitative target for atom 2's plain side:** a diagonal three-plain moment (two plains
  of any length, one short plain factor) at slot cost at most 1.85 would be worth `≥ 1e-5`, and
  `c_S = 1` about 9e-5 at `f = 0.9` (shared budget).
- The agent's other items: the pointwise numerator instead of Hölder, decoupling the slot character
  from the denominator, and sparse-set Halász were all checked by the agent and found not useful
  at the binding point. Its height-localized fallback is bookkeeping only.
