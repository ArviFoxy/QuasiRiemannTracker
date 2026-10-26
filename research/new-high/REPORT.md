# Saturated HIGH rows: mechanism, a no-go theorem, and priced new inputs (2026-10-26)

Written by the new-HIGH probe agent. It is saved here by the orchestrator, because the agent could not
write report files. Scripts and logs are in this directory.

## Summary

- **No relaxation of the binding HIGH gate can be proved from the present inputs.** The saturated HIGH
  count at the binding corner (ν, p) = (q, 1/2) is already optimal for these inputs. The no-go theorem
  is in §4.
- **The best new input is a slot cost c < 2 in Theorem 7.3** (the marked inverse moment), for canonical
  smooth prime pools.
  - At c = 1.8: θ* = 0.8739327, Δ = −3.37e-4 against 0.8742701. Almost all of it (−3.30e-4) comes from
    the return's count, not the faces.
  - At c = 1.9 the return alone gives −1.42e-4.
- **Runner-up: a long inverse moment with slope κ < 5/6** in place of (204).
  - κ = 0.80: Δ = −2.06e-4 (−1.85e-4 from the return alone).
  - κ = 0.82: Δ = −8.4e-5.
- **Both inputs are open problems for sextic characters.** Neither is in `openai_baseline` or
  `hailey_collet_1252270103`. In Lean they would replace the `inverseRep` and `inverseUnmarked` fields
  of `FiberMomentsK`, plus the return's `V` and inverse line.
- **The source chain is a weak lever.** Removing the HIGH gate entirely is worth at most −9.3e-5, and
  only with the return's sP raised from 0.058 to about 0.063. With sP fixed at 0.058 the gain
  saturates at −1.0e-5.

## Prices

Computed with the exact return (`ret_scan.py`: Lemma D, dMinus > 1/2), design cap 0.075, sP = sC = 0.058,
h = 0.8044. The P face is at the envelope crossing E = 0.843 and the C face at s = 0.06.

| model | s* | source only, sP = 0.058 | source only, sP re-optimized | return only | both |
|---|---|---|---|---|---|
| published grid flow | 0.0577 | 0.8742701 | – | 0.8742701 | – |
| baseline, continuous q | 0.05769 | 0.8742691 | 0.8742691 | – | – |
| uniform Δξ = +0.001 | – | 0.8742671 | – | – | – |
| uniform Δξ = +0.005 | 0.05828 | 0.8742599 | – | – | – |
| κ = 0.82 | 0.05809 | 0.8742624 | 0.8742624 | 0.8741946 | 0.8741864 |
| κ = 0.80 | 0.05871 | 0.8742599 | 0.8742520 | 0.8740848 | 0.8740643 |
| c = 1.9 | 0.05786 | about −3e-6 (closed form) | – | 0.8741281 | – |
| c = 1.8 | 0.05809 | 0.8742624 | 0.8742624 | 0.8739400 | 0.8739327 |
| HIGH removed at every (ν, p) | 0.0632 | 0.8742599 | 0.8741774 | – | – |

## 1. What the binding branch counts

- **Rows and class.** HIGH rows at the lowest density ν = q, where L(s, χ_row) has a zero at
  σ = (1+q)/2. Amplitude class p = 1/2: every marked slot polynomial is saturated.
- **Detector cutoff equation.** νξ + (5/6 − ν)(I_p(ξ) + P_p(ξ)/2) = (5/6)Q.
- **Branch 5.** The inverse witness is at its cap z = (Q−r)/2. The plain witness is at the HIGH
  parent's affine cap (B_H Q − y)/Λ_H. Neither cap involves the slot width S.
- **Why the slot gain vanishes.** Each unit of selected slot width buys 2pν of count reduction and
  costs 2pν of slot weight, so the surplus (1−2p)νS is zero at p = 1/2. Both witnesses are limited by
  capacity, not by slot supply. The slot-limited inverse branches 0–2 have margin 1.4e-2.

## 2. Mechanism

**Lemma 1 (triple point).** At ξ = T and p = 1/2, the slot-limited plain threshold T − S and the
affine plain threshold (ΛT − B)/(Λ − 1) both equal E, using B = E + Λs. So branches 3 and 5 coincide,
and the binding plain witness is the configuration itself.

**Lemma 2 (closed-form floor).** Let κ be the long-branch slope and c the inverse slot cost. Put
I_T = (cT − 1)/(c − 1) and t_cut = I_T + E/2. Then branch 5 holds iff

  q ≥ q_min(E, s) = κ(t_cut − 1)/(t_cut − T).

With den3 → 0⁺ this gives Λ = 6qE/(1 + q − 6qs), i.e. the chain ODE E' = −6 q_min E/(1 + q_min − 6 q_min s).
- It matches the full-gate float flow to 2e-5 in Λ on [0.016, 0.062], so every other gate is slack.
- Sensitivities: ∂q/∂κ = 0.696, ∂q/∂c = 0.077.

**Lemma 1′.** The envelope E(·) is convex. So no other tangent face is a better HIGH parent; the
natural face and Sil's face are weaker still.

## 3. Lemma 3: how far the LOW route reaches

At the crossing (X₀ = 0, a = r, d = 6qβr/den3), a class whose excess slots erase at rate ρ has RAW
excess −r[1 − 6β(ρ − q)/den3]. So the LOW route pays iff ρ < q* = (1+q)/(6β), and
q* = q_max − (q_max − q)/(6β) ≤ q_max = 1/(6β − 1).

Consequences:
- A HIGH class (ν, p) has ρ = 2pν, so the corner (q, 1/2) is unique. No reassignment of classes between
  LOW and HIGH moves it.
- An "energy budget" bound (Markov on the parent) is this same route, exactly marginal in the
  continuum.

## 4. Theorem (no-go)

**Inputs.**
- (204), the long moment;
- Lemma A_K / Theorem 7.3, with any number of copies and slot-only counts;
- every chain face, and the unmarked plain fourth moment;
- Lemma 14.2 with (207)–(208), at any number of cutoffs;
- the LOW route.

**Claim.** Fix ν ≥ q*, p = 1/2 and ξ > ξ*(ν). There are witness profiles, saturated on
R = [0, I(ξ)) ∪ (t_max(ξ), 3/2] for the Möbius witness and on M = [0, P(ξ)/2) for the plain witness,
that satisfy the detector at every cutoff. On such a profile, every available bound and every Hölder
combination exceeds U^{Q−νξ}.

So ξ* is the exact limit of these inputs. The theorem says nothing about which rows exist.

## 5. Directions examined

- **Halász–Montgomery.** Pairs have conductor about U², with only Pólya–Vinogradov. This gives
  U^{(1−ν)/ν} = U^{0.72} at ν = 0.58, against the U^{0.477} needed. Dead.
- **Huxley subdivision.** Dead: the second term is at least N^{3−3ν}.
- **A Heath-Brown-type sextic large sieve.** At best U^{1−ν/2}. Dead below ν = 2/3.
- **An optimal sextic large sieve (U + N)‖a‖².** Conjectural. It would give c = 1 and remove the gate.
- **Fourth-power transfer inside the HIGH count.** The slot product enters as χ_u(D). Transferring it
  would cost about 6 to save 1, against the current 2. Only sixth powers are invisible to the row lift.
- **Energy budget, per-class cutoffs.** Ruled out by Lemma 3 and the theorem.
- **Row sieve.** The only power-saving redundancy is u ↦ u a⁶, which (204) already uses.
- **Mollified and tensor detectors.** Only O(1) changes, or the K copies, which are slack.

## 6. The two new inputs (conditional)

**(LM_κ)** Σ_{q_u≍U} |M_u(U^r)|² ≪ U^{1+κ(r−1)+ε} for 1 ≤ r ≤ 3/2.
- Today κ = 5/6, from the sixth-power lift of Theorem 4.1.
- A lift-free equivalent: Σ_{q_v≤H} |M_v(D)|² ≪ H^{1−λ}D^λ for D ∈ [H, H^{3/2}] gives κ = λ.
- Gate changes: in the source, HF5's 5/6 becomes κ. In the return, V = κ − δ in FR4/FR6.

**(MI_c)** Theorem 7.3 with first gate r + c·z ≤ m − c₁, c < 2, for canonical pools.
- In the descent (MF3.38) the slot width is counted twice: once in the length D₀ = r + z, and once as
  the burden z₀ carried into the child. This is a possible structural slack, to examine against the
  re-reflection argument in `../LOG.md`, which concluded that slot cost 2 is intrinsic.
- Gate changes: in the source, I_p = max(ξ − 2pKS, (ξ − 2pQ/c)/(1 − 2p/c)). In the return, p becomes
  2p/c in the inverse line.

## 7. Where the value is

The final return's count R* (FR9/NR1) uses the same three witness lines. It binds at δ ≈ 0.44,
p → 1/2, with coefficient 3d/4 ≈ 0.6 in the return exponent. The source chain reaches θ* only through
s*, with dθ*/ds* ≈ −0.017 once sP is re-optimized.

## 8. Recommendation

Stop work on the source HIGH gate itself. If a new analytic input is pursued, aim at (MI_c) first
(best price) or at (LM_κ) (cleaner statement), and deploy it in the return.

## Tools

- `closed_form.py`, `price_closed.py`: instant pricing.
- `ret_new.py` (env `QRH_KL`, `QRH_CI`, `QRH_TMAX`): the exact return with general count lines.
- `hgate.py` (`test_hgate.py`), `flow_new.py`, `models.py`: the generalized gate and flow.
