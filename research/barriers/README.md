# Where the method is pinned (2026-10-24)

This note collects, in one place, the four analytic exponents that bind the current argument at
θ ≈ 0.87472, where each one comes from, how far it would have to move for a 1e-5 gain, and the
reasons it does not move with the tools in the papers. Details and dead ends are in `../LOG.md`.
Numbers come from `../atom-targets/` (float LP model) unless marked exact.

## The four atoms

**1. Reflected-energy slot cost 2.** Paper Lemma 14.3: `T_d = 2H + 2z_a − N_*`.
- Origin: a divisibility mark `p | A` on the cubic-theta index puts `p` into the cusp denominator
  `c`. The reflection at `a/c` rescales by `c²`, and the hybrid norm already saves the whole slot
  length in the column branch.
- Cleanest form (2026-10-24). In the hybrid norm (MF2.29) the column branch's dual sum carries
  the twist `χ_k(n)³χ_P(n)^{-2}`, the row's quadratic character times the slot tuple's cubic
  character. Its critical length is therefore `Z^{H+z}` with `H = 2(r+z) − m`. The maximal dual
  length is `T_d = 3r + 5z − 2m`, and `T_d ≤ H + z ⟺ r + 2z ≤ m`. So the inverse moment's budget
  says exactly that the dual sums stay within the joint critical length. In the probe's marked
  energy (Theorem 7.1) the condition `M + 2z ≤ N_*` is `T_d ≤ H` (the row count), which lies inside
  the joint critical length. In both cases, between the row count and the joint critical length,
  the quadratic sieve's `N` term costs the excess. Beyond the joint critical length, re-reflection
  with the optimal sextic sieve (de Faveri) costs the `A^{7/6}`-type term, which is worse near
  the boundary.
- It binds in three places:
  - the physical probe's marked energy `x + y + ℓ ≤ 1` (`dθ/dε = −0.0628`; for −1e-5 the cost must
    fall `2 → 1.99905`);
  - the count's marked inverse moment `r + 2z ≤ 1` (for −1e-5: `2 → 1.995`);
  - the source chain's HIGH inverse cap `(Q − r)/2`.
- Why it does not move: removing the excess needs an almost diagonal quadratic large sieve at dual
  length `K^{1+η}` for reflected Gauss-sum coefficients, i.e. Lindelöf-quality bounds for twisted
  cubic theta series. Amplifying the residual rows by squares fails on the redundancy term of the
  full family. Probe redesigns either lose the sextic slot factor (cube marks) or pay more than they
  save.

**2. Sixth-power exchange rate 6.**
- Origin: `G(u, hp⁶) = G(u, h)`. Sixth powers are the full invariance group of sextic Gauss sums
  and sextic symbols, and they have density `X^{1/6}` among elements of norm `≤ X`.
- It binds in three places:
  - the long Möbius moment `(1+5r)/6` (for −1e-5: lower by `2.7e-4` at `r ≈ 1.155`);
  - the plain descent's slot cost (`Λ ≈ 6qB`);
  - the LOW amplifier denominator `1 − 6qB₀/Λ₀ ≈ 0.007`.
- Why it does not move: exact invariance cannot use a denser multiplier set. Twisted
  multipliers (`p³`, `p²`) orthogonalize rather than amplify.
  - **Correction (2026-10-25, after PR 74):** this is true only where the multiplier enters the
    argument of characters attached to the summation variable (Möbius-type rows: the long line, the
    11/12 base). Where it enters the frequency of Gauss sums with the row as modulus, the twist
    `χ_a(D)²` of `G_a(D⁴k) = χ_a(D)² G_a(k)` depends on `(D, row)` only. Sil's `whole_column` turns
    the twisted family into the same polynomial at `D⁴k`, an exact energy transfer, and the source
    face's slot cost drops from `6κ` to `2 + 4φ` (93/25). See `../combined/BARRIER_REVISITED.md`. The long moment beyond the family is
  equivalent to zero-density input, and bootstrapping with the count itself is circular exactly at
  the binding `δ ≈ 0.45–0.5`.

**3. HIGH density floor `q ≥ 1/2`.**
- Origin: the HIGH count's gate `H_ν + G > f` at `ν = q`. Below `ν = 1/2` the gain `G` (itself
  pinned by atoms 1–2) no longer covers `H_ν`.
- The chain's fixed point is `Λ → 6qB ≈ 3B`. Lowering the floor to 0.45 gains only `5·10⁻⁷`
  (exact).

**4. Sextic theta bias `c_g = 1/12`.**
- Origin: the Gram estimate's exceptional frequencies `k = a⁶e₀`. With the exact correlation
  (Lemma 13.3) both complete column means survive iff `v_p(k) ≡ j_p − 1 (mod 6)` at the S-primes,
  so main terms exist for an S-supported `e₀`.
- Mixtures of probe characters give only positive diagonal main terms. For −1e-5 the bias term must
  become `P_a^{1/6 − 2.5e-4}`.
- Why it does not move (2026-10-24, late): the bias is the signal channel. Poisson in the row of
  the low separation `Σ_m A_m B_m` pairs the Gauss-sum polynomial with the completed row through
  dual frequencies `k`. At `k = a⁶e₀`, the identities (4.7) (`γ₁ = γ₂²G`, `γ₂³ = μα`) turn the
  row's dual coefficient into `∫Z^tΦ(t)E(t)/L(1+t, η·ξ₀)dt`, the target's own inverse L-function.
  - With the zero-free hypothesis at `β*` the pairing is the Cauchy–Schwarz bound times
    `Z^{β* − θ_low}` exactly, `(1 + 3ℓ)/12 + θ_low − 1 = 0` (`../lean-lab/SignalChannel.lean`).
  - So the bias is the largest signal the energies allow. Only the energies (`‖A‖`, `‖B‖`, i.e.
    atom 1's marked energy) can move it.

## What is LP-tight

Given these four inequalities, every recombination tried is no better:
- Hölder between witnesses, joint numerator × witness moments (they reproduce Cauchy–Schwarz on
  affine branches), pointwise vs fourth-moment numerators, and witness-weighted numerator bounds;
- multiple or second-order detectors, smoothed mollifiers, and covering arguments over cutoffs;
- face selection, re-feeding, `h`, `z₀`, caps and windows.

The exact pipeline with every known refinement (Lemma F, fine pivots, density floor) is at
θ* = 0.8747257, against the next milestone of 0.8747189.

## What would move it

| new input | effect |
|---|---|
| Lindelöf-quality mean values for quadratic twists of cubic theta sums beyond the critical length (the column excess is the generic sieve's dual term and is plausibly not the true size; see `../LOG.md`, "Is the column-branch excess a real size?", where an earlier contrary heuristic is retracted), or an inverse-moment proof that keeps the signed off-diagonal | atom 1, all three places |
| a Möbius Type II estimate beyond the diagonal for sextic families, or any zero-density input stronger than the count itself | atom 2, long branch |
| a plain fourth moment with slots that subtracts the Patterson bias instead of amplifying | atoms 2 and 3 on the plain side; slot cost 2 there would lower the count `R` from 0.6047 to about 0.5996, worth about `7·10⁻⁴` in θ |
| a diagonal three-plain moment `Σ_u|S_m² S_z|² ≪ U^{1+ε}` for `2m + c_S z ≤ B` (one short squarefree-plain factor) with `c_S ≤ 1.85` | mixed prime/plain slots: break-even at `c_S ≈ 1.85`, −1e-5 at `c_S ≈ 1.8`, about −9e-5 at `c_S = 1` (`../mixed-slots/`); Lemma 18.1's induction gives only `c_S = 6κ → Λ`, because only two plains can be reflected |
| a Möbius scale-profile interpolation: for all but `U^{R−7.5e-5}` bad rows, `|M_r(ρ)|` saturated at `r = 0.741` and `r = 1.155` implies `|M₁(ρ)|² ≥ U^{δ−2c}` | the I line at `r = 1` takes the corner: the milestone needs `c ≤ 0.0294`, only within about `4e-4` of the corner; lossless (`c → 0`) is worth about `−7.8e-3` (`../LOG.md`, round-5 detector agent). The rows that escape need clusters of about `0.004·log U` zeros, so counting them needs a multiplicity-sensitive zero count with a power saving |

## Additions after the second pass (2026-10-24, later)

- **Why slot cost 2 cannot be removed by reflecting again.** The column branch's dual sums are a
  fixed cusp expansion twisted by the quadratic `χ_h³`. Re-reflecting them past their critical
  length would make the branch diagonal. But each reflection adds a theta factor `χ_p^{∓2}`, so the
  twist alternates between quadratic and sextic, and the generic sextic sieve's `(ML)^{2/3}` term
  then costs more than the excess.
- **Why the plain slot cost is `6κ` (then `6q`).** Slots are carried unchanged through the two
  transforms because prime sums cannot be reflected. Only the row scale shrinks, by the amplified
  ball growth `6ℓ`, against a density allowance `ℓ`. Pointwise deletion at rate `κ` (or `q` for LOW
  rows) pays the difference.
- **The source chain is HIGH-limited.**
  - With the HIGH gate switched off, the chain reaches the LOW limit `Λ = 3B` in one step, about
    +0.02 in face height at `s ≈ 0.041`.
  - The marginal value is `dθ*/dε_H ≈ −4.4e-3`, so 1e-5 needs `ε_H ≈ 0.0025`. That is a count
    improvement at densities 0.5–0.75, about 30 times what the return's count needs directly.
  - The centered terminal gate and every other gate have no value.
- **The physical face is evaluated on a level curve of the chain.** `(B − 4ℓ/h)/Λ` is flat along
  the chain's end, because `B` falls with `Λ`. So PR #69's `Λ_P > 3` restriction (needed only for
  FR21, which Lemma D removes) is worth just 2e-7.
- **Explicit-formula scale transfer.** Saturation comes from the zero-free bin, at one scale only.
  The binding crossing needs a left zero with `|1/L'| ≈ U^{0.085}` about `0.23` to the left. Jensen
  allows this with mildly elevated local zero density, and nothing counts such rows below `U^R`.
- **The source chain is an ODE** (`../chain-ode/`). The envelope obeys `E' = −6qE/(1 − 6qs)` with
  `q = (15 − 10/X)/6` and `X = E + (1 − g)s`. The two equations are the LOW limit `Λ ≥ 6qB` and the
  HIGH gate at the pivot. With the measured gain fraction `g(s)` this reproduces the 107-node chain
  to 1.2e-4. Early in the chain the gain is capped by the inverse cap and the slot supply together.
  Late in the chain the faces sit on the unmarked zero-density boundary `t = 10/(15 − 6q)`. So the
  faces are fixed by `ρ(ν)` (the long line), the exchange rate 6 and slot cost 2.
- **Bin-restricted faces do not exist in this framework.** The source step selects zeros on the
  transformed joint row `w` of foundations (168), not on the original rows. A zero-free bin on the
  original rows therefore does not make the HIGH class empty.
- **Screening test for atom 2 (the λ test, round 3).** A mean-value estimate of the shape
  `H + D(H/D)^λ` on a ball of rows of size `H` improves the long line only if `λ > 1/6`. For
  `λ ≤ 1/6`, sixth-power amplification still wins. At the binding `t = 1.155`, the needed 2.6e-4
  requires a direct bound `Σ_{q_u≍U}|M_u(D)|² ≪ U + D(U/D)^{λ}` with `λ ≥ 0.16834`. Atom 1's
  sharpest form is P1 in `../LOG.md` (the column-branch quadratic sieve slightly past `N = K`).


## Third pass (2026-10-24, late): ceilings and the common root

- **The source graph is at its ceiling** (`../variational-ceiling/`). The continuum limit of the
  face map, with PR #71's fine fees, gives θ* = 0.8747241. The comparison principle
  (`../lean-lab/MaximalEnvelope.lean`) proves this bound for envelopes satisfying the pointwise
  slope condition. Discrete graphs can be locally flatter at a pivot (the lag effect), and for them
  the ceiling is the measured limit: chains converge from below, linearly in the spacing. That is 4.8e-6 below the Lean branch and 5.2e-6 short of the milestone 0.8747189. The
  Lemma F chain under the Lean branch's own guards gives 0.8747263. Every sub-bar item found so far
  (fees, density floor, `Λ_P > 3`, pivots, caps, Lemma F) lies inside this ceiling.
- **The probe's bookkeeping has no slack** (`../return-slack/README.md`, `../lean-lab/BalanceAlgebra.lean`).
  Every term of the binding balance is an atom or a fixed normalization. The weighted numerator's
  Hölder weight is tied to the count's plain line by an exact identity
  (`../lean-lab/JointNumerator.lean`). The count face C is the envelope's best face at the binding
  crossing.
- **Atoms 1 and 2 have one root.** The inverse moment's initialization writes the nonprincipal
  Poisson expression as a ray-class combination of positive canonical squares, restoring the
  principal pairs with total weight `G(1) = 1`.
  - Past the diagonal, that restored dual diagonal is the long line's `+D` (atom 2).
  - In the mark-twisted form it is the column branch's `N` term (atom 1).
  - In the cleanest form (alternate 11/12 proof, eqs. 2.13–2.15) the obstruction is the quadratic
    large sieve over `O` for cusp coefficients of the cubic theta function, slightly past the
    diagonal.
  - The exchange rate 6 underlies the whole architecture: 11/12 = 1 − 1/(2·6) is the single-target
    amplification by sixth powers. The compensated probe is an amplifier for the principal row
    whose per-unit gain 1/6 is the cubic theta residue exponent.
- **What would move θ by 1e-5**: an explicit bound (A) or (B):
  - (A) the quadratic large sieve for (slot-twisted) cubic theta coefficients stays diagonal up to
    column length `K^{1+δ'}`, `δ' ≥ 1.3·10⁻⁴`;
  - (B) the sextic Möbius mean value past the diagonal has `λ ≥ 0.16834`.

  Inexplicit savings (Dunn–Radziwiłł type) cannot enter the rational certificates.
- **Both mean values behind the count are affine-type multiple Dirichlet series**
  (`../lean-lab/FEGroup.lean`): the inverse second moment has group C̃₂ and the plain fourth
  moment D̃₄. Their functional equations preserve a linear form (`s₁+s₂+w`, resp. `(Σsᵢ)/2+w`), and
  only the Hecke moves at cubes and sixth powers change it. Affine type is the boundary where the
  classical analogues (fourth moment of quadratic L-functions, second moment of quadratic twists
  of GL(2)) have only log savings unconditionally (X. Li, Invent. Math. 2024).

