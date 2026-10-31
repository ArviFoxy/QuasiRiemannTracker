# State of knowledge (2026-10-31)

One page with everything currently known about lowering θ below the record. Details and derivations are in
`journal/JOURNAL.md`. The lever table is `frontier/BAR_STATUS.md` and the dependency tree is `frontier/PROGRAM.md`.
Evidence tags: [Lean] built and checked; [exact] exact rational computation; [numerical] float or numerics;
[derived] paper argument; [read] from the literature or the library.

## 1. Records and the bar

| what | θ | note |
|---|---|---|
| upstream record, PR 99 (Bebel) | 0.8733819666133 | #100 and #101 refine it at the 1e-16 level |
| **bar** (5e-5 below PR 99) | **0.8733319666** | |
| our bank, `lean/arvi_bank/` | 0.87338228 | [Lean] 3.1e-7 above PR 99; not submitted |
| our merged PR 97 | 0.87341198 | selected-norm leaf |

No upstream PR has landed since PR 99 (checked 2026-10-31).

## 2. Where θ is bound [exact, numerical]

- **The binding.** θ is set by one row of the final return: the newTop edge, at δ ≈ 0.425, p = 1/2.
  - The float model (`fresh-look/second/base_models/worth.py`) reproduces the bank, 0.87338228.
  - So does the exact kernel mirror (`fresh-look/scripts/mirror3.py`, `cover3.py`): N = 6330886 covers all four
    edges, and N + 1 fails on newTop.
- **What moves that row.**
  - Mainly the end face Λ of Sil's native line (Λ = 2.0001 in the bank). In the float model that is ≈ 1.5e-5 per
    0.01 near Λ = 2.
  - Then the long slope 5/6, the numerator capacity, and the count inputs behind the D-levers (§4).
- **Two walls hold Λ at 2. Either alone buys ≈ 0.**
  - The **K-wall**: the overshoot gate Λ(1 + K) > 6KB with deletion cut K ≥ 1/2. PR 93's selected norm reaches
    its fixed point only above slope 1/2.
  - The **reference wall**: Sil's principal gate Λ > 2, from the √A short reference.

## 3. Proven in Lean (ours; standard axioms only, no `sorry` outside the sketch package)

| package | content |
|---|---|
| `arvi_selected_leaf` | β ≤ 0.87341198 (merged upstream as PR 97) |
| `arvi_bank` | β ≤ 0.87338228: line to Λ = 2.0001, transport fork, return at h = 0.8097 |
| `arvi_prime_dilation` | reference wall without metaplectic input: `phase_mul`, the canonical phase `phaseCan` with exact multiplicativity, `bilinear_sieve`, **`correlation_bound`** (slot-convolution spike correlations bounded through Sil's `OptimalBound`) |
| `arvi_polar_sketch` | **sketch package, one `sorry`** (`polarInput`, the Kubota polar input). Everything downstream is proved from it as a hypothesis: R1 below K = 1/2 from `NaturalSelectedCellNormFrom δ₀`, `ReferenceAtγ`, and the scalar gates of the line down to Λ = 1.965 at K₀ = 0.4869, γ₀ = 0.51 |
| `arvi_kwall` | barrier results (`no_balanced_bound_below`); the spike-free conjecture (`SexticSpikeFree.lean`) with proved reductions; `SpikeRule.lean` (dilution closes for slopes δ > 7/36); `ReciprocityBridge.lean`; `TransposeCorrection.lean` |
| `arvi_rip`, `arvi_primeface`, `arvi_newpowers`, `arvi_ode_shape`, `arvi_energy_region`, `arvi_face_region`, `arvi_uniform_chain`, `arvi_density`, `arvi_return_tuning` | see `lean/README.md` |

Upstream facts we rely on [Lean, read]:
- Sil's `OptimalBound` proves the sextic large sieve with majorant A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6} on
  sixth-power-free rows and columns. That is de Faveri's conjectured optimum, so the sextic family is not
  orthogonal at the balanced point.
- Sil's `pair_poisson`, `coherent_weighted_bound`.
- The baseline's cubic Kubota theory: pole-free reflection only.

## 4. What each open input is worth (priced before any long project)

**The faces route (both walls), conditional** [numerical: `frontier/conditional_gains.py`; exact:
`frontier/conditional_exact.py`].

| K-wall cut K (with the reference wall's target 2) | end face Λ | float θ*, vs PR 99 | exact all-edge θ, vs PR 99 (bank guard constants) |
|---|---|---|---|
| 0.5 (today) | 2.0000 | +1e-7 | +3e-7 |
| 0.4877 | 1.967 | −5.1e-5 (the bar) | −5.0e-5 (bar + 9e-8) |
| 0.4815 | 1.95 | −7.8e-5 | −7.0e-5 |
| 0.4634 | 1.90 | −1.6e-4 | −8.0e-5 |
| ≤ 0.4286 | 1.80 (target-2 floor) | −3.1e-4 (ceiling) | −1.21e-4 |

- Near the bar the two models agree.
- Below Λ ≈ 1.95 the exact binding moves to δ ≈ 0.37 and the bank's count windows lose their guards. So the
  certified payoff with today's return design is ≈ 1.2e-4 at most. Re-tuning the guard constants per face could
  recover part of the float ceiling (not done).

**Single levers at the bank face** [numerical]:
- **Long slope.** 5/6 − 0.0107 is still 4e-6 short of the bar; 5/6 − 0.02 gives −3.7e-5 vs the bar. It needs B2,
  twisted-Chowla strength.
- **Numerator capacity.** +0.0022 at the binding reaches the bar. There is no mechanism: the physical face is one
  linear face.
- **D2.** A power saving η₀ ≈ 7e-4 in a fixed-index cross moment (affine multiple Dirichlet series).
- **D4.** A thin-family sixth moment with excess ε₆ ≈ 0.115; proven 0.213.
- **D1.** A prime-pool face at Λ ≈ 1.97. It needs the K-wall at every slope with excess ≲ 0.034, the Mellin
  rescue, and the low-slope gap.
- **Envelope coefficient.** c = 6 → 5.9 (≈ 5e-5). Rigid for every known block type.
- **Doubled-block share** φ ≈ 2.5%: no mechanism.

## 5. The open inputs, by type

| input | statement | type | status |
|---|---|---|---|
| **A‴ (the corner)** | for the K-wall's balanced leaf vector (two smooth plain factors of length ≈ √X, tiny slots), the large sieve over the full row family (sixth-power multiples included) at the balanced point is ≪ X^{1+ε}‖v‖². Equivalently, Σ_{m∼H}\|⟨v, f_m⟩\|² ≤ B^{5/6+ε}H^{1/6}‖v‖² for every H in [B^{0.21}, B^{0.96}] | Lindelöf-on-average fourth moment of the sextic family; a breakthrough-level open problem (the cubic analogue is open) | needed exactly (tolerance γ → 0) for every K < 1/2 |
| **A (polar input)** | the 6-fold Kubota theory: polar asymptotic of twisted sextic Gauss-sum sums, pointwise and on average | classical on paper (Kazhdan–Patterson), unformalized; even n = 3 lacks the polar Voronoi formula in Lean | needed for the K-wall's single-factor leaves in the twist band B^{0.21}–B^{0.6} (the elementary route has the squarefree gap, §6) |
| **C (corrected recursion)** | de Faveri's recursion run off the spikes to 1 + γ | elementary, new; its step-3 core (corrected Cauchy–Schwarz, level closure) is open | arithmetic in Lean |
| **target 2 (reference wall)** | short reference past √A for smooth × prime vectors, up to B ≤ A^{0.51} | elementary | Lean core done (`correlation_bound`); the Poisson fork of `coherent_weighted_bound` remains |
| **B2** | Möbius sieve past the family size, saving (D/H)^λ with λ ≥ 0.178 | twisted-Chowla strength | open |
| **D2** | any power saving η₀ ≥ 7e-4 in Σ_k S(k, P) conj S(k, P′), P ≠ P′ | affine multiple Dirichlet series over a number field (only log savings known even for quadratic fourth moments) | numerically η₀ ≈ 1/2 |
| **D4** | Σ_u ∫\|L(1/2 + it, χ_u)\|⁶ ≤ U^{1.115} on the thin sextic family | beyond the state of the art even for all Dirichlet characters mod q | numerically ε₆ ≈ 0 |

**Reading.**
- Every route to the bar needs at least one breakthrough-level input (A‴, B2, D2 or D4).
- The faces route additionally needs a large classical formalization (A) and one open elementary step (C).
- The conditional payoff of the faces route is real: ≈ 1.2e-4 certified with today's return design, up to 3.1e-4
  after re-tuning.

## 6. Established, corrected or withdrawn on 2026-10-31

- **Three Poisson steps** (twist mean square of one smooth Gauss-sum factor) [derived, numerical].
  - The polar shape |W̃(s₀)|²H^{1−1/n}X^{1+2/n} matches the existing logs: n = 3 shows the predicted H^{−1/3} and
    X^{2/3} scaling, n = 6 the H^{−1/6} scaling.
  - The route differs from de Faveri–Dunn–Hoffstein's (twist side, Rankin–Selberg).
  - Two gaps were found in the elementary proof:
    - the gcd(n, n′) blocks, costing X²H^{−1/3};
    - the squarefree support of Gauss-sum vectors. Its Möbius blocks carry (h/d)₃ and defeat the last Poisson
      step; the best crude bound is X²H^{−1/12}. In Sil's sixth-power-free normalization the dual weight is
      N(rad I)^{−1/2}, and the gap persists.
  - So "elementary away from the corner" is **withdrawn**.
- **Twist large sieve corrected** [Lean, read]. The proven bound is Sil's `OptimalBound` majorant, not an
  orthogonal (H + X).
  - It covers the K-wall's need only for H ≳ X, so the corner's open band is [B^{0.21}, B^{0.96}].
  - The claimed bilinear "B^{10/9}" improvement is **withdrawn**: the theta term at H ~ X keeps the excess 1/6.
- **The sixth-power amplifier** (fresh look at the corner) is circular. The cluster-inclusive large sieve is the
  goal itself in summed form. It leaves the clean restatement of A‴ in §5.
- **The K-wall tolerates no excess** [numerical]: at slot width → 0 the selected price is γ − (1 − δ)s.
- **The envelope's 6u** (2u column + 4u D⁴ transfer) is both the overshoot gate and the corner. c = 6 is forced
  for known block types. T8′ (Cauchy–Schwarz midpoint) is dead on the native line.
- **Conditional gains priced and checked exactly** (§4). No long Lean project on the faces route until one of its
  open inputs moves.
- **Earlier the same day**:
  - the reference wall needs no metaplectic input (prime dilation; Lean T3 done);
  - the 2026 literature (DFDH, DIPP) shows the sextic balanced excess is real for general vectors, and fourth
    moments are open.

## 7. Numerical evidence (summary; `rip/theta/README.md`, `rip/moments_probe/`)

- **The sextic large sieve's excess** at the balanced point is the residue of a Kubota series: the theta spike,
  B^{1/q}.
- **Mellin-zero vectors.**
  - Radial weights with zero Mellin transform at s₀ = 1/2 + 1/q remove it: +224% → +2.5% at 10⁵.
  - Mellin-zero plain vectors sit at the masked null against twisted thetas of every twist size measured, in both
    families.
  - Balanced convolutions (the corner's shape) sit at the null even without Mellin zeros, at L = 10⁵.
- **D2:** fixed-index cross-correlations are random-like (η₀ ≈ 1/2).
- **D4:** the thin family's sixth moment has no N-term (ε₆ ≈ 0).
- So the open inputs look true; what fails is provability.

## 8. Literature (checked late October 2026)

- de Faveri–Dunn–Hoffstein (arXiv 2607.07911): the cubic and quartic large sieves are not orthogonal; they
  conjecture the order-n norm, which Sil's library proves for n = 6.
- Diaconu–Ion–Paşol–Popa (arXiv 2607.27131): second moments of r-th order Hecke L-functions.
- Nothing newer on fourth moments, Lindelöf on average or structured large sieves for cubic or sextic families.
  Nearest: Dunn, arXiv 2403.13151 (bilinear sieve for metaplectic cusp-form coefficients, a different kernel), and
  Hu–Petrow–Young, arXiv 2506.14741 (PGL₂ cubic moments).

## 9. Fresh look at θ overall (2026-10-31, delegated, neutral brief)

- **Verdict.** Nothing reaches the bar with known mathematics. The lever table above is complete within the
  architecture.
- **The binding.** newTop at δ = 0.426, p = 1/2. The ridge within the bar's margin is flat (δ ∈ [0.386, 0.464],
  p ∈ [0.485, 0.5]), so a lever must lower the count along the whole ridge.
- **Count face and physical face separate.** The count face alone breaks even at Λ ≈ 1.943.
- **New: a width-floored count face.** Faces below Λ = 2 are claimed only for slot widths ≥ s0 ≈ 0.118, with the
  base face below the floor.
  - s0 is capped by a jump guard in Collet's window.
  - Float ceilings: −4.2e-5 vs the bar at a stop face 1.90, −6.2e-5 at 1.88.
  - The K-wall then tolerates a uniform excess γ ≈ 0.048 (instead of 0) at a moved corner: x₁ = x₂ ≈ 0.39,
    slot width ≈ 0.12.
  - Against the proven sieves it is still ≈ B^{0.14} short. So it is A‴ in weakened form (Lindelöf on average up to
    B^{0.05} at the moved corner), plus C and target 2.
  - It is the right target for partial fourth-moment progress. Exact check, composition with Sil's step and the
    jump-guard reading are still to verify.
- **Dead:**
  - density steps past the native end (≤ 1.2e-5);
  - bootstrap and transport (≈ 1e-6);
  - Guth–Maynard, Huxley and Halász–Montgomery (inapplicable);
  - a PR 96 port.
- Details: journal entry "Fresh look 3"; scripts in `fresh-look/third/`.

## 10. Repository notes

- **Lean mirrors** (`lean/`) match the built packages for the bank, the prime dilation, the polar sketch, the
  K-wall and the rest.
  - The full packages of `arvi_density`, `arvi_selected_leaf` and the return retunes live on the submission
    branches `submission-arvi-density` and `submission-arvi-selected-leaf`.
  - `arvi_mixed_step_20261026` is a re-prefixed copy of `mixed-step/lean/`.
  - Not in git: the local audit fork `arvi_followup` (the PR 73 package with the changes listed in
    `verification/AUDIT_FOLLOWUP.md`) and the generated scratch package `arvi_density_lab` (regenerated by its
    script in `density/`).
- **Old fork history** still holds session links in older commits. Scrubbing them needs a force-push, which has
  not been authorized.
