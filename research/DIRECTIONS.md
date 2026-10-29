# Research directions (registry)

This is a living list of the directions seeded so far. **Phase: exploration.** Each direction is first
understood and priced. Exploitation (bound improvements past the 5e-5 bar) comes later.

Evidence tags:
- **[Lean]**: checked theorem.
- **[derived]**: our own derivation, not formal.
- **[numerical]**: computed, not proven.
- **[idea]**: not yet examined.

| id | direction | status | best evidence so far | next step |
|---|---|---|---|---|
| D1 | Twisted transfers | **open: needs new math** (task 156: new-math agent running) | existing Lean prices the type at 0; the obstruction is identified: the Cauchy–Schwarz over D discards the orthogonality of the D-terms (a factor W) [derived], and the HIGH counts and parents fix the character before Z [Lean] | see New-math targets T1 |
| D2 | Squared-prime slots (doubled blocks, e = 2) | **open: needs new math** (agent report done) | the count keeps only slots with pointwise lower bounds on counted rows [Lean `select_physical_product`]; a squared slot is the prime slot of φ_u², so the zero does not force it: by Jensen/3-4-1 a first-harmonic alignment a forces the squares only if a > 1/√2, but here a ≈ P^{β−1} ≪ 1 [derived]; even if granted, the net is −3e-6 to −9e-6 under the carrying costs (−3.3e-5 on the chain alone at a 5 % share) [numerical] | a mechanism making doubled slots visible to the zero (e.g. p² marks on the signal side), plus a source of P² pools; low priority given the payoff |
| D3 | Cubic amplifier (c = 3) | **open: needs new math** (a new detector) | in this framework the signal identity needs γ₁γ₂ and cubic rows give γ₂γ₄ = 1 [Lean]; scratch cubic-transfer lemmas build [Lean] | see New-math targets T3 |
| D4 | Classify sextic identities (geometry, Stickelberger, rigidity) | explored (task 147) | rigidity for every block Dᵐ and dilation [Lean, `arvi_newpowers/Rigidity.lean`]; local Stickelberger completeness [numerical]; geometric origin notes | feeds D1 (only twisted or new-room identities remain) |
| D5 | Continuous tuning of the return (per-patch detector, fewer certificates) | agent running (task 152) | return = 31 windows × 6 fixed branches, ~715 KB of admission certificates | slack in θ; size of a parametric certificate |
| D6 | Firing patterns / multilinear bank (higher moments, joint counts, Guth–Maynard-type structure) | idea | the existing pieces are multilinear: slot products, repeated marks, PR 93 joint count | first: per-class combination with the joint count (task 145, about −1.4e-5 [numerical]) |
| D7 | Codes and radar sequences (cross-field mechanisms) | agent running (task 154) | the sextic symbol is a power-residue sequence; Gauss sums are its spectrum; energy bounds are Welch-type bounds | read the knowledge base; map mechanisms to the proof |
| D8 | **Face region (long-standing goal):** define the true region of valid energy bounds and characterize it analytically, so the face iteration becomes unnecessary | started | faces are the supporting lines of a convex boundary curve, (Λ, B) is its Legendre transform, s₀ = dB/dΛ rises 0.0278 → 0.0834 [numerical, from the 130 faces]; a convex hull would add up to +0.011 plain length at s ≈ 0.05 [numerical, *valid only if Cauchy–Schwarz interpolation applies*] | D8a below |
| D8a | Cauchy–Schwarz convexification | **rule valid; the current return gains nothing** | rule legitimate [Lean-read]; no gain at equal plain lengths, and one step gives the whole closure [proved, `D8_NOTES.md`]; the gain (up to +0.011 in P) sits at unbalanced splits [numerical]; the count and the numerator both bind at balanced configurations [Lean] | D8a′: a numerator design with an unbalanced binding corner; why numeratorCap = 3/50 |
| D8b | Continuum ODE of the density chain; a faceless density chain | idea | done for the older source chain (`chain-ode/`, `faceless-chain/`: 59 nodes → 5 cubic pieces) [notes; partly Lean in that PR] | derive for the marked density chain |
| D8c | Properties of the true region: monotone, convex balanced slice, the ideal line P + s ≤ 1 | idea | heuristics [derived] | state precisely; prove what can be proven |
| D9 | Density floor below 1/2 | explored (task 144) | see `replan/floor.md` | revisit together with D6 |
| D10 | Visual explainer | done (task 153) | `explainers/sextic-filter-bank/` | update as directions mature |
| D11 | Mine upstream formal libraries for unused theorems | in progress (task 86) | | continue in the background |
| D12 | Mechanism catalogue for the top knobs (conductors, moments, tensor bounds) | pending (task 100) | | merge with D7 output |

## New-math targets

The research is about finding new mathematics, so the question for each direction is not "what does
the current library prove" but "which new theorem would pay, how much, and how plausible is it".

- **T1 (D1), twisted transfers.** One of these is needed:
  - (a) a trilinear "twisted-transfer sieve" bounding Σ_h |Σ_D Σ_n c_D(h) a_n (n/D)₃ 𝔤(n, h)|² without the
    Cauchy–Schwarz over D, at the size the D-orthogonality predicts;
  - (b) a zero-density / large-values count for the W twisted residual families jointly, whose cost in
    the twist conductor is small, together with face statements uniform over many base characters.

  Price on the current chain [numerical]:

  | conductor charge κ (scale units) | Δθ |
  |---|---|
  | 0 | −6.2e-5 (past the bar) |
  | 0.1 | −3.7e-5 |
  | 0.25 | −3.5e-5 |
  | 0.5 | −4e-6 |

  The natural cost, the conductor of a single twist, is κ ≈ 0.8–1.0. Beating it means using the average
  over the W twists. Literature to mine: Heath-Brown's cubic large sieve and its conjectured sharp form;
  hybrid and bilinear large sieves for cubic and sextic characters.
- **T2 (D2), squared slots.** A source theorem that supplies squared (doubled) slots with positive density,
  about 1.3 % of the transferred width. Lifting q to 3/4 upstream is worth 3.5–6.2e-5 [numerical].
- **T3 (D3), cubic detector.** A zero detector whose rows are cubic: a signal identity giving 1/L with cubic
  Gauss sums, or an automorphic object other than θ₃. If c = 3: θ ≈ 0.873917, and that is only the floor
  of the return box, so the true gain is larger [numerical].
- **T6 (D6), firing patterns.** Large-values estimates for the sextic family that use the structure of
  the set where the bank fires (higher moments of the bank's Gram matrix, Guth–Maynard style).
  Not yet priced.
- **T8 (D8), face region.** A consumer interface for asymmetric faces (D8a, no new analysis needed), then
  the continuum characterization of the method's limit, then properties of the true region.

## Exploitation candidates (for later)

These are ordered by expected Δθ against the 5e-5 bar.

1. **D8a, if Cauchy–Schwarz convexification holds.** The potential gain is large, so it must be checked hardest.
2. **D6, per-class combination with the joint count:** about −1.4e-5 alone; needs company.
3. **D5:** only if the discrete windows leave slack.
4. **D2 / D1:** each needs a new source theorem.
