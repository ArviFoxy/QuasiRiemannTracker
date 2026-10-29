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
| D1 | Twisted transfers | **open: needs new math**; agent interim done (task 156, `twisted/new-math/`) | existing Lean prices the type at 0 [Lean]. In the dual variable (Poisson in h) the cubic twist disappears: the energy becomes Σ_j \|Γ(j)\|²\|A(j)\|², i.e. the D-block acts as an ordinary slot [derived; structure of the Fourier identity checked by the lead]. So a twisted transfer probably only re-books the live slot that faces already use (the agent's own circularity flag). What would remain new is a non-concentration estimate M_e: residual mass may not sit on the exceptional rows of a prime slot [conjecture]. That is the same kind of estimate as T6 | compare the twisted ledger (1, 2, 1) with the slot ledger (MF3.71–3.72) before any further work |
| D2 | Squared-prime slots (doubled blocks, e = 2) | **open: needs new math** (agent report done) | the count keeps only slots with pointwise lower bounds on counted rows [Lean `select_physical_product`]; a squared slot is the prime slot of φ_u², so the zero does not force it: by Jensen/3-4-1 a first-harmonic alignment a forces the squares only if a > 1/√2, but here a ≈ P^{β−1} ≪ 1 [derived]; even if granted, the net is −3e-6 to −9e-6 under the carrying costs (−3.3e-5 on the chain alone at a 5 % share) [numerical] | a mechanism making doubled slots visible to the zero (e.g. p² marks on the signal side), plus a source of P² pools; low priority given the payoff |
| D3 | Cubic amplifier (c = 3) | **open: needs new math** (a new detector) | in this framework the signal identity needs γ₁γ₂ and cubic rows give γ₂γ₄ = 1 [Lean]; scratch cubic-transfer lemmas build [Lean] | see New-math targets T3 |
| D4 | Classify sextic identities (geometry, Stickelberger, rigidity) | explored (task 147) | rigidity for every block Dᵐ and dilation [Lean, `arvi_newpowers/Rigidity.lean`]; local Stickelberger completeness [numerical]; geometric origin notes | feeds D1 (only twisted or new-room identities remain) |
| D5 | Continuous tuning of the return | **done** (task 152, `return-tuning/`) | no θ slack: the best this return can certify is in (0.873872338, 0.87387234] [derived, exact rationals]. It binds at newTop, p = 1/2, δ* = 0.44879, branch C, with every guard slack. The reflective redesign builds: `dirichlet_nonvanishing_f50` has the same statement (`rfl`) and standard axioms, and the lead rebuilt it [Lean]. Certificates shrink 796 KB → 45 KB and 1067 → 94 CPU-s | adopt in the next submission; the same technique applies to the density chain (D8b) |
| D6 | Firing patterns / multilinear bank (higher moments, joint counts, Guth–Maynard-type structure) | idea | the existing pieces are multilinear: slot products, repeated marks, PR 93 joint count | first: per-class combination with the joint count (task 145, about −1.4e-5 [numerical]) |
| D7 | Codes and radar sequences | **knowledge base done** (task 154, `codes/`) | 70 sources; the lead spot-checked [BY10] Thm 1.5 (sextic large sieve), [DR24] (Annals 2024, cubic large sieve sharp under GRH) and [Ka13]. Cross-pollination [idea]: (i) Welch k-th moment lower bounds give a rigorous *outer* limit for the true face region (D8c); (ii) RIP beyond √N via additive combinatorics [BDFKK11] is the coding-theory cousin of Guth–Maynard large values (T6); (iii) [DR24]'s Kummer bias caps what a generic cubic large sieve can give T1; (iv) mismatched filter = dual frame, i.e. amplifier weights from the Gram inverse (Selberg-type) | pick (i) or (ii) to pursue |
| D8 | **Arvi Zone (long-standing goal):** the optimal energy region (where the energy bounds truly hold). Characterize it, and prove energy region estimates without face iteration | ODE estimate solved exactly; vocabulary in `face-region/CONTINUUM.md` §6 | inner estimates: chain ⊂ ODE estimate ⊂ Arvi Zone ⊆ outer limit [derived]; the ODE estimate is the method's limit and has an exact solution | D8b uniform proof; D8c outer limit; D8d curve iteration |
| D8a | Cauchy–Schwarz convexification | **rule proved in Lean; the current proof gains 0; needs new math** | `arvi_face_region/Midpoint.lean`: `energy_sum_cs`, `midpoint_source`, `balanced_no_gain` (standard axioms only, rebuilt by the lead) [Lean]; every face evaluation (count, numerator, density steps) binds at equal plain lengths [Lean file:line in `face-region/README.md`]; the count witness certifies one plain block per row, and the numerator is one packet to the 4th power [Lean] | T8′: two different numerator packets per row, which would let the numerator bind unbalanced: up to −6.3e-5 if numeratorCap can also be raised to 63/1000, −6.4e-6 if not [numerical, hypothetical] |
| D8b | ODE energy region estimate as one uniform proof | **solved analytically; Lean in progress** (`face-region/CONTINUUM.md`, `UNIFORM_STEP.md`) | the slope is σ = (B − κ)/(Λ − κ) with κ(q) = 4(5−3q)/(25−18q), equal to `ode2` to 2e-14. Faces pursue the scaled ideal face (κ, κ). The envelope is E(s) = κ(q(s))(1 − s). Exact solution: 1/(Λ − B) − 𝒢(B/Λ) = const, with 𝒢 elementary. The floor face is in closed form [derived; checked numerically]. On the chain region, `high_marked` reduces exactly to one function of v (reductions P, N) [numerical, about 2·10⁵ samples] | stage 1 of the uniform-proof plan: one-variable gates → scalar conditions; then P/N as lemmas |
| D8c | Properties of the true region: monotone, convex balanced slice, the ideal line P + s ≤ 1 | idea | heuristics [derived] | state precisely; prove what can be proven |
| D8d | Curve iteration (Arvi): iterate convex energy region estimates instead of single faces | idea, needs new math | the step's density loss is the child's excess over its parent: h·v for a single face, but second order for a convex parent curve; a model estimate gives about 20 iterates instead of about 1300 for the same accuracy, with the same limit [derived, rough] | generalize Sil's density step to a family of parent faces |
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
