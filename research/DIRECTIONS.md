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
| D1 | Twisted transfers (lemma T: a source theorem uniform over twist conductors) | agent running (task 149) | Rigidity: twist-free transfers have c ≡ 0 mod 6 [Lean `no_cheaper_transfer_general`]; R2 ledger for twisted types [derived] | verify the agent report; decide whether lemma T is plausible |
| D2 | Squared-prime slots (doubled blocks, e = 2) | agent running (task 151) | identities [Lean `square_row`, `square_twist`, `collision_family_energy_div`]; e = 2 [derived] | find a source of squared slots; return accounting |
| D3 | Cubic amplifier (c = 3) | explored (task 150) | signal identity needs γ₁γ₂ [Lean `localGamma_one_two_full_signal`], cubic rows give γ₂γ₄ = 1 [Lean]; no cubic route found in this framework [audit only, not a proof]; θ ≈ 0.873917 if c = 3 existed [numerical] | parked; revisit only with a new detector |
| D4 | Classify sextic identities (geometry, Stickelberger, rigidity) | explored (task 147) | rigidity for every block Dᵐ and dilation [Lean, `arvi_newpowers/Rigidity.lean`]; local Stickelberger completeness [numerical]; geometric origin notes | feeds D1 (only twisted or new-room identities remain) |
| D5 | Continuous tuning of the return (per-patch detector, fewer certificates) | agent running (task 152) | return = 31 windows × 6 fixed branches, ~715 KB of admission certificates | slack in θ; size of a parametric certificate |
| D6 | Firing patterns / multilinear bank (higher moments, joint counts, Guth–Maynard-type structure) | idea | the existing pieces are multilinear: slot products, repeated marks, PR 93 joint count | first: per-class combination with the joint count (task 145, about −1.4e-5 [numerical]) |
| D7 | Codes and radar sequences (cross-field mechanisms) | agent running (task 154) | the sextic symbol is a power-residue sequence; Gauss sums are its spectrum; energy bounds are Welch-type bounds | read the knowledge base; map mechanisms to the proof |
| D8 | **Face region (long-standing goal):** define the true region of valid energy bounds and characterize it analytically, so the face iteration becomes unnecessary | started | faces are the supporting lines of a convex boundary curve, (Λ, B) is its Legendre transform, s₀ = dB/dΛ rises 0.0278 → 0.0834 [numerical, from the 130 faces]; a convex hull would add up to +0.011 plain length at s ≈ 0.05 [numerical, *valid only if Cauchy–Schwarz interpolation applies*] | D8a below |
| D8a | Cauchy–Schwarz convexification: (m₁, m₂, s_A + s_B) is proven when (m₁, m₁, 2s_A) and (m₂, m₂, 2s_B) are | **step checked, valid**; routing open; agent running | energy = Σ_z [keep z]·Re Φ(‖z‖²/K)·|W₁·W₂·∏ slots|²/(X₁X₂∏P) with Re Φ ≥ 0 [Lean `CenteredMomentInductionEnergy.energy`, `positive_squared_absolute`]; squared configurations are legal inputs (any profile pair, any finite slot type, duplicated pools); `Profiles.control` = c(W₁)·c(W₂), so controls combine exactly [Lean `FiniteProfileExceptionalPair.lean:18`]. The gain exists only for unbalanced plain pairs (one plain long and slot-free, the other short with all slots); for two equal plains it reproduces E(s) [derived]. The return consumes symmetric faces (`broadFace B Λ cap` = ⟨B, Λ, 0, ½, 0, cap⟩) [Lean `Return/WindowSources.lean`] | find where the return/steps use unbalanced plains; design an asymmetric face interface; price θ |
| D8b | Continuum ODE of the density chain; a faceless density chain | idea | done for the older source chain (`chain-ode/`, `faceless-chain/`: 59 nodes → 5 cubic pieces) [notes; partly Lean in that PR] | derive for the marked density chain |
| D8c | Properties of the true region: monotone, convex balanced slice, the ideal line P + s ≤ 1 | idea | heuristics [derived] | state precisely; prove what can be proven |
| D9 | Density floor below 1/2 | explored (task 144) | see `replan/floor.md` | revisit together with D6 |
| D10 | Visual explainer | done (task 153) | `explainers/sextic-filter-bank/` | update as directions mature |
| D11 | Mine upstream formal libraries for unused theorems | in progress (task 86) | | continue in the background |
| D12 | Mechanism catalogue for the top knobs (conductors, moments, tensor bounds) | pending (task 100) | | merge with D7 output |

## Exploitation candidates (for later)

These are ordered by expected Δθ against the 5e-5 bar.

1. **D8a, if Cauchy–Schwarz convexification holds.** The potential gain is large, so it must be checked hardest.
2. **D6, per-class combination with the joint count:** about −1.4e-5 alone; needs company.
3. **D5:** only if the discrete windows leave slack.
4. **D2 / D1:** each needs a new source theorem.
