# Lean proofs (research mirror)

Mirrors of the packages built in the local Lean environment (`Submissions.<package>`, Lean 4.34.1 with the upstream
library). Each package's own files carry `#print axioms` lines. The packages listed with a θ depend only on
`propext`, `Classical.choice` and `Quot.sound`, with no `sorry`, `admit`, `axiom` or `native_decide`.

| package | what it proves | status |
|---|---|---|
| `arvi_selected_leaf/` | `beta_le_theta`: β ≤ 43670599/50000000 = **0.87341198** (selected-norm leaf, R1, the line to Λ = 401/200) | **merged upstream as PR #97** (e02df3d2) |
| `arvi_bank/` | `beta_le_theta`: β ≤ 43669114/50000000 = **0.87338228** (line to Λ = 2.0001, transport fork, return at h = 0.8097) | research bank, −2.97e-5 vs #97, below the 5e-5 PR rule; superseded by 1.4e-7 by upstream PR #98 (Bebel, 0.8733821435, open); see its README |
| `arvi_kwall/` | the selected norm's amplify–reflect rules cannot pass slope 1/2: below it they allow B^{7/6} at the balanced point, even starting from Θ₆ (`no_balanced_bound_below`) | research (barrier) |
| `arvi_rip/` | RIP foundation for the √-barrier program: Gershgorin certificate, the Welch bound, `coherence_order_barrier` (with N ≥ 2n unit columns, coherence certifies RIP only up to order 1 + δ√(2n)), `flat_rip_on` (BDFKK's flat RIP ⇒ RIP, fixed support, constant 32δ(T+1)²); finite Hoeffding with conditioning (`card_cond_le`); `exists_rip_sign_explicit`: random sign dictionaries have RIP of order k once 2(N+1)^{2k}e^{−δ²n/4} < 1, i.e. k ≈ δ²n/(8 log N), beyond √n | research (RIP program) |
| `arvi_primeface/` | D1 (direct prime-pool face): the quadratic Davenport–Hasse relation `chi_four_mul_jacobiSum_self` (χ(4)J(χ,χ) = J(χ,η)), `gaussSum_duplication` (χ(4)g(χ)g(χη) = g(χ²)g(η)), `sextic_duplication` (sextic Gauss sums at primes = conjugate cubic ones times a Hecke factor) | research (D1) |
| `arvi_density/` | marked density-split step at the floor q_f = 3/5, with return; earlier record 0.87387234 | merged upstream as PR #94 |
| `arvi_return_tuning/` | return retunings; `dirichlet_nonvanishing_f50` (0.87387234 family) | superseded |
| `arvi_ode_shape/` | the density chain as an ODE inequality (`ode_inequality_estimate`, `ode_shape_sources`) | research |
| `arvi_uniform_chain/` | facet inequalities for a uniform density chain (`facets_ge_facet12`) | research |
| `arvi_energy_region/` | the energy region as a least upper bound (`arviZone_isLUB`, `isEstimate_globalFace_iff`) | research |
| `arvi_face_region/` | Cauchy–Schwarz for weighted `tsum`s, face midpoints (`energy_sum_cs`, `midpoint_source`) | research |
| `arvi_newpowers/` | `no_cheaper_transfer` (rigidity of the sextic transfer); marked count at amplitude 0 = unmarked count | research |

Where each result sits in the research is recorded in `../journal/JOURNAL.md`. What the next bar needs is in
`../frontier/README.md`.
