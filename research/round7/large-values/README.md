# Round 7: large values for the sextic count (2026-10-25, negative)

Question: can a large-values argument (Halász–Montgomery, Huxley subdivision, Jutila/Heath-Brown
moments, Guth–Maynard) lower the HIGH count `R = 0.6037` (by 7.5e-5) or `ρ(0.5) = 7/12` (by 1.6e-3)
with the inputs the chain has (inverse moment I, long line L, plain fourth moment P)?

Answer: no. The LP reproduces the corner (t* = 1.1539, r* = 0.7435, m* = 0.4104; sensitivities
I 0.51, L 0.28, P 0.22 for R, and I 0.31, L 0.50, P 0.16 for ρ(0.5)).

| method | δ = 0.4546 | ν = 0.5 | obstruction |
|---|---|---|---|
| current mean values | 0.6037 | 0.5833 | |
| Halász–Montgomery (any witness, powers, copies `u·a⁶`) | no bound (best 1.091) | 1.000 | off-diagonals `Σ_{n~Y} ψ_u ψ̄_v(n)` are genuinely of size `Y^{1/2}` > `Y^δ` (thin family: rows of conductor U, quotients of conductor U²); copies `u·a⁶` give `|G| ≈ Y` |
| Huxley subdivision | ≥ 1 | ≥ 1 | best total `min_G U^{2(1−δ)} G^{2δ−1} = U` |
| Jutila / Heath-Brown / Hilbert–Schmidt | ≥ 1 | ≥ 1 | only for δ > 1/2 |
| moments of the large-value set | 0.6037 | 0.5833 | Chebyshev on I, P, L again (LP-tight) |
| Guth–Maynard (arXiv 2405.20552), available inputs | no bound | no bound | E2 only via the coset fourth moment of width 2; S3 only trivially |
| Guth–Maynard assuming (H1) width-1 coset fourth moment and (H2′) S3 cancellation by `Y^{0.136}` | 0.6037 (0.579 only via a saturated slot product) | 0.5769 | no mechanism found for (H2′) |
| any coefficient-free method on the L line | ≥ 0.629 | ≥ 0.625 | the L line is already below this density-hypothesis floor for t > 1 |

Poisson is an exact self-duality for the sextic family: `τ(ψ_u ψ̄_v) = c(u,v) τ(ψ_u) τ(ψ̄_v)`, so
`G_Y − Y·I = (Y/U)·D(C∘(G′_{U²/Y} − L·I))D*`. Root numbers cancel around every cycle; this is why
the Guth–Maynard triangle sum S3 gets no saving.

Numerics (`sextic_gram.py`, actual `(u/n)_6` over `Z[ω]`, U = 3000 and 8000): `E|G|²/Σw⁴ = 0.89–0.95`
(random-phase size), Halász ratio 0.9–1.2 growing like `Y^{1/2−δ}`, `S3/(R³Y) = 0.55–0.64` for random
row sets.

Status: proved for the Halász/Huxley/Jutila exponents and the self-duality; heuristic (absence of
mechanism) for S3. Files: `derivations.txt`, `lp_corner.py`, `gm_conditional.py`, `sextic_gram.py`.
