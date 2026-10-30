# RIP program: the square-root barrier for the sextic dictionary (numerics and closures)

Formal side: `../lean/arvi_rip/` (Gershgorin/Welch barrier, flat RIP ⇒ RIP). Journal: "RIP program (1)", "(2)".

| script | what it checks |
|---|---|
| `closure4.py` | K-wall closure with the trivial Frobenius rule added: n(1) stays 7/6. |
| `closure_dr.py` | Closure with a corrected initial bound. Diagonal up to x = 3/5 (Dunn–Radziwiłł range) leaves the closure unchanged. The diluted bound max(1, x, Θ₆(x) − δ) gives the fixed point. |
| `zomega.py` | Sextic residue symbols (x/π)₆ over Z[ω], for split and inert primes. Checked: multiplicativity and uniform value distribution. |
| `zfamily.py` | Rows: squarefree ideals of norm in [B, 2B] coprime to 6. Sources: primary elements of squarefree norm ≤ L. Reports top eigenvalues of the row Gram matrix on the full family, on random thin W, on large-value sets of a short prime (slot) polynomial, and on sets aligned with the top eigenvector. |
| `mp_check.py` | Compares those eigenvalues with the Marchenko–Pastur edge (1 + √(\|W\|/S))². |

Run: `python3 -I zfamily.py B L P0` (B = 3000 takes a few minutes).
