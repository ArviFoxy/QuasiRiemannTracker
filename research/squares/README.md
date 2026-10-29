# squares/ — scratch for the squared-prime-source study (not a report; the report is the hand-back message)

* `dchain.py` — T-A floor-1/2 marked chain (`ta/chain2.py`, K = 8 Lean gain) with R2's generalised ledger:
  `share PHI` ((e,c,r) = (1+PHI,6,1)), `cap UD` (first UD of each step's selection doubled, R2 `dchain_cap.py`),
  `capR UD` (as cap, plus retained doubled slots priced at the natural bound kappa_I at HIGH rows),
  `capRN UD` (capR plus R2 s2.3(f)'s native penalty 2(1-rho) per carried doubled unit), `cap2 UD` (doubled units counted
  by norm in the face: r = 2 per doubled unit).
  dens capped at 3/4 - 2e-6 (R2 convention). PHI = 0 reproduces T-A's chain exactly (checked, 3 steps identical).
* `price.py` — exact return (T-A `ta/exact.py`, six branches, ell < 0.18) with role split; optional return-side
  carrying cost B_k -> B_k - LAM * L_k * X_k (X_k = doubled volume consumed by steps 0..k); 5th arg = chain
  supplying a cost-free physical face. Base chain reproduces the record 0.873872341.
* `dB.py` — face gain vs base chain at equal L against LAM*L*X.
* `chains/`, `logs/price.log`, `logs/chains.log` — outputs.
* `summarize.py` — table of `logs/price.log` (all exact-return prices of this study).
