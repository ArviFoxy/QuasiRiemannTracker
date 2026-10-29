# Sextic Filter Bank (visual explainer)

`sextic-filter-bank.html` is the source of the published page. It covers:
- the hexagonal lattice and its tori;
- plane waves and the sextic code;
- Gauss sums as DFTs (phasor walk and flat spectrum);
- the CRT / Good–Thomas layout with a live check of g(Dn,h) = ±g(D,h)·g(n,D⁴h);
- the D⁴ dilation geometry and the squared-prime comb;
- the Gram matrix of 26 atoms;
- the 130 chain faces: primal lines with their envelope, a one-step magnifier, faces as points (Λ, B)
  with the q-fan, and the q band per step.

`math.js` and `test.js` hold the same arithmetic as plain node code. `node test.js` checks:
- the flat spectrum and dilation rule (1352 cases);
- the transfer identity (144 cases, ε = ±1);
- the D² comb (360 cases).

`chain_data.json` holds the faces and the per-step q(v) range, from `research/chain/steps_f050_dL200.json`
and `dens` in `Source/HybridGates.lean`.
