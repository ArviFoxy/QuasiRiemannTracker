# Cubic amplifier route (task 150)

Question: can the sextic transfer (scale cost c = 6) be replaced by a cubic one (c = 3)?

## What is in Lean (checked)

- `sexticChar := cubicChar ^ 2 * quadraticCharO` (`openai-baseline .../GaussSum/FiniteFourier.lean`, def `sexticChar`).
- The probe's signal identity uses the row Gauss sums γ₁γ₂: `localGamma_one_two_full_signal`
  gives γ₁γ₂ = −(angular factor)·G (`Detector/SourcePrime.lean`). With cubic rows the product is
  `localGamma_two_four`: γ₂γ₄ = 1 (`Detector/PrimeConstants.lean`), so the row no longer carries 1/L.
- Two cubic-type transfer lemmas, `CubicTransfer.lean` (scratch namespace, builds against
  `arvi_newpowers.Rigidity`; axioms propext, Classical.choice, Quot.sound; rebuilt and checked):
  - `cubic_dilation_leaves_quadratic`: g(Dn,h) = χ_D(n)³·g(D,h)·g(n,Dh). Dilating by D¹ leaves the
    quadratic twist (n/D)₂ in the residual coefficients, so this is a twisted type.
  - `squared_residual_transfer`: g(D²m², DH) = g(D²,DH)·g(m²,H). There is no dilation, but the residual
    columns must be squares.

## What is derived or numerical only (not proven)

- The claim that only row exponent j ≡ 1 (mod 6) gives the signal identity. This was checked numerically
  (`cubic_checks.py`, all identities pass) but not proved in general.
- The claim that no higher-order explicit theta series exists (Kazhdan–Patterson). It was taken from
  `LOG.md` and not checked.
- Ledger prices (`price_cubic.py`, R2 toolchain copy):
  - c = 3 in every step gives θ = 0.873916667. That is the floor of the return box, so the true
    gain may be larger and could not be priced.
  - A 1.38 % cubic share is about at the 5e-5 bar.
- The verdict "no cubic amplifier inside this framework" is the agent's audit result, not a theorem.
  Not finding a route does not show that none exists.

`price_cubic.py` expects a copy of `research/newpowers/r2` in `r2copy/` beside it.
