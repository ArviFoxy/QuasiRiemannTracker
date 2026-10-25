# Round 9, outside-tools agent

The full report is `NOTES.md`. Summary:
- **P1 localized to large primes.** Split the columns by their largest prime factor `π`. On the
  columns with `N(π) ≤ K`, the column branch is the diagonal times a frame constant `F`, for any
  values of the Gauss sums at the block primes (rigorous). Numerically `F` is at
  Marchenko–Pastur.
- **The hard core carries the difficulty.** These are the columns with a prime factor of norm
  `> K`. By Vaughan's identity it is P1 modulo the frame bound.
- **ω-witnesses do not help.** Möbius blocks weighted by prime factors in a band have
  density-hypothesis mean values, but the lattice adversary defeats them through a scale shift.
- Short closures: SDP combinations of witnesses, slot spikiness, exchange rate 6, higher-rank theta.

Synthesis: `../README.md` §5.
