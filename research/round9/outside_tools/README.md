# Round 9, outside-tools agent

The full report is `NOTES.md`. Summary:
- **P1 localized to large primes, modulo a frame bound.** Split the columns by their largest
  prime factor `π`, so that `c(πm) = g̃(π)e_π(m)`.
  - On the columns with `N(π) ≤ K`, the column branch is the diagonal times a frame constant `F`.
    This holds for any unimodular block multipliers in place of `g̃(π)`, with the cofactor data
    `e_π` fixed (rigorous).
  - This is not the same as changing `g̃` at the prime `π`, since primes `≤ K` also divide
    cofactors of larger blocks.
  - Numerically `F` is at Marchenko–Pastur, and random cofactor data gives the same value.
  - A bound `F ≤ N^{o(1)}` (Lemma BG) is unproved. It is a non-alignment property of the
    cofactor data, which still contain `g̃` at primes `≤ K`.
- **The hard core carries the difficulty.** These are the columns with a prime factor of norm
  `> K`, and every adversary found lives there.
  - P1 ⟸ BG + HC.
  - Given BG, HC ⟺ P1.
  - The Vaughan route to HC returns `c` itself in its `d = 1` Type I term.
- **ω-witnesses do not help.** Möbius blocks weighted by prime factors in a band have
  density-hypothesis mean values, but the lattice adversary defeats them through a scale shift.
- Short closures: SDP combinations of witnesses, slot spikiness, exchange rate 6, higher-rank theta.

Synthesis: `../README.md` §5.
