# New amplifier types and their combinations (research direction, 2026-10-28)

**Question (Arvi).** The source steps use two amplifiers: Collet's pool (`g(u, p⁶h) = 1_{p∤u}·g(u, h)`,
cost 6 per unit) and Sil's transfer (`g(a, D⁴k) = χ_a(D)²·g(a, k)`, a reciprocity twist absorbed as a
dilation; cost 4 + 2 per unit, Lean: PR 76 `FourthPower/GaussTransfer.lean`). Together they beat either
alone (descent `Λ > 6qB/(1+q)` instead of `6qB`), because the transfer acts on the input's own slots.
Find more amplifier types — other dilation exponents, block multiplicities and twists — and combine
them, in the source steps and in the return.

**Rule.** Only Lean theorems count as established. Every claim from earlier notes in `research/` is a
hypothesis to re-derive and check.

**First observations (derivations, not Lean-checked).**
- CRT: `g(B·n, k) = χ_B(n)·χ_n(B)·g(B, k)·g(n, k)`; with reciprocity the residual's twist is `χ_n(B)²`
  up to a sign.
- Simple block `B = D`: twist `χ_n(D)² = (D/n)₃²`; the dilation `D^k` gives `χ_n(D)^{-k}`, so the
  cubic part needs `k ≡ 1 (mod 3)`: `k = 4` exact (Sil), `k = 1` leaves the quadratic twist `(D/n)₂`.
- Squared block `B = D²`: twist `χ_n(D)⁴ = (D/n)₃`, absorbed exactly by `D²`:
  `g(D²n, h) = g(D², h)·g(n, D²h)`. The character mod `D²` is imprimitive, so `g(D², h) = 0` unless
  `D | h`, with normalized size `≈ N(D)^{1/2}` there.

**Agents (reports in this folder).** `R1_algebra.md`: classification and numerical verification of the
identities over ℤ[ω]. `R2_ledger.md`: savings, costs and the combination law, priced on PR 83's
steps. `R3_return.md`: amplifier mixtures in the final return.
