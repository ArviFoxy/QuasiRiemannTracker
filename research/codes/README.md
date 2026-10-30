# Codes and radar sequences (D7)

- `radar_sequences.md`: treatise, with evidence tags [T]/[D]/[F]/[O]/[U] (an agent, task 154).
- `sources.md`: 70 sources, each marked with how much of it was read.

## Lead's verification (2026-10-29)

Spot-checked against publisher and arXiv records:
- [BY10] Baier–Young, *Mean values with cubic characters*, JNT 130 (2010), arXiv:0804.2233. Thm 1.5
  extends the cubic large sieve to sextic characters; Gao–Zhao cite it the same way.
- [DR24] Dunn–Radziwiłł, *Bias in cubic Gauss sums: Patterson's conjecture*, Ann. of Math. 200(3)
  (2024). Under GRH the cubic large sieve is sharp up to X^{o(1)}.
- [Ka13] Katz, *Asymptotic L⁴ norm of polynomials derived from characters*, Pacific J. Math. (2013),
  arXiv:1205.1069.

The theorem numbers in the other entries were not re-checked.

## Cross-pollination with the proof (lead, ideas only)

1. **Outer limit of the true face region (D8c).**
   - Welch's k-th moment bound, Σ|⟨x_i,x_j⟩|^{2k} ≥ M²/C(N+k−1,k), is a *lower* bound on Gram moments.
   - Applied to the row family, it could prove that no face beats a certain line.
   - That would make the outer half of the region rigorous.
2. **Large values beyond pairwise coherence (T6).**
   - Explicit RIP matrices beyond the √N barrier [BDFKK11] use additive structure of the large-value set.
   - Guth–Maynard large values do the same for Dirichlet polynomials.
   - The firing-pattern direction is that idea applied to the sextic bank.
3. **Ceiling for T1.** [DR24]: the (AB)^{2/3} term of the cubic large sieve cannot be removed in general,
   because of the Kummer bias. A twisted-transfer sieve has to use the transfer structure, not a generic
   sieve improvement.
4. **Mismatched filter = dual frame.** The sidelobe-free filter uses the Gram inverse, at a cost set by the
   lower frame bound. In our language this means amplifier or mollifier weights chosen by the Gram inverse
   (Selberg-type) instead of fixed Möbius weights.
