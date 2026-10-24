# Research log

Goal: lower θ in "every Dirichlet L-function is nonvanishing on Re s > θ" by at least 1e-5 against
the best upstream PR (smaller gains count only if they simplify or clarify the proof).

| reference | θ | note |
|---|---|---|
| upstream PR #70 (Mark Lewko), best upstream PR | 0.874772906 | checked 2026-10-24 |
| this branch, Lean (`submissions/repeated-marks-20261024`) | 0.8747289 | 4.4e-5 below PR #70 |
| next milestone (1e-5 below this branch) | ≤ 0.8747189 | |

Conventions: `θ*` values are exact-return evaluations (rational certificates) unless marked "float".
Each entry records the idea, the measured effect, and where the artifacts are. Negative results are
kept on purpose.

---

## 2026-10-23

**1. Proof analysis (PR #69, Collet).** Read the paper and Lean. All estimates are ℓ² bounds for
character evaluation maps over K = Q(√-3), closed by Poisson/Gauss sums, cubic-theta reflection,
recursion, sixth-power amplification and the zero detector. The final count is the weighted mean of
three witness lines (inverse I, plain P, long L; weights 0.505/0.193/0.303).

**2. Doubled marks in the source HIGH count.** The HIGH inverse witness may use each marked slot
twice (foundations Lemma 8.1 already allows repeated lists). New 59-face graph, exact certificate:
θ = 0.8747514. → `doubled-marks/`. Superseded by 3.

## 2026-10-24

**3. Repeated marks (K copies), per-class cutoff, Lemma C, Lemma D.** θ = 0.8747289, formalized in
Lean (`Candidate.bound`, standard axioms only). → `repeated-marks/`,
`submissions/repeated-marks-20261024/`.
- Lemma A_K: slots repeated K times in the inverse witness.
- Lemma B_K: one detector cutoff per amplitude class.
- Lemma C: payment for any monotone min-of-facets gain with `G ≤ νS` (replaces HF12).
- Lemma D: the physical face applied through its global source theorem at every shift.

**4. Lemma E (amplitude split of LOW/HIGH): REFUTED.** Erasing low-amplitude HIGH rows as LOW rows
needs zero-free slot bounds uniformly in real power and height (`ActualLow`); amplitude at the
detected zero says nothing at other heights. All gains from it were void.

**5. Lemma F (cap induction): valid, below the bar.** A node can be its own LOW parent at a smaller
cap. Consolidated with finer pivots and a HIGH density floor 0.45: θ* = 0.8747257 (−3.2e-6).
→ `cap-induction/`, `lean-lab/LemmaF.lean`.

**6. Lever map.** Sensitivities at the binding point (d = h, δ ≈ 0.4546, p = 1/2):
- dθ/dB_C ≈ −4.0e-3 and dθ/dB_P ≈ −6.7e-3 (face heights);
- per 1e-3 of line exponent: I 6.7e-5, L 4.0e-5, P 2.6e-5;
- dθ/dR ≈ 0.133.

The four binding exponents:
- MI slot cost 2;
- sextic amplifier exchange 6;
- long slope (1+5r)/6;
- plain slot cost 6κ.

A catalogue cross-check (21.9k records) found nothing that moves them. → `cap-induction/README.md` §4.

**7. Re-derivation of the binding structure (this session).**
- *Coupled hybrid norm (new lemma, proved abstractly).*
  - Mechanism: the active slot product's Gauss-sum coefficient is twisted-multiplicative. A balanced
    split of the slots gives a bilinear form with a cubic-symbol kernel. Heath-Brown's cubic sieve
    then removes the `L` term of MF2.29, giving `u'_h = min(z, (v+z)/3) ≥ u_h`.
  - Result: no θ gain. In the MI's binding child the row branch has slack (exponent `F_c/2` at
    `v = 0`, `F_c − 3z/2` at `v = H`). Only the column branch binds, and it is exactly
    `T_d ≤ F_c ⟺ r + 2z ≤ m`.
  - Conclusion: the slot cost 2 is the slot primes entering the second reflection's conductor
    squared. → `lean-lab/MIBranches.lean`, `lean-lab/CoupledHybrid.lean`.
- *Numerator glue (14.7), Hölder vs pointwise.*
  - Replacing the fourth-moment Hölder bound by the pointwise bound `|S'| ≪ U^{δλ/2}` for class rows
    (zeros ≤ a + 2e) gives E-contribution `dR + δℓ = 0.56093` against Hölder's
    `d/4 + 3dR/4 − δpC/2 = 0.56026` at the binding point.
  - Interpolating (`|N|^k ≤ max^{k−4}|N|⁴`) is affine in 4/k, so the optimum is an endpoint.
  - Result: Hölder is optimal by 6.7e-4 in E. No gain.
- *Plain sixth moment / higher Hölder.* Unavailable: the reflected length λ = 2ℓ/h = 0.4186 has
  3λ > 1.
- *Halász–Montgomery / Huxley large values.* Useless here: the witness threshold U^{δr} is below the
  Pólya–Vinogradov off-diagonal U, and the mean-square off-diagonal gives U^{1+r/2−δr} > U.
- *Heath-Brown/Vaughan decomposition of the long Möbius witness.* Pure Möbius pieces are short and
  weak. Mixed pieces (μ*1) are not canonical (the canonical energy forbids extra n-coefficients),
  and Möbius×slot pieces raise the amplification cost (marks cost 5/3 > 2δp in the long branch).
  No gain.

## Open directions (ranked)

1. **Column branch of MI / long Möbius moment beyond amplification.** Both need cancellation in sums
   of cubic Gauss sums twisted by quadratic characters (Type II bilinear structure as in
   Dunn–Radziwiłł's proof of Patterson's conjecture). A power saving of 2.5e-4 at r = 1.155 in the
   long Möbius moment would already give 1e-5.
2. **Joint same-zero witness moments** (catalogue G137, OPEN).
3. **Sparse-image large sieve for the long branch.**
