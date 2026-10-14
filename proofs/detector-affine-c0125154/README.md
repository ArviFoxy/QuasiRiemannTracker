# A zero-free half-plane with boundary 437423/500000

The theorem gives **Re(s) > 437423/500000 = 0.874846**, i.e. **c = 0.125154**. Like Cycle61, it covers every complex Dirichlet character of nonzero modulus (the principal pole at s = 1 excluded), the Riemann zeta function, and the finite-order Hecke family over the Eisenstein field. The boundary is strict.

The improvement over [Cycle61](../cycle61-c0125139/README.md) (874861/1000000) comes from one change. Cycle61's initial affine moment (Theorem 2.2) is used inside the detector count, where Cycle61 had used only the κ-marked plain moment. For plain lengths m ∈ [0.4137, 0.4235], the marked capacity (1 − 2m)/(6κ) becomes (B − 2m)/Λ. On the critical region δ ∈ [0.445, 0.485], p ∈ [0.495, 0.5] this lowers the count exponent from Cycle25's `countingR κ*` to a κ-independent closed form `R_New`. That frees the new-h row, and the endpoint moves to θ = 437423/500000 with h = 15903/20000.

* [Mathematical notes](manuscript/notes.md): the new count, case analysis, region, moment supply.
* [Exact arithmetic](arithmetic/README.md): every scalar check and Bernstein certificate, cross-checked character for character against the Lean source.
* [Verification](Verification.md): what was compiled locally, and how.
* [Provenance](PROVENANCE.md) and [notice](NOTICE.md).

The tracker entry is [`Candidate.bound`](../../submissions/detector-affine-c0125154/src/Candidate/Main.lean).
