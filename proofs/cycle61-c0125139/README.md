# A zero-free half-plane with boundary 874861/1000000

Hailey Collet · HaileyCollet@gmail.com · Apache-2.0

The theorem gives **Re(s) > 874861/1000000 = 0.874861**, or **c = 0.125139**. It applies to every complex Dirichlet character of nonzero modulus, except for the principal pole at s = 1. The accompanying formalization also covers the Riemann zeta function and the stated finite-order Hecke family over the Eisenstein field. The boundary is strict.

Read the [paper](manuscript/paper.pdf), [TeX](manuscript/paper.tex), or [Markdown](manuscript/paper.md). The manuscript follows the final Lean construction, including its source normalization, choice order and complete error estimate.

The tracker entry is [`Candidate.bound`](../../submissions/cycle61-c0125139/src/Candidate/Main.lean). The candidate bundles contain only the local source closure required for this proof. [The original source archive](original-sources.tar.gz) preserves the 772 unbundled local modules; [the source manifest](source-manifest.json) records those modules and the 2,923 protected OpenAI imports. The latter come from the tracker's pinned dependency environment, rather than being redistributed in the candidate namespace.

The proof combines the earlier moment and source architecture with Gao's local refinement, extends the required density range, and supplies one common probe for the final zero-exclusion argument. Its final theorem has no unproved analytic-estimate premise. The earlier 4/33 and quartic endpoint theorems are not premises of this new bound.

The [exact arithmetic check](arithmetic/README.md) reconstructs 47 scalar checks and 156 Bernstein coefficients from the retained fixed-hash receipt.

The [packaging check](packaging/README.md) reconstructs every submitted bundle from the archived original sources and recorded transformations. It checks byte identity separately from Lean proof verification.

See [verification and reproduction](Verification.md) for the exact evidence level and [authorship and source attribution](PROVENANCE.md) for the mathematical and AI contributions. Original notices are retained under [licenses](licenses/).
