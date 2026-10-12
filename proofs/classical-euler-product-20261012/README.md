# Classical Euler-product bound

The exact bound is **1/1**, with decimal approximation **1.0**.

[`Solution.lean`](Solution.lean) proves two declarations:

- `QRH.canonical_bound`: for every positive modulus and complex Dirichlet
  character, the analytically continued L-function is nonzero when
  `1 < re s`. Its signature retains the tracker's pole-exception argument.
  The half-plane hypothesis already excludes the pole.
- `QRH.zeta_bound`: the Riemann zeta function is nonzero when `1 < re s`.

The all-Dirichlet proof identifies the continued L-function with its convergent
series and applies Mathlib's classical nonvanishing theorem. The zeta proof
applies Mathlib's corresponding theorem directly. The package's verification
scope is these two declarations.

[`Challenge.lean`](Challenge.lean) independently states the two target types
for a separate Comparator challenge environment. Both modules contain explicit
proofs from Mathlib. Each module is compiled in its own environment because
they use the same declaration names.

The dependency pins are Lean **4.34.1**, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The exact upstream results are
[`DirichletCharacter.LSeries_ne_zero_of_one_lt_re`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/LSeries/Dirichlet.lean#L228),
[`DirichletCharacter.LFunction_eq_LSeries`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L75),
and
[`riemannZeta_ne_zero_of_one_lt_re`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/LSeries/Dirichlet.lean#L326).

The captured [Solution audit](evidence/Solution.log) and
[Challenge audit](evidence/Challenge.log) record successful compilation with
cached Mathlib dependencies. Every audited declaration uses the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The
[validation metadata](evidence/cached-lean-validation.json) records source
hashes and the scope of this preliminary check. Independent dependency replay,
Comparator statement comparison and the NanoDa/con-ron checks remain the
admission verification work.

To build using the pinned package configuration:

```sh
cd /path/to/classical-euler-product-20261012
lake update
lake exe cache get
lake build Solution Challenge
lake env lean Solution.lean
lake env lean Challenge.lean
```

The historical catalogue entry preserves its 1922 bibliographic date anchor.
This package was prepared on 12 October 2026 and formalizes the classical
theorem at the stated scope. Attribution and licensing appear in
[NOTICE.md](NOTICE.md) and [LICENSE](LICENSE).
