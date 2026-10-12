# Classical theta-one proof notice

These short wrappers were prepared for QuasiRiemannTracker PR #5 with AI
assistance on 12 October 2026. They apply established Mathlib theorems and are
distributed under Apache-2.0; see [LICENSE](LICENSE).

The imported Mathlib development is pinned to commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

- `Mathlib/NumberTheory/LSeries/Dirichlet.lean`: copyright 2024 Michael Stoll;
  author Michael Stoll. This supplies the Dirichlet-series and Riemann-zeta
  nonvanishing theorems in the half-plane `1 < re s`.
- `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`: copyright 2024
  David Loeffler; authors David Loeffler and Michael Stoll. This identifies the
  analytically continued Dirichlet L-function with its convergent series.

Mathlib's imported dependencies retain their original notices and licenses.
The historical catalogue entry separately credits its bibliographic date
anchor. These wrappers express the classical Euler-product bound.
