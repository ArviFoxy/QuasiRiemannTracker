import Submissions.arvi_density.Return.Endpoint
import Submissions.density_split_fine_chain.Theorem

/-! Test of the baseline `Submissions.arvi_density.Return` (research/density/gen_return86.py, PR 86's constants,
two-source endpoint): the endpoint `dirichlet_of_sources`, fed by PR 86's chain for both faces, has literally the
statement of PR 86's `K15.dirichlet_nonvanishing`; `#print axioms` shows only the standard axioms. -/
set_option autoImplicit false

/-- The two-source endpoint, with the count source and the physical source both PR 86's final face. -/
theorem arvi_return_test {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369779 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.Return.dirichlet_of_sources (fun hβ => QRH.SilDensitySplit.K15.final_source hβ)
    (fun hβ => QRH.SilDensitySplit.K15.final_source hβ) χ hs hpole

example : type_of% @QRH.SilDensitySplit.K15.dirichlet_nonvanishing := @arvi_return_test

#check @QRH.ArviDensity.Return.dirichlet_of_sources
#check @QRH.ArviDensity.Return.beta_le_theta_of_sources
#print axioms arvi_return_test
#print axioms QRH.ArviDensity.Return.dirichlet_of_sources
#print axioms QRH.ArviDensity.Return.beta_le_theta_of_sources
