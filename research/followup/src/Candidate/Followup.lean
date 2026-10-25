/- Follow-up of the repeated-mark submission, single stage: the natural cost is `K = 9/2`, whose cap
is the baseline's `β ≤ 7/8`, so Collet's seed step, intermediate return and bootstrap stage are not
used. The face family and the final return are regenerated for `K = 9/2`; the final return closes at
2186813/2500000 = 0.8747252 (`bound_sharp`). -/
import Submissions.arvi_followup.Graph.Endpoint
import Submissions.arvi_followup.Source.NFStep2

set_option autoImplicit false

namespace CandidateFollowup

/-- The value the proof reaches: 2186813/2500000 = 0.8747252. -/
theorem bound_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2186813 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  apply QRH.RepeatedMarks.Graph.dirichlet_of_step QRH.RepeatedMarks.Source.nf_step2 χ s _ hpole
  convert hs using 1
  norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8747289 / 10000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  bound_sharp χ (lt_trans (by norm_num) hs) hpole

end CandidateFollowup
