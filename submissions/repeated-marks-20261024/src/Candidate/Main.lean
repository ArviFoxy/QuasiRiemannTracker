/- Repeated marks: the candidate bound 8747490/10^7.
The source step `nf_step2` (Source/NFStep2.lean) is the repeated-mark fork of Collet's NF step;
the seed step is Collet's (Record1252270103Source/Core/Endpoint.lean, Apache-2.0). -/
import Submissions.repeated_marks_20261024.Graph.Endpoint
import Submissions.repeated_marks_20261024.Source.NFStep2
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Endpoint

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8747490 / 10000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  apply QRH.RepeatedMarks.Graph.dirichlet_of_steps QRH.Record1252270103Source.Endpoint.seed_step
    QRH.RepeatedMarks.Source.nf_step2 χ s _ hpole
  convert hs using 1
  norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]

end Candidate
