/- The candidate bound 34971/40000 = 0.874275.
The source chain starts on Sil's fourth-power face (PR 74, through PR 76's `Graph/Start.lean`), runs
through the fan (`Fan/Steps.lean`) and the mixed face family (`Family/`, `Graph/MixedChain.lean`) to the
count face and the physical face; every step is the mixed source step `nf_step3`
(`Source/NFStep3.lean`: Sil's fourth-power transfer inside Collet's pool step). The final return
(`FinalReturn/`) closes at 0.874275. -/
import Submissions.arvi_mixed_step_20261026.Graph.Endpoint3
import Submissions.arvi_mixed_step_20261026.Source.NFStep3

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (34971 / 40000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  apply QRH.MixedStep.Graph.dirichlet_of_step3 QRH.MixedStep.Source.nf_step3 χ s _ hpole
  convert hs using 1
  norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]

end Candidate
