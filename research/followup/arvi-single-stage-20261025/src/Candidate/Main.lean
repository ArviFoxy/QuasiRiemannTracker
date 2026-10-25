/- Repeated marks in one stage: the candidate bound 2186813/2500000 = 0.8747252.
The natural cost is K = 9/2. Its cap 6(2β − 1) ≤ K is the baseline's β ≤ 7/8
(Graph/NaturalCap.lean), so the proof is a single stage: the face family (Graph/Chain.lean,
Faceless/) from the natural face to its end, then the final return (FinalReturn/). The source step
`nf_step2` (Source/NFStep2.lean) is the repeated-mark fork of Collet's NF step. -/
import Submissions.arvi_single_stage_20261025.Graph.Endpoint
import Submissions.arvi_single_stage_20261025.Source.NFStep2

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2186813 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  apply QRH.RepeatedMarks.Graph.dirichlet_of_step QRH.RepeatedMarks.Source.nf_step2 χ s _ hpole
  convert hs using 1
  norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]

end Candidate
