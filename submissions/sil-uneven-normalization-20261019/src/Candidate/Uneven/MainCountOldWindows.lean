/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountConcrete

set_option autoImplicit false
namespace OAI.SevenEighths.MainCount
noncomputable section

def Window.ofOld (w : Target830.Count.Window) : Window where
  plane := Plane.ofOld w.plane
  deltaLo := w.deltaLo
  deltaHi := w.deltaHi
  pLo := w.pLo
  bounds := w.bounds

theorem Window.ofOld_admissible (w : Target830.Count.Window) {d p : ℝ}
    (h : Target830.Count.Admissible w.plane d p) :
    Admissible (Window.ofOld w).plane d p := by
  constructor
  · simpa only [Window.ofOld,guardD,Target830.Count.guardD,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.denominator
  · simpa only [Window.ofOld,guardA,Target830.Count.guardA,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.a
  · simpa only [Window.ofOld,guardC,Target830.Count.guardC,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.c
  · simpa only [Window.ofOld,guardJ,Target830.Count.guardJ,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.j
  · simpa only [Window.ofOld,guardTLo,Target830.Count.guardTLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cutoff_lower
  · simpa only [Window.ofOld,guardTHi,Target830.Count.guardTHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cutoff_upper
  · simpa only [Window.ofOld,guardRLo,Target830.Count.guardRLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cross_lower
  · simpa only [Window.ofOld,guardRHi,Target830.Count.guardRHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cross_upper
  · simpa only [Window.ofOld,guardMLo,Target830.Count.guardMLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.plain_lower
  · simpa only [Window.ofOld,guardMHi,Target830.Count.guardMHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.plain_upper
  · simpa only [Window.ofOld,guardWidth,Target830.Count.guardWidth,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.selected_lower
  · simpa only [Window.ofOld,guardTail,Target830.Count.guardTail,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.tail
  · simpa only [Window.ofOld,guardMonotone,Target830.Count.guardMonotone,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.monotone

end
end OAI.SevenEighths.MainCount
#print axioms OAI.SevenEighths.MainCount.Window.ofOld_admissible
