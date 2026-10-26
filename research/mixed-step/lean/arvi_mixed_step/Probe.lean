import Submissions.arvi_mixed_step.Finite.HighGate3
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.StartFace
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite
def fan1 : Source := ⟨(18588231128263757/18720707281250000:ℚ),(1963935102933139/599062633000000:ℚ),(3/40:ℚ),(7499/10000:ℚ),(1/100000000000000000:ℚ),(1/1000000000000:ℚ),(1/10000000000:ℚ)⟩
example : 0 ≤ weakCap3 fan1 start fan1.cap := by decide +kernel
example : ∀ j : Fin 3, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate3 fan1 start fan1.cap ν j) fan1.q (3/4) i := by decide +kernel
#eval (List.finRange 18).map (fun j => decide (0 < scalarGate3 fan1 start fan1.cap j))
#eval (List.finRange 18).map (fun j => (scalarGate3 fan1 start fan1.cap j).floor)
#eval weakCap3 fan1 start fan1.cap
#eval (sourceD fan1 start fan1.cap)
