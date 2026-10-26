/- The mixed-step face family: the gate `SourceValid3X` at every step of a piece.

For the family's threshold `q = (1 − den) L₀/(6 B₀ − L₀)`,
`6 q B₀ − L₀ = L₀ (L₀ − 6 den B₀)/(6 B₀ − L₀) > 0`, so Collet's LOW denominator is negative at every
step. No certificate data is needed beyond the field guards of `Certs3`. -/
import Submissions.arvi_mixed_step.Family.Validity3
import Submissions.arvi_mixed_step.Finite.SourceValid3X

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.MixedStep.Finite

namespace Piece
variable {P : Piece}

theorem Certs3.validX (C : P.Certs3) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    SourceValid3X (P.node3 y) (P.node3 (y - P.Dy)) := by
  obtain ⟨_, _, _, _, hq34, _, hB0, hB01, hL01⟩ := C.fieldPos hy0 hy1
  have hSp : 0 < 6 * P.B (y - P.Dy) - P.L (y - P.Dy) := by
    have hdenv : den = 1/2^15 := rfl
    rw [hdenv] at hq34
    linarith
  have hL0p : 0 < P.L (y - P.Dy) := by linarith
  have hden : den = 1/2^15 := rfl
  unfold SourceValid3X
  simp only [node3, q3]
  have key : 6 * ((1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy) - P.L (y - P.Dy))) *
      P.B (y - P.Dy) - P.L (y - P.Dy) =
      P.L (y - P.Dy) * (P.L (y - P.Dy) - 6 * den * P.B (y - P.Dy)) /
        (6 * P.B (y - P.Dy) - P.L (y - P.Dy)) := by
    field_simp
    ring
  rw [key]
  apply div_pos _ hSp
  apply mul_pos hL0p
  rw [hden]
  linarith

end Piece

end QRH.RepeatedMarks.Faceless
