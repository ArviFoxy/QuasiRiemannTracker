/- Mixed source step: new in this submission. The mixed source chain: pieces with a variable cap.

As `piece_sources3` / `piece_last3` (`Graph/Chain3.lean`), for a piece whose face at `y` has cap
`cp(y)` (`Family/Validity3c.lean`). A piece whose cap starts at `capM` starts at the same face as the
constant-cap piece (`node3c_zero`). -/
import Submissions.arvi_mixed_step.Graph.Chain3
import Submissions.arvi_mixed_step.Family.Validity3c

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite
open QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless Poly

lemma nf_accounting_node3c (P : Piece) (cp : Poly) (y : ℚ) : NFAccounting (P.node3c cp y) :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- A variable-cap piece whose cap starts at `capM` starts at the constant-cap face. -/
lemma node3c_zero (P : Piece) (cp : Poly) (h : eval cp 0 = capM) : P.node3c cp 0 = P.node3 0 := by
  simp only [Piece.node3c, Piece.node3, h]

/-- Every face of a variable-cap piece on the grid `y = i·Dy` is a global source. -/
theorem piece_sources3c (step : NFStep3) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (cp : Poly)
    (C : P.Certs3c cp) (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node3c cp 0)) :
    ∀ i : ℕ, i < 2 ^ 16 → QRH.Record1252270103Graph.P (P.node3c cp (i * P.Dy)) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    have hD0 := C.Dy0
    have hy0 : 0 ≤ ((i + 1 : ℕ) : ℚ) * P.Dy := by positivity
    have hy1 : ((i + 1 : ℕ) : ℚ) * P.Dy ≤ 1 := by
      have : ((i + 1 : ℕ) : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hi.le
      calc ((i + 1 : ℕ) : ℚ) * P.Dy ≤ 2 ^ 16 * P.Dy := by gcongr
        _ = 1 := by rw [mul_comm]; exact hD
    have hprev : ((i + 1 : ℕ) : ℚ) * P.Dy - P.Dy = (i : ℚ) * P.Dy := by push_cast; ring
    have hv := C.valid _ hy0 hy1
    have hx := C.validX _ hy0 hy1
    rw [hprev] at hv hx
    have hpar := ih (by omega)
    exact step _ _ _ hβ hk hv hx (parent_good_of_high3 hv) (nf_accounting_node3c P cp _) hpar hpar

/-- The last face of a variable-cap piece. -/
theorem piece_last3c (step : NFStep3) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (cp : Poly)
    (C : P.Certs3c cp) (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node3c cp 0)) :
    QRH.Record1252270103Graph.P (P.node3c cp (1 - P.Dy)) := by
  have h := piece_sources3c step hβ hk P cp C hD h0 (2 ^ 16 - 1) (by norm_num)
  have : ((2 ^ 16 - 1 : ℕ) : ℚ) * P.Dy = 1 - P.Dy := by
    push_cast; linear_combination hD
  rwa [this] at h

end
end QRH.MixedStep.Graph
