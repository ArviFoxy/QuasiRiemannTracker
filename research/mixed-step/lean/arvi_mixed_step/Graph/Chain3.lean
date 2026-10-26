/- The mixed source chain: generic part.

The chain runs from Sil's face (`QRH.RepeatedMarks.start`) through the fan (`Fan/Steps.lean`, faces
through one point on Sil's line) and the junction steps into the pieces of the mixed face family
(`Family/`). Every step is a mixed source step (`SourceValid3`) whose LOW and HIGH parent is the
previous face. `NFStep3` is the analytic theorem the chain consumes; `Certs3.valid` proves the step
certificate for every face of a piece at once, and a piece is an induction along its grid
`y = i/2^16` (`piece_sources3`). -/
import Submissions.arvi_mixed_step.Family.Validity3
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Graph.GraphContract

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite
open QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless

/-- The mixed source step. -/
def NFStep3 : Prop := ∀ n low h : Source,
 (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK →
 SourceValid3 n low h → ParentGood low → NFAccounting n →
 P low → P h → P n

lemma parent_good_of_valid3 {n low h : Source} (hv : SourceValid3 n low h) : ParentGood n :=
  ⟨hv.1.1, hv.1.2.1, hv.1.2.2.1, hv.1.2.2.2.1, hv.1.2.2.2.2.1⟩

/-- The HIGH parent of a valid mixed step is a good parent. -/
lemma parent_good_of_high3 {n low h : Source} (hv : SourceValid3 n low h) : ParentGood h := by
  obtain ⟨hB, hB1, hL, hc0, hc1⟩ := hv.1.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨lt_of_lt_of_le (by norm_num) hB, hB1, hL, hc0, hc1⟩

lemma nf_accounting_node3 (P : Piece) (y : ℚ) : NFAccounting (P.node3 y) :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- Every face of a mixed piece on the grid `y = i·Dy` is a global source. -/
theorem piece_sources3 (step : NFStep3) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (C : P.Certs3)
    (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node3 0)) :
    ∀ i : ℕ, i < 2 ^ 16 → QRH.Record1252270103Graph.P (P.node3 (i * P.Dy)) := by
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
    rw [hprev] at hv
    have hpar := ih (by omega)
    exact step _ _ _ hβ hk hv (parent_good_of_high3 hv) (nf_accounting_node3 P _) hpar hpar

/-- The last face of a mixed piece. -/
theorem piece_last3 (step : NFStep3) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (C : P.Certs3)
    (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node3 0)) :
    QRH.Record1252270103Graph.P (P.node3 (1 - P.Dy)) := by
  have h := piece_sources3 step hβ hk P C hD h0 (2 ^ 16 - 1) (by norm_num)
  have : ((2 ^ 16 - 1 : ℕ) : ℚ) * P.Dy = 1 - P.Dy := by
    push_cast; linear_combination hD
  rwa [this] at h

end
end QRH.MixedStep.Graph
