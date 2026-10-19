/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedMonotone
import Candidate.Cycle63.Marked.DeletionMaxAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem max_weighted_row_sum {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C d loss : ℝ)
    (hw : ∀s∈slots,0≤ w s) (hU : 1≤ U) (hC : 0≤ C)
    (hd0 : 0≤ d) (hd : d<5/6)
    (hsub : ∀J⊆slots,(∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(fullCount d (∑s∈J,w s)+d*(∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(fullCount d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
  have hs (J : Finset Slot) (hJ:J⊆slots) :
      fullCount d (∑s∈J,w s)+d*(∑s∈J,w s)+loss ≤
      fullCount d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss := by
    apply add_le_add _ (le_refl loss)
    exact full_exponent_mono hd0 hd
      (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun s hs _=>hw s hs))
  calc
    _ ≤ ∑u∈rows,∑J∈slots.powerset,‖∏s∈J,Q u s‖^2 :=
      Finset.sum_le_sum (fun u _=>OAI.SevenEighths.Deletion26.max_product_le_powerset slots (Q u))
    _ = ∑J∈slots.powerset,∑u∈rows,‖∏s∈J,Q u s‖^2 := Finset.sum_comm
    _ ≤ ∑J∈slots.powerset,C*U^(fullCount d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJs := Finset.mem_powerset.mp hJ
      exact (hsub J hJs).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (hs J hJs)) hC)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

theorem max_weighted_row_sum_of_nonempty {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C d loss : ℝ)
    (hw : ∀s∈slots,0≤ w s) (hU : 1≤ U) (hC : 0≤ C)
    (hd0 : 0≤ d) (hd : d<5/6)
    (hcount : (rows.card : ℝ)≤ C*U^(rho d+loss))
    (hsub : ∀J⊆slots,J.Nonempty → (∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(fullCount d (∑s∈J,w s)+d*(∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(fullCount d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
  apply max_weighted_row_sum rows slots Q w U C d loss hw hU hC hd0 hd
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl|hne
  · simp only [Finset.prod_empty,norm_one,one_pow,Finset.sum_const,Finset.sum_empty,
      nsmul_eq_mul,mul_one,mul_zero,add_zero]
    exact hcount.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (add_le_add (zero_width_lower hd) (le_refl loss))) hC)
  · exact hsub J hJ hne

end Sil.Uneven.Saturated
#print axioms Sil.Uneven.Saturated.max_weighted_row_sum_of_nonempty
