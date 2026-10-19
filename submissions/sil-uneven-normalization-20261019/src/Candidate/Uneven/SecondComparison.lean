/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/
import Candidate.Uneven.SecondNorm

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
variable (Mprice Aprice : ℝ)
variable (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)

/-- Actual common surplus decreases the second weight pointwise.
No cancellation or HIGH source estimate is replaced by this comparison. -/
theorem uneven_main_second_weight_norm_le
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖ := by
  have hs := actual_allocation_nonneg reflected s R seed (Z^Mrow) Z ξ hZ j.1.1.val.1.val
  have hp : Z^(-allocation reflected (geometryExponents s R seed (Z^Mrow) Z ξ j.1.1.val.1.val))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (neg_nonpos.mpr hs)
  rw [unevenMainSecondWeight_eq]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (norm_nonneg (geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j))

theorem uneven_main_second_product_norm_le
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)
    (value : ℂ) :
    ‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*value‖≤
      ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*value‖ := by
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    (uneven_main_second_weight_norm_le reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j)
    (norm_nonneg _)

/-- Complete selected exceptional families retain the same indices and
values; only their actual first-allocation weight is reduced. -/
theorem uneven_main_second_norm_sum_le {Label : Type*} [Fintype Label]
    (column : Label→GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)
    (value : Label→ℂ) :
    (∑j,‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j)*value j‖)≤
      ∑j,‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j)*value j‖ := by
  exact Finset.sum_le_sum (fun j _=>uneven_main_second_product_norm_le
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j) (value j))

end
end OAI.SevenEighths.Target830.Source.Uneven
#print axioms OAI.SevenEighths.Target830.Source.Uneven.uneven_main_second_weight_norm_le
#print axioms OAI.SevenEighths.Target830.Source.Uneven.uneven_main_second_product_norm_le
#print axioms OAI.SevenEighths.Target830.Source.Uneven.uneven_main_second_norm_sum_le
