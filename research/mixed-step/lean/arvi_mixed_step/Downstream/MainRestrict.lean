/- Mixed step (L4/L5, F6): glue for the MAIN twins on the transfer residual (new in this submission).

The MAIN complement and remainder twins (ForkMx `…MainExceptional*`, `…RemainderScalarSum*`,
`…RemainderOne`) run their second layer on the transfer residual `s₀.restrict J` of a canonical
initial input `s₀`. That residual is literally the canonical initial input of the restricted slot
data `(θ ∘ val, w ∘ val, v ∘ val)` (`restrict_initialInput`, by `rfl`), so Collet's initial-input
caps apply to it. This file supplies the three facts about the restriction that the twins use:
* `restrict_admissible`: removing nonnegative-width slots keeps a global-face cell admissible;
* `restrict_width_le`: the residual width sum is at most the original one;
* `logb_volume_restrict`: the residual log-volume drop is exactly the transferred width, so the
  δ-shift `amp - a ≤ Σ_J w + κ` is `amp - a ≤ logb V₀ - logb V_res + κ`. -/
import Submissions.arvi_mixed_step.Residual.Restrict
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialMainRemainderGap

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped BigOperators ContDiff
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open QRH.Record1252270103Source
local notation "O" => HeckeFamily.O

section Widths
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The width sum splits along the transferred block. -/
theorem restrict_width_sum (w : α → ℝ) (J : Finset α) :
    (∑ i : {i // i ∉ J}, w i.val) + ∑ j ∈ J, w j = ∑ i, w i := by
  rw [← Finset.sum_compl_add_sum J w]
  congr 1
  exact (Finset.sum_subtype Jᶜ (fun i => by simp) (fun i => w i)).symm

theorem restrict_width_le (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (J : Finset α) :
    (∑ i : {i // i ∉ J}, w i.val) ≤ ∑ i, w i := by
  have h := restrict_width_sum w J
  have h0 : 0 ≤ ∑ j ∈ J, w j := Finset.sum_nonneg (fun j _ => hw j)
  linarith

theorem restrict_width_nonneg (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (J : Finset α) :
    0 ≤ ∑ i : {i // i ∉ J}, w i.val :=
  Finset.sum_nonneg (fun i _ => hw i.val)

/-- Removing nonnegative-width slots keeps a global-face cell admissible. -/
theorem restrict_admissible (Bf lam cap m₁ m₂ : ℝ) (hlam : 0 ≤ lam) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (J : Finset α)
    (h : (globalFace Bf lam cap).Admissible m₁ m₂ (∑ i, w i) 1) :
    (globalFace Bf lam cap).Admissible m₁ m₂ (∑ i : {i // i ∉ J}, w i.val) 1 := by
  have hle := restrict_width_le w hw J
  have h0 := restrict_width_nonneg w hw J
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [globalFace] at h1 h2 h3 h4 h5 h6 h7 ⊢
  refine ⟨h1, h2, h3, h4, by linarith, by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_left hle hlam
  linarith

end Widths

/-- The residual log-volume drop is the transferred width. -/
theorem logb_volume_restrict {α : Type*} [Fintype α] [DecidableEq α] (s : Input α)
    (J : Finset α) (Z : ℝ) (hZ : 1 < Z) (w : α → ℝ) (hP : ∀ i, s.P i = Z^(w i)) :
    Real.logb Z (volume (s.restrict J)) = Real.logb Z (volume s) - ∑ j ∈ J, w j := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [QRH.MixedStep.Residual.volume_restrict]
  have hprod : (∏ j ∈ J, s.P j) = Z^(∑ j ∈ J, w j) := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_congr rfl (fun j _ => hP j)
  rw [hprod, Real.logb_div (volume_pos s).ne' (Real.rpow_pos_of_pos hZ0 _).ne',
    Real.logb_rpow hZ0 hZ.ne']

section Initial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance mainRestrictFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : CenteredMomentFiniteProfileExceptional.Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)

/-- The transfer residual of a canonical initial input is the canonical initial input of the
restricted slot data. -/
theorem restrict_initialInput (J : Finset ι) :
    (initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p (by norm_num)
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod).restrict J =
    initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ (fun i : {i // i ∉ J} => θ i.val)
      (fun i => w i.val) (fun i => v i.val) t p (by norm_num)
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod := rfl

/-- The δ-shift in log-volume form for the canonical residual. -/
theorem initial_restrict_logb (J : Finset ι) (hZ1 : 1 < Z) :
    Real.logb Z (volume ((initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p (by norm_num)
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod).restrict J)) =
    Real.logb Z (volume (initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p (by norm_num)
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod)) - ∑ j ∈ J, w j :=
  logb_volume_restrict _ J Z hZ1 w (fun _ => rfl)

end Initial

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.restrict_admissible
#print axioms QRH.MixedStep.Downstream.logb_volume_restrict
#print axioms QRH.MixedStep.Downstream.restrict_initialInput
#print axioms QRH.MixedStep.Downstream.initial_restrict_logb
