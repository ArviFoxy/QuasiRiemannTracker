/- Mixed source step, L3 interface: new in this submission; uses the baseline's
`residualPool`, `residual_ne` and `residual_coverage` by import (as in the
baseline's `child`).

`Input.shortenPlains s D₀ D₁`: the input with the two plains shortened by `D₀`,
`D₁` (design §7): plains `{a : D_k·a ∈ plain_k}`, lengths `X_k/N(D_k)`,
`Y_k/N(D_k)`; slots, weights and radial data unchanged. Its volume is
`volume s / (N(D₀) N(D₁))`, and its plain rectangle at `a` is the original
rectangle at `D_k·a` (`rectangle_shorten`). It commutes with `restrict`. -/
import Submissions.arvi_mixed_step.Residual.Restrict

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace OAI.SevenEighths.CenteredMomentCommonRadialData
noncomputable section
open scoped BigOperators Classical
open CenteredMomentFirstSectors CenteredMomentAmplificationChildInput
local notation "O" => ActualEisensteinCubic.O

theorem absNorm_pos_of_ne {D : Ideal O} (h : D ≠ 0) : (0 : ℝ) < Ideal.absNorm D := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h)

/-- The input with both plains shortened. -/
def Input.shortenPlains {α : Type*} [Fintype α] (s : Input α) (D₀ D₁ : Ideal O)
    (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0) : Input α where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := s.slots
  prime := s.prime
  ν := s.ν
  W := s.W
  lo := s.lo
  hi := s.hi
  P := s.P
  lo_pos := s.lo_pos
  P_pos := s.P_pos
  support := s.support
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁ / Ideal.absNorm D₀
  X₂ := s.X₂ / Ideal.absNorm D₁
  Y₁ := s.Y₁ / Ideal.absNorm D₀
  Y₂ := s.Y₂ / Ideal.absNorm D₁
  M := s.M
  M_ge_one := s.M_ge_one
  coefficient_bound := s.coefficient_bound
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := div_pos s.X₁_pos (absNorm_pos_of_ne h₀)
  X₂_pos := div_pos s.X₂_pos (absNorm_pos_of_ne h₁)
  Y₁_pos := div_pos s.Y₁_pos (absNorm_pos_of_ne h₀)
  Y₂_pos := div_pos s.Y₂_pos (absNorm_pos_of_ne h₁)
  same_product := by rw [div_mul_div_comm, div_mul_div_comm, s.same_product]
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := residualPool D₀ h₀ s.plain₁
  plain₂ := residualPool D₁ h₁ s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := s.ν_bound
  W_bound := s.W_bound
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := s.lower_le
  upper_ge := s.upper_ge

section Fields
variable {α : Type*} [Fintype α] (s : Input α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)

@[simp] theorem shortenPlains_slots : (s.shortenPlains D₀ D₁ h₀ h₁).slots = s.slots := rfl
@[simp] theorem shortenPlains_P : (s.shortenPlains D₀ D₁ h₀ h₁).P = s.P := rfl
@[simp] theorem shortenPlains_X₁ :
    (s.shortenPlains D₀ D₁ h₀ h₁).X₁ = s.X₁ / Ideal.absNorm D₀ := rfl
@[simp] theorem shortenPlains_X₂ :
    (s.shortenPlains D₀ D₁ h₀ h₁).X₂ = s.X₂ / Ideal.absNorm D₁ := rfl
theorem mem_shortenPlains_plain₁ (a : Ideal O) :
    a ∈ (s.shortenPlains D₀ D₁ h₀ h₁).plain₁ ↔ D₀ * a ∈ s.plain₁ := mem_residualPool D₀ h₀ _ _
theorem mem_shortenPlains_plain₂ (a : Ideal O) :
    a ∈ (s.shortenPlains D₀ D₁ h₀ h₁).plain₂ ↔ D₁ * a ∈ s.plain₂ := mem_residualPool D₁ h₁ _ _

theorem volume_shortenPlains :
    volume (s.shortenPlains D₀ D₁ h₀ h₁) =
      volume s / ((Ideal.absNorm D₀ : ℝ) * Ideal.absNorm D₁) := by
  have h0 := (absNorm_pos_of_ne h₀).ne'
  have h1 := (absNorm_pos_of_ne h₁).ne'
  unfold volume
  change s.X₁ / Ideal.absNorm D₀ * (s.X₂ / Ideal.absNorm D₁) * ∏ i, s.P i = _
  field_simp

end Fields

/-- The shortened rectangle at `a` is the original rectangle at `D·a`. -/
theorem rectangle_shorten (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (D₀ D₁ a b : Ideal O) :
    CenteredMomentRectangle.idealRectangle W₁ W₂ (X₁ / Ideal.absNorm D₀) (X₂ / Ideal.absNorm D₁)
        (Y₁ / Ideal.absNorm D₀) (Y₂ / Ideal.absNorm D₁) a b =
      CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (D₀ * a) (D₁ * b) := by
  unfold CenteredMomentRectangle.idealRectangle
  simp only [map_mul, Nat.cast_mul, div_div_eq_mul_div]
  ring_nf

/-- Shortening the plains commutes with removing slots. -/
theorem restrict_shortenPlains {α : Type*} [Fintype α] [DecidableEq α] (s : Input α)
    (J : Finset α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0) :
    (s.restrict J).shortenPlains D₀ D₁ h₀ h₁ = (s.shortenPlains D₀ D₁ h₀ h₁).restrict J := rfl

end
end OAI.SevenEighths.CenteredMomentCommonRadialData

#print axioms OAI.SevenEighths.CenteredMomentCommonRadialData.volume_shortenPlains
#print axioms OAI.SevenEighths.CenteredMomentCommonRadialData.rectangle_shorten
#print axioms OAI.SevenEighths.CenteredMomentCommonRadialData.restrict_shortenPlains
