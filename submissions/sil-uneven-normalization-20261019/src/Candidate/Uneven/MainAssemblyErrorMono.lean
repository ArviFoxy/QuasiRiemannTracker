/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainAssemblyInitialHeight
set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open Sil.Uneven.MainSource
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R≤H)

/-- A proved smaller source error is enlarged only after the finite
parameters, mesh and controls have been fixed. -/
theorem initial_affine_error_mono (plane : Sil.Uneven.MainSource.Plane)
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax εsmall εbig Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hC : 0≤C) (hZ : 1<Z) (he : εsmall≤εbig)
    (h : MainInitial.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εsmall Z η η₀ Q degree S C) :
    MainInitial.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εbig Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hb:=h T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by have hd:=diagonalControl_nonneg Φ; positivity)
end
end OAI.SevenEighths.MainAssembly
#print axioms OAI.SevenEighths.MainAssembly.initial_affine_error_mono
