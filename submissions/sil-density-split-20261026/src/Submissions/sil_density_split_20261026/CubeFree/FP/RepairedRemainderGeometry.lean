/- Copyright (c) 2026 Sil. Apache-2.0.
Exact raw zero/tail normalization and original-seed algebra. No analytic
estimate is assumed here.
Modified by Sil (2026-10-26): WP-K2b: only the lane-free part is kept (coefficient_zero_of_cap_lt_one, sharp_support_factored, linear_seed_scalar made public); the u-freezing supplier-lane statements (grouped_norm_le_average, outer_zero_of_cap_lt_one, residual_profileCap_le, raw_zero_geometry on Data/Frozen/supplierData) are not ported (replaced lane; the cube-free second step is Second/Concrete*).
-/
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstLiveRemainders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.SilDensitySplit.CubeFree.FP.RepairedRemainderGeometry
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open MixedFirstLiveRemainders
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqRemainderGeometry {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Subunit sharp support forces the actual coefficient to vanish. -/
theorem coefficient_zero_of_cap_lt_one (s : Source ι a b) (ha : 0 < a)
    (seed : Id) (hcap : sourceNormCap s.P b s.T s.d < 1) (I : Id) :
    sourceCoefficient s ha seed I = 0 := by
  by_contra hn
  have hc := original_coefficient_cap s ha seed I hn
  exact (not_le_of_gt hcap) ((ideal_norm_one_le hc.1).trans hc.2)

theorem sharp_support_factored (s : Source ι a b) :
    sourceNormCap s.P b s.T s.d = b^2 * (2 : ℝ)^Fintype.card ι * (sourceVolume s / pairNorm s.d) := by
  rw [source_cap_factored, ← s.hpX]
  rfl

/-- The seed restoration scalar (FP `linear_seed_scalar`, generic). -/
theorem linear_seed_scalar (F f seed u T : ℝ)
    (hF : 0 < F) (hf : 0 < f) (hs : 0 < seed) (hu : u = f * seed) (hcap : f ≤ T * F) :
    1 / (F * seed) ≤ T / u := by
  have hu0 : 0 < u := hu.symm ▸ mul_pos hf hs
  apply (div_le_div_iff₀ (mul_pos hF hs) hu0).mpr
  rw [one_mul, hu]
  convert mul_le_mul_of_nonneg_right hcap hs.le using 1 <;> ring

end
end QRH.SilDensitySplit.CubeFree.FP.RepairedRemainderGeometry
