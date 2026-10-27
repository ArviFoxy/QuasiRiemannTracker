/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the norm caps `Fits.G_cap`, `Fits.D_cap` of a second label from the radical cap
`Fits.cap`: `N(G) ≤ N(rad G)²` when `G ∣ rad(G)²` (multiplicities at most two, i.e. `G`
cube-free), `N(t₂) = N(rad t₂)` for squarefree `t₂`, and the radicals of `G` and `t₂` divide the
capped product `∏_{P ∈ supp((R G) t₂) ∪ holes} P`. -/
import Submissions.density_split_third_20261026.CubeFree.FP.MixedCompletedRows
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.ValuationEnumeration

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped BigOperators Classical
open Candidate.FourthPower
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal
open QRH.DensitySplitThird.CubeFree.FP
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles KernelRowExpansion
open KernelRowPools KernelRestrictedState KernelPunctureRows KernelLabelledSlots
open MixedCommonRestriction MixedTupleRows RestorationFamily
open QRH.DensitySplitThird.CubeFree.FP.MixedCompletedRows
local notation "O" => HeckeFamily.O

theorem absNorm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (h : I ∣ J) :
    (I.absNorm : ℝ) ≤ (J.absNorm : ℝ) := by
  have hn : 0 < Ideal.absNorm J :=
    Nat.pos_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm h)

/-- A product over a subset of nonzero ideals has smaller norm. -/
theorem prod_absNorm_le_of_subset {S T : Finset (Ideal O)} (hST : S ⊆ T) (hT : ∀ P ∈ T, P ≠ 0) :
    ((∏ P ∈ S, P).absNorm : ℝ) ≤ ((∏ P ∈ T, P).absNorm : ℝ) :=
  absNorm_le_of_dvd (Finset.prod_ne_zero_iff.mpr hT) (Finset.prod_dvd_prod_of_subset S T id hST)

/-- `N(I) ≤ N(rad I)²` when `I ∣ rad(I)²`. -/
theorem norm_le_rad_sq {I : Ideal O}
    (h3 : I ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P)^2) :
    (I.absNorm : ℝ) ≤ ((∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P).absNorm : ℝ)^2 := by
  have hne : (∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P)^2 ≠ 0 :=
    pow_ne_zero 2 (IdealMobiusDivisorSum.support_product_ne_zero (subset_refl _))
  have h := absNorm_le_of_dvd hne h3
  rwa [map_pow, Nat.cast_pow] at h

theorem norm_eq_rad_of_squarefree {I : Ideal O} (hI : Squarefree I) :
    (I.absNorm : ℝ) = ((∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P).absNorm : ℝ) := by
  rw [IdealMobiusDivisorSum.squarefree_support_product_self hI]

theorem capped_members_ne_zero (R G D : Ideal O) (H : Finset {P : Ideal O // Prime P}) :
    ∀ P ∈ IdealMobiusDivisorSum.primeSupport ((R*G)*D) ∪ holes H, P ≠ 0 := by
  intro P hP
  rcases Finset.mem_union.mp hP with h | h
  · exact (IdealMobiusDivisorSum.support_prime h).ne_zero
  · exact (holes_prime H P h).ne_zero

/-- **`Fits.G_cap`** from the radical cap. -/
theorem G_cap_of_cap (R G D : Ideal O) (H : Finset {P : Ideal O // Prime P}) (hR : R ≠ 0) (hG : G ≠ 0)
    (hD : D ≠ 0) (hG3 : G ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport G, P)^2) (Z B : ℝ)
    (hZ : 0 ≤ Z)
    (hcap : (Ideal.absNorm (∏ I ∈ IdealMobiusDivisorSum.primeSupport ((R*G)*D) ∪ holes H, I) : ℝ) ≤
      Z^B) :
    (G.absNorm : ℝ) ≤ Z^(2*B) := by
  have hsub : IdealMobiusDivisorSum.primeSupport G ⊆
      IdealMobiusDivisorSum.primeSupport ((R*G)*D) ∪ holes H :=
    (QRH.Record1252270103KernelMass.primeSupport_subset_of_dvd hG
      (mul_ne_zero (mul_ne_zero hR hG) hD)
      (Dvd.dvd.mul_right (Dvd.intro_left R rfl) D)).trans Finset.subset_union_left
  have hrad := prod_absNorm_le_of_subset hsub (capped_members_ne_zero R G D H)
  have h0 : (0:ℝ) ≤ ((∏ P ∈ IdealMobiusDivisorSum.primeSupport G, P).absNorm : ℝ) := Nat.cast_nonneg _
  calc (G.absNorm : ℝ) ≤ ((∏ P ∈ IdealMobiusDivisorSum.primeSupport G, P).absNorm : ℝ)^2 :=
        norm_le_rad_sq hG3
    _ ≤ (Z^B)^2 := pow_le_pow_left₀ h0 (hrad.trans hcap) 2
    _ = Z^(2*B) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; ring_nf

/-- **`Fits.D_cap`** from the radical cap. -/
theorem D_cap_of_cap (R G D : Ideal O) (H : Finset {P : Ideal O // Prime P}) (hR : R ≠ 0) (hG : G ≠ 0)
    (hD : Squarefree D) (Z B : ℝ)
    (hcap : (Ideal.absNorm (∏ I ∈ IdealMobiusDivisorSum.primeSupport ((R*G)*D) ∪ holes H, I) : ℝ) ≤
      Z^B) :
    (D.absNorm : ℝ) ≤ Z^B := by
  have hsub : IdealMobiusDivisorSum.primeSupport D ⊆
      IdealMobiusDivisorSum.primeSupport ((R*G)*D) ∪ holes H :=
    (QRH.Record1252270103KernelMass.primeSupport_subset_of_dvd hD.ne_zero
      (mul_ne_zero (mul_ne_zero hR hG) hD.ne_zero) (Dvd.intro_left (R*G) rfl)).trans
        Finset.subset_union_left
  rw [norm_eq_rad_of_squarefree hD]
  exact (prod_absNorm_le_of_subset hsub (capped_members_ne_zero R G D H)).trans hcap

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
