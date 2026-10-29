/-
The return reads a proven shape.

The return never needs a face: it applies the energy bound to single configurations, the 31 count windows
(`finalCountScheme.windows`) and the physical numerator face. So its input is an energy region estimate `R`
together with one containment query per consumer: each window and the physical face must lie in `R`. Each
consumer may be covered by a different part of `R` (`literal_numerator_of_estimate`). The merged two-face
return is the special case `R = C ∪ P` (`beta_le_theta_of_two_face_shape`).
-/
import Submissions.arvi_energy_region.EnergyRegion
import Submissions.arvi_density.Return.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.ArviEnergyRegion
noncomputable section

open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence

/-- A region source restricts to every subregion. -/
theorem UnitRegionSource.mono {R R' : EnergyRegion} (hRR : R' ⊆ R) {mesh ε : ℝ}
    (h : UnitRegionSource R mesh ε) : UnitRegionSource R' mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨d, S, C, hC, hev⟩ := h α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨d, S, C, hC, hev.mono fun Z hZ => RegionAffineAt.mono rayM H hH hRR hZ⟩

/-- On a face region, a region source is the face source. -/
theorem unitRegionSource_faceRegion_iff (face : SourceFace) (mesh ε : ℝ) :
    UnitRegionSource (faceRegion face) mesh ε ↔ UnitFaceSource face mesh ε := Iff.rfl

/-- `Restricts` is containment of regions; a face with `plainLo < plainHi` only admits `0 ≤ M`. -/
theorem faceRegion_subset_of_restricts {strong weak : SourceFace} (h : strong.Restricts weak)
    (hw : weak.plainLo < weak.plainHi) : faceRegion weak ⊆ faceRegion strong := by
  rintro ⟨m₁, m₂, s, M⟩ hx
  have hx' : weak.Admissible m₁ m₂ s M := hx
  have hM : 0 ≤ M := by
    obtain ⟨h1, h2, -⟩ := hx'
    by_contra hneg
    have hneg' : M < 0 := lt_of_not_ge hneg
    nlinarith
  exact SourceFace.admissible_of_restricts h hM hx'

/-- An estimate is a uniform source for every face it contains. -/
theorem IsEstimate.faceSource {R : EnergyRegion} (hR : IsEstimate R) {W : SourceFace}
    (hW : faceRegion W ⊆ R) : UniformUnitFaceSource W :=
  (isEstimate_faceRegion_iff W).mp (hR.mono hW)

end
end QRH.ArviEnergyRegion

namespace QRH.ArviDensity.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.ArviEnergyRegion
namespace ShapeReturn
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsN := Geometry.finalBounds
local instance : CountScheme := finalCountScheme
local instance : GenericArithmetic.PhysicalSchedule := finalPhysicalSchedule

/-- **The return from a shape.** Every count window and the physical face are queries: each must lie in the
proven region `R`, possibly in different parts of it. -/
theorem literal_numerator_of_estimate {R : EnergyRegion} (hR : IsEstimate R)
    (hwin : ∀ w ∈ finalCountScheme.windows, faceRegion w.face ⊆ R)
    (hphys : faceRegion GenericPhysical.PhysicalDirect.physicalFace ⊆ R)
    (hcap : 2*HeckeZeroSupremum.beta-1 ≤ naturalK/6) : Final.LiteralNumeratorInput := by
  have hc : ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
      ∀ w ∈ finalCountScheme.windows, UnitFaceSource w.face mesh ε := by
    intro ε hε
    obtain ⟨mesh, hm, hs⟩ := hR ε hε
    exact ⟨mesh, hm, fun w hw => (unitRegionSource_faceRegion_iff _ _ _).mp (hs.mono (hwin w hw))⟩
  exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
    (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc (hR.faceSource hphys))

theorem beta_le_theta_of_estimate {R : EnergyRegion}
    (hR : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → IsEstimate R)
    (hwin : ∀ w ∈ finalCountScheme.windows, faceRegion w.face ⊆ R)
    (hphys : faceRegion GenericPhysical.PhysicalDirect.physicalFace ⊆ R) :
    HeckeZeroSupremum.beta ≤ (43693617/50000000 : ℝ) := by
  rw [← theta_value]
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · exact Final.beta_of_literal_numerator (literal_numerator_of_estimate (hR hbeta) hwin hphys natural_cap_return)
  · have ht : (51/100:ℝ) ≤ theta := by norm_num [theta, c]
    exact (not_le.mp hbeta).le.trans ht

/-- The windows of the merged return lie in `C ∪ P` (the face containments behind `supplier_restricts_counting`). -/
theorem windows_subset_two_faces :
    ∀ w ∈ finalCountScheme.windows, faceRegion w.face ⊆ faceRegion countGlobal ∪ faceRegion physicalGlobal := by
  intro w hw
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
  change faceRegion (countingSource v.branch) ⊆ _
  have hsub := faceRegion_subset_of_restricts (supplier_restricts_counting v.branch v.nonold)
    (by cases v.branch <;> norm_num [countingSource, broadFace])
  cases hb : v.branch <;> rw [hb] at hsub
  · exact (v.nonold hb).elim
  all_goals first
    | exact hsub.trans Set.subset_union_left
    | exact hsub.trans Set.subset_union_right

theorem physical_subset_physicalGlobal :
    faceRegion GenericPhysical.PhysicalDirect.physicalFace ⊆ faceRegion physicalGlobal := by
  refine faceRegion_subset_of_restricts ?_ (by norm_num [GenericPhysical.PhysicalDirect.physicalFace])
  change physicalGlobal.Restricts
    ⟨QRH.ArviDensity.Return.physicalB, QRH.ArviDensity.Return.physicalLambda, 0, 1/2, 0,
      QRH.ArviDensity.Return.numeratorCap⟩
  constructor <;> norm_num [physicalGlobal, QRH.Record1252270103Return.globalFace,
    QRH.ArviDensity.Return.physicalB, QRH.ArviDensity.Return.physicalCap, QRH.ArviDensity.Return.numeratorCap]

/-- The merged return as a special case: the shape `C ∪ P` of the count and physical faces. -/
theorem beta_le_theta_of_two_face_shape
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → UniformUnitFaceSource countGlobal)
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → UniformUnitFaceSource physicalGlobal) :
    HeckeZeroSupremum.beta ≤ (43693617/50000000 : ℝ) :=
  beta_le_theta_of_estimate (R := faceRegion countGlobal ∪ faceRegion physicalGlobal)
    (fun hβ => ((isEstimate_faceRegion_iff _).mpr (hC hβ)).union ((isEstimate_faceRegion_iff _).mpr (hP hβ)))
    windows_subset_two_faces (physical_subset_physicalGlobal.trans Set.subset_union_right)

end ShapeReturn
end
end QRH.ArviDensity.Return

#print axioms QRH.ArviDensity.Return.ShapeReturn.beta_le_theta_of_estimate
#print axioms QRH.ArviDensity.Return.ShapeReturn.beta_le_theta_of_two_face_shape
