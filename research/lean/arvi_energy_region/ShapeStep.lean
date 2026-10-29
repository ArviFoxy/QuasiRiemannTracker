/-
Shape → shape iteration.  The density step, read on shapes: if a proven shape `R` contains the parent face's
half-space, then `R ∪ (child face)` is again an estimate.  The face-by-face chain is the special case where each
shape is the union of the faces proven so far; the iteration is monotone and every iterate lies in the Arvi Zone.
A continuous family of faces (an ODE curve) gives one shape, the union of its faces, which lies in the Arvi Zone
as soon as every face is an estimate (`ode_shape_subset_arviZone`).
-/
import Submissions.arvi_energy_region.EnergyRegion
import Submissions.arvi_density.Density.StepMarked

set_option autoImplicit false

namespace QRH.ArviEnergyRegion
noncomputable section

open OAI OAI.SevenEighths QRH.Record1252270103Source QRH.ArviDensity

/-- The half-space of a global face. -/
abbrev globalRegion (B lam cap : ℝ) : EnergyRegion := faceRegion (globalFace B lam cap)

/-- **Density step on shapes**: a shape containing the parent face grows by the child face. -/
theorem density_shape_step {R : EnergyRegion} (hR : IsEstimate R)
    (qf B₀ L₀ c₀ B L c A D : ℝ) (hqf : 1/2 ≤ qf) (hqf' : qf ≤ 3/4) (hB₀ : 22/23 ≤ B₀)
    (h : HybridGatesM qf B₀ L₀ c₀ B L c A D) (hF : Density.DSFace B₀ L₀ c₀ B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hpar : globalRegion B₀ L₀ c₀ ⊆ R) :
    IsEstimate (R ∪ globalRegion B L c) := by
  have hparent : GlobalSource B₀ L₀ c₀ := (isEstimate_globalFace_iff B₀ L₀ c₀).mp (hR.mono hpar)
  have hchild := Density.density_step_marked qf B₀ L₀ c₀ B L c A D hqf hqf' hB₀ h hF hβ hparent
  exact hR.union ((isEstimate_globalFace_iff B L c).mpr hchild)

/-- Monotone shape iteration: an estimate grown by any estimate stays an estimate, and only grows. -/
theorem shape_iterate_mono {R R' : EnergyRegion} (hR : IsEstimate R) (hR' : IsEstimate R') :
    IsEstimate (R ∪ R') ∧ R ⊆ R ∪ R' :=
  ⟨hR.union hR', Set.subset_union_left⟩

/-- An ODE shape: the union of a continuous family of faces `Λ ↦ (β Λ, Λ, cap)` over a parameter set `I`. -/
def odeShape (β : ℝ → ℝ) (cap : ℝ) (I : Set ℝ) : EnergyRegion := ⋃ Λ ∈ I, globalRegion (β Λ) Λ cap

/-- The ODE shape lies in the Arvi Zone as soon as every face of the family is proven. -/
theorem ode_shape_subset_arviZone (β : ℝ → ℝ) (cap : ℝ) (I : Set ℝ)
    (h : ∀ Λ ∈ I, GlobalSource (β Λ) Λ cap) : odeShape β cap I ⊆ arviZone := by
  intro x hx
  simp only [odeShape, Set.mem_iUnion] at hx
  obtain ⟨Λ, hΛ, hx⟩ := hx
  exact subset_arviZone ((isEstimate_globalFace_iff _ _ _).mpr (h Λ hΛ)) hx

end
end QRH.ArviEnergyRegion

#print axioms QRH.ArviEnergyRegion.density_shape_step
#print axioms QRH.ArviEnergyRegion.ode_shape_subset_arviZone
