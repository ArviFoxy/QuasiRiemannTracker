/- Repeated marks: fork of Collet's generic return module Transport.Transport.CentralFiniteError (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<81/100 in the bank fork, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_bank.ReturnD and QRH.ArviDensity.Return (no other change). -/
import Submissions.arvi_bank.ReturnD.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError
import Submissions.arvi_bank.ReturnD.Transport.Transport.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
set_option autoImplicit false
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.ArviDensity.Return.Geometry.BoundsN]
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ArviDensityReturn.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(QRH.ArviDensity.ReturnT.Transport.Arithmetic.ell:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(QRH.ArviDensity.ReturnT.Transport.Arithmetic.ell:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]

end SevenEighths.ArviDensityReturn.TransportHighRowFamily

end

end OAI

