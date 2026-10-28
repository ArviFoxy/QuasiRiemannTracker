/- Repeated marks: fork of Collet's generic return module Transport.Transport.TailScales (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
/- Modified by Sil (2026-10-26): forked into QRH.DensityTen.Bridge.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.density_ten.Bridge.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
set_option autoImplicit false
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.DensityTen.Bridge.Return.Geometry.BoundsN]
open scoped BigOperators
namespace SevenEighths.DensityTenReturn.TransportHighRowFamily
open ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+QRH.DensityTen.Bridge.ReturnT.Transport.Transport.b)/6-(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.y/2-QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [QRH.DensityTen.Bridge.ReturnT.Transport.Assembly.row_endpoint, QRH.DensityTen.Bridge.ReturnT.Transport.Transport.b]
  linarith [QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.x/2+QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.y)+(QRH.DensityTen.Bridge.ReturnT.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [QRH.DensityTen.Bridge.ReturnT.Transport.Assembly.row_endpoint]
  ring

end SevenEighths.DensityTenReturn.TransportHighRowFamily
end

end OAI

