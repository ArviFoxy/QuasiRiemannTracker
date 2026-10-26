/- Mixed source step: the one gate beyond `SourceValid3`.

The virtual nodes of the downstream (`Ledger/`) evaluate Collet's step formulas at a shifted node,
and Collet's amplifier `sourceA = (…)/sourceDen` needs `sourceDen n low = 1 − 6qB₀/L₀ ≠ 0`. On the
mixed chain this denominator is negative: `6 q B₀ > L₀`. That is the certificate form here. -/
import Submissions.arvi_mixed_step.Finite.SourceValid3
set_option autoImplicit false
namespace QRH.MixedStep.Finite
open Record1252270103Finite

/-- Collet's LOW denominator is negative: `6 q B₀ − L₀ > 0`. -/
def SourceValid3X (n low : Source) : Prop := 0 < 6*n.q*low.B - low.L

instance (n low : Source) : Decidable (SourceValid3X n low) := by
  unfold SourceValid3X; infer_instance

theorem sourceDen_neg_of_valid3X {n low : Source} (h : SourceValid3X n low) (hL : 0 < low.L) :
    sourceDen n low < 0 := by
  unfold SourceValid3X at h
  unfold sourceDen
  rw [sub_neg, lt_div_iff₀ hL]
  nlinarith

theorem sourceDen_ne_of_valid3X {n low : Source} (h : SourceValid3X n low) (hL : 0 < low.L) :
    sourceDen n low ≠ 0 :=
  (sourceDen_neg_of_valid3X h hL).ne

end QRH.MixedStep.Finite
