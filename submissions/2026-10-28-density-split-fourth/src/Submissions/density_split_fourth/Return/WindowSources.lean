/- Repeated marks: fork of Collet's final-stage module WindowSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): three branches; the count face C supplies the `C` windows and the
physical face P the capped `capP` windows (literal `Restricts`); unused corollaries removed. -/
import Submissions.density_split_fourth.Return.SourceInlet
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

def countingSource (b:CountBranch) : SourceFace :=
 broadFace (branchB b) (branchL b) (branchCap b)
def sourceSupplier (b:CountBranch) : SourceFace :=
 match b with
 | .fourthC => fourthCountGlobal
 | _ => countGlobal

theorem supplier_restricts_counting (b:CountBranch) (hb:b≠.old) :
 (sourceSupplier b).Restricts (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (constructor <;>
  norm_num [sourceSupplier,countingSource,broadFace,countGlobal,fourthCountGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,countCap,parentCapB,parentCapLambda,
   fourthCountB,fourthCountL,physicalCap])
end
end QRH.DensitySplitThird.Return
