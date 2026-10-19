/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointStageParameters
import Candidate.Uneven.WarmupCountIncumbent
import Candidate.Uneven.RoundedCountIncumbent

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.UnevenEndpoint.Count
noncomputable section
variable [config : Configuration]

def count (κ d p : ℝ) : ℝ := MainCount.count config.stage κ d p
def d0 : ℝ := 1/200
def rowBase (d cap δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+d*(1/4-17/50)-δ*p*cap/2
def rowAt (κ d cap δ p : ℝ) : ℝ := rowBase d cap δ p+3*d*count κ δ p/4
def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)
def newCapacity (d : ℝ) : ℝ :=
  min (slotClip*d) ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda)
def oldExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (oldCapacityAt κ d) δ p
def newExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (newCapacity d) δ p

theorem old_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hinc : β ≤ incumbent) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β ≤ -reserve-(β-theta) := by
  cases config with
  | mk stage =>
    cases stage
    · have hb' : Sil.Uneven.WarmupRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.WarmupRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.WarmupRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.WarmupRows.rowHeight 0 ≤ d ∧ d ≤ Sil.Uneven.WarmupRows.rowHeight 1 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.WarmupRows.old_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,oldExponentAt,oldCapacityAt,h,ell,y,theta,slotClip,reserve,Sil.Uneven.WarmupRows.reserve,Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda,Sil.Uneven.WarmupRows.scalarRow,Sil.Uneven.WarmupRows.rowConstant,Sil.Uneven.WarmupRows.oldCapacityAt,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.ell,Sil.Uneven.WarmupRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

    · have hb' : Sil.Uneven.RoundedRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.RoundedRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.RoundedRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.RoundedRows.rowHeight 0 ≤ d ∧ d ≤ Sil.Uneven.RoundedRows.rowHeight 1 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.RoundedRows.old_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,oldExponentAt,oldCapacityAt,h,ell,y,theta,slotClip,reserve,Sil.Uneven.RoundedRows.scalarRow,Sil.Uneven.RoundedRows.rowConstant,Sil.Uneven.RoundedRows.oldCapacityAt,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.ell,Sil.Uneven.RoundedRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

theorem new_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hinc : β ≤ incumbent) (hd : d ∈ Set.Icc dMinus dPlus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β ≤ -reserve-(β-theta) := by
  cases config with
  | mk stage =>
    cases stage
    · have hb' : Sil.Uneven.WarmupRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.WarmupRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.WarmupRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.WarmupRows.rowHeight 2 ≤ d ∧ d ≤ Sil.Uneven.WarmupRows.rowHeight 3 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.WarmupRows.new_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,newExponentAt,newCapacity,h,ell,y,theta,slotClip,reserve,Sil.Uneven.WarmupRows.reserve,Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda,Sil.Uneven.WarmupRows.scalarRow,Sil.Uneven.WarmupRows.rowConstant,Sil.Uneven.WarmupRows.newCapacity,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.ell,Sil.Uneven.WarmupRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

    · have hb' : Sil.Uneven.RoundedRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.RoundedRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.RoundedRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.RoundedRows.rowHeight 2 ≤ d ∧ d ≤ Sil.Uneven.RoundedRows.rowHeight 3 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.RoundedRows.new_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,newExponentAt,newCapacity,h,ell,y,theta,slotClip,reserve,Sil.Uneven.RoundedRows.scalarRow,Sil.Uneven.RoundedRows.rowConstant,Sil.Uneven.RoundedRows.newCapacity,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.ell,Sil.Uneven.RoundedRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda,Sil.Uneven.Critical.physicalB,Sil.Uneven.Critical.physicalLambda] <;> ring_nf <;> simp

end
end OAI.SevenEighths.UnevenEndpoint.Count
#print axioms OAI.SevenEighths.UnevenEndpoint.Count.old_supremum_deficit
#print axioms OAI.SevenEighths.UnevenEndpoint.Count.new_supremum_deficit
