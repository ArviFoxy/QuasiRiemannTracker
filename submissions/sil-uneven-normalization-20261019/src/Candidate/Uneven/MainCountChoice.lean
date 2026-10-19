/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountOldWindows
import Candidate.Uneven.MainCountGeometry
import Candidate.Target830.Physical.CountChoice

set_option autoImplicit false
namespace OAI.SevenEighths.MainDetectorCount
noncomputable section
open scoped Classical
open Target830

def window (stage : MainCount.Stage) : Fin 15 → MainCount.Window :=
  ![MainCount.Window.ofOld Count.window0,MainCount.Window.ofOld Count.window1,MainCount.Window.ofOld Count.window2,MainCount.Window.ofOld Count.window3,MainCount.Window.ofOld Count.window4,MainCount.Window.ofOld Count.window5,MainCount.Window.ofOld Count.window6,MainCount.Window.ofOld Count.window7,MainCount.Window.ofOld Count.window8,MainCount.Window.ofOld Count.window9,MainCount.window10 stage,MainCount.window11 stage,MainCount.window12 stage,MainCount.window13 stage,MainCount.window14 stage]

theorem window_admissible (stage : MainCount.Stage) (i : Fin 15) {d p : ℝ}
    (ha : (window stage i).Available d p) : MainCount.Admissible (window stage i).plane d p := by
  fin_cases i
  · exact MainCount.Window.ofOld_admissible Count.window0 (Count.window0_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window1 (Count.window1_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window2 (Count.window2_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window3 (Count.window3_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window4 (Count.window4_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window5 (Count.window5_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window6 (Count.window6_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window7 (Count.window7_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window8 (Count.window8_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window9 (Count.window9_admissible d p ha)
  · exact MainCount.window10_admissible stage d p ha
  · exact MainCount.window11_admissible stage d p ha
  · exact MainCount.window12_admissible stage d p ha
  · exact MainCount.window13_admissible stage d p ha
  · exact MainCount.window14_admissible stage d p ha

theorem window_supported (stage : MainCount.Stage) (i : Fin 15) :
    stage.Supports (window stage i).plane := by
  fin_cases i <;> simp [window,MainCount.Window.ofOld,MainCount.Stage.Supports,
    MainCount.Plane.ofOld,Count.window0,Count.window1,Count.window2,Count.window3,Count.window4,Count.window5,Count.window6,Count.window7,Count.window8,Count.window9,MainCount.window10,MainCount.window11,MainCount.window12,MainCount.window13,MainCount.window14]

theorem attained (stage : MainCount.Stage) (κ d p : ℝ) :
    MainCount.count stage κ d p=Count.oldCount κ d p ∨
      ∃i : Fin 15,(window stage i).Available d p ∧
        MainCount.count stage κ d p=Count.affineR (window stage i).plane.lambda (window stage i).plane.B d p := by
  rcases MainCount.count_attained stage κ d p with hold | ⟨b,hb,ha,he⟩
  · rcases Target830.Physical.DetectorCount.attained κ d p with hh | ⟨i,ha,he⟩
    · exact Or.inl (hold.trans hh)
    · right
      fin_cases i
      · exact ⟨0,ha,hold.trans he⟩
      · exact ⟨1,ha,hold.trans he⟩
      · exact ⟨2,ha,hold.trans he⟩
      · exact ⟨3,ha,hold.trans he⟩
      · exact ⟨4,ha,hold.trans he⟩
      · exact ⟨5,ha,hold.trans he⟩
      · exact ⟨6,ha,hold.trans he⟩
      · exact ⟨7,ha,hold.trans he⟩
      · exact ⟨8,ha,hold.trans he⟩
      · exact ⟨9,ha,hold.trans he⟩
  · right
    simp only [MainCount.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with hb | hb | hb | hb | hb <;> subst b
    · exact ⟨10,ha,he⟩
    · exact ⟨11,ha,he⟩
    · exact ⟨12,ha,he⟩
    · exact ⟨13,ha,he⟩
    · exact ⟨14,ha,he⟩

def choice (stage : MainCount.Stage) (κ d p : ℝ) : Option (Fin 15) :=
  if hh : MainCount.count stage κ d p=Count.oldCount κ d p then none
  else some (Classical.choose ((attained stage κ d p).resolve_left hh))

theorem choice_none (stage : MainCount.Stage) {κ d p : ℝ}
    (hh : choice stage κ d p=none) : MainCount.count stage κ d p=Count.oldCount κ d p := by
  by_cases he : MainCount.count stage κ d p=Count.oldCount κ d p
  · exact he
  · simpa [choice,he] using hh

theorem choice_some (stage : MainCount.Stage) {κ d p : ℝ} {i : Fin 15}
    (hh : choice stage κ d p=some i) : (window stage i).Available d p ∧
      MainCount.count stage κ d p=Count.affineR (window stage i).plane.lambda (window stage i).plane.B d p := by
  by_cases he : MainCount.count stage κ d p=Count.oldCount κ d p
  · simp [choice,he] at hh
  · have hi : Classical.choose ((attained stage κ d p).resolve_left he)=i := by
      simpa [choice,he] using hh
    rw [←hi]
    exact Classical.choose_spec ((attained stage κ d p).resolve_left he)

def cutoff (stage : MainCount.Stage) (d p κ : ℝ) : ℝ :=
  match choice stage κ d p with
  | none => Cycle25DetectorRowCount.cutoff d p κ
  | some i => MainCountArithmetic.tN (window stage i).plane d p

theorem cutoff_bounds (stage : MainCount.Stage) {d p κ : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 3/4) (hp : 0 ≤ p) (hphi : p ≤ 1/2)
    (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ cutoff stage d p κ ∧ cutoff stage d p κ ≤ 3/2 := by
  unfold cutoff
  split <;> rename_i hh
  · exact Cycle25DetectorRowCount.cutoff_bounds hd hdhi hp hphi hk
      (hkhi.trans (by norm_num [kappa0]))
  · have hg := MainCountArithmetic.admissible_geometry _
      (window_admissible stage _ (choice_some stage hh).1) hd hp hk hkhi
    exact ⟨hg.1,hg.2.1⟩

end
end OAI.SevenEighths.MainDetectorCount
#print axioms OAI.SevenEighths.MainDetectorCount.attained
#print axioms OAI.SevenEighths.MainDetectorCount.cutoff_bounds
