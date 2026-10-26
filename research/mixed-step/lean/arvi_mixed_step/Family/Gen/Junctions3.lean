import Submissions.arvi_mixed_step.Family.Gen.Data3
import Submissions.arvi_mixed_step.Fan.Steps

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.MixedStep.Family
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless

def junction0_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction0_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction0_validC : SourceValidC3 (mpiece0.node3 0) QRH.MixedStep.Fan.fan46 QRH.MixedStep.Fan.fan46 := by decide +kernel
theorem junction0_highL : HighCertAt3 (mpiece0.node3 0) QRH.MixedStep.Fan.fan46 QRH.MixedStep.Fan.fan46 8 (crossing (mpiece0.node3 0) QRH.MixedStep.Fan.fan46) junction0_treesL := by
  decide +kernel
theorem junction0_highR : HighCertAt3 (mpiece0.node3 0) QRH.MixedStep.Fan.fan46 QRH.MixedStep.Fan.fan46 8 (mpiece0.node3 0).cap junction0_treesR := by
  decide +kernel
theorem junction0_cell : CellRatio3 (mpiece0.node3 0) QRH.MixedStep.Fan.fan46 := by decide +kernel
theorem junction0_valid : SourceValid3 (mpiece0.node3 0) QRH.MixedStep.Fan.fan46 QRH.MixedStep.Fan.fan46 := by
  refine sourceValid3_of_certs _ _ _ junction0_validC ?_ junction0_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction0_highL⟩
  · exact ⟨_, junction0_highR⟩

def junction1_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction1_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction1_validC : SourceValidC3 (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy)) (mpiece0.node3 (1 - mpiece0.Dy)) := by decide +kernel
theorem junction1_highL : HighCertAt3 (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy)) (mpiece0.node3 (1 - mpiece0.Dy)) 8 (crossing (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy))) junction1_treesL := by
  decide +kernel
theorem junction1_highR : HighCertAt3 (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy)) (mpiece0.node3 (1 - mpiece0.Dy)) 8 (mpiece1.node3 0).cap junction1_treesR := by
  decide +kernel
theorem junction1_cell : CellRatio3 (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy)) := by decide +kernel
theorem junction1_valid : SourceValid3 (mpiece1.node3 0) (mpiece0.node3 (1 - mpiece0.Dy)) (mpiece0.node3 (1 - mpiece0.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction1_validC ?_ junction1_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction1_highL⟩
  · exact ⟨_, junction1_highR⟩

def junction2_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction2_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction2_validC : SourceValidC3 (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy)) (mpiece1.node3 (1 - mpiece1.Dy)) := by decide +kernel
theorem junction2_highL : HighCertAt3 (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy)) (mpiece1.node3 (1 - mpiece1.Dy)) 8 (crossing (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy))) junction2_treesL := by
  decide +kernel
theorem junction2_highR : HighCertAt3 (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy)) (mpiece1.node3 (1 - mpiece1.Dy)) 8 (mpiece2.node3 0).cap junction2_treesR := by
  decide +kernel
theorem junction2_cell : CellRatio3 (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy)) := by decide +kernel
theorem junction2_valid : SourceValid3 (mpiece2.node3 0) (mpiece1.node3 (1 - mpiece1.Dy)) (mpiece1.node3 (1 - mpiece1.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction2_validC ?_ junction2_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction2_highL⟩
  · exact ⟨_, junction2_highR⟩

def junction3_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction3_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction3_validC : SourceValidC3 (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy)) (mpiece2.node3 (1 - mpiece2.Dy)) := by decide +kernel
theorem junction3_highL : HighCertAt3 (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy)) (mpiece2.node3 (1 - mpiece2.Dy)) 8 (crossing (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy))) junction3_treesL := by
  decide +kernel
theorem junction3_highR : HighCertAt3 (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy)) (mpiece2.node3 (1 - mpiece2.Dy)) 8 (mpiece3.node3 0).cap junction3_treesR := by
  decide +kernel
theorem junction3_cell : CellRatio3 (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy)) := by decide +kernel
theorem junction3_valid : SourceValid3 (mpiece3.node3 0) (mpiece2.node3 (1 - mpiece2.Dy)) (mpiece2.node3 (1 - mpiece2.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction3_validC ?_ junction3_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction3_highL⟩
  · exact ⟨_, junction3_highR⟩

def junction4_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction4_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction4_validC : SourceValidC3 (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy)) (mpiece3.node3 (1 - mpiece3.Dy)) := by decide +kernel
theorem junction4_highL : HighCertAt3 (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy)) (mpiece3.node3 (1 - mpiece3.Dy)) 8 (crossing (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy))) junction4_treesL := by
  decide +kernel
theorem junction4_highR : HighCertAt3 (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy)) (mpiece3.node3 (1 - mpiece3.Dy)) 8 (mpiece4.node3 0).cap junction4_treesR := by
  decide +kernel
theorem junction4_cell : CellRatio3 (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy)) := by decide +kernel
theorem junction4_valid : SourceValid3 (mpiece4.node3 0) (mpiece3.node3 (1 - mpiece3.Dy)) (mpiece3.node3 (1 - mpiece3.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction4_validC ?_ junction4_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction4_highL⟩
  · exact ⟨_, junction4_highR⟩

def junction5_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction5_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction5_validC : SourceValidC3 (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy)) (mpiece4.node3 (1 - mpiece4.Dy)) := by decide +kernel
theorem junction5_highL : HighCertAt3 (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy)) (mpiece4.node3 (1 - mpiece4.Dy)) 8 (crossing (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy))) junction5_treesL := by
  decide +kernel
theorem junction5_highR : HighCertAt3 (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy)) (mpiece4.node3 (1 - mpiece4.Dy)) 8 (mpiece5.node3 0).cap junction5_treesR := by
  decide +kernel
theorem junction5_cell : CellRatio3 (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy)) := by decide +kernel
theorem junction5_valid : SourceValid3 (mpiece5.node3 0) (mpiece4.node3 (1 - mpiece4.Dy)) (mpiece4.node3 (1 - mpiece4.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction5_validC ?_ junction5_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction5_highL⟩
  · exact ⟨_, junction5_highR⟩

def junction6_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction6_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction6_validC : SourceValidC3 (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy)) (mpiece5.node3 (1 - mpiece5.Dy)) := by decide +kernel
theorem junction6_highL : HighCertAt3 (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy)) (mpiece5.node3 (1 - mpiece5.Dy)) 8 (crossing (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy))) junction6_treesL := by
  decide +kernel
theorem junction6_highR : HighCertAt3 (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy)) (mpiece5.node3 (1 - mpiece5.Dy)) 8 (mpiece6.node3 0).cap junction6_treesR := by
  decide +kernel
theorem junction6_cell : CellRatio3 (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy)) := by decide +kernel
theorem junction6_valid : SourceValid3 (mpiece6.node3 0) (mpiece5.node3 (1 - mpiece5.Dy)) (mpiece5.node3 (1 - mpiece5.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction6_validC ?_ junction6_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction6_highL⟩
  · exact ⟨_, junction6_highR⟩

def junction7_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction7_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction7_validC : SourceValidC3 (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy)) (mpiece6.node3 (1 - mpiece6.Dy)) := by decide +kernel
theorem junction7_highL : HighCertAt3 (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy)) (mpiece6.node3 (1 - mpiece6.Dy)) 8 (crossing (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy))) junction7_treesL := by
  decide +kernel
theorem junction7_highR : HighCertAt3 (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy)) (mpiece6.node3 (1 - mpiece6.Dy)) 8 (mpiece7.node3 0).cap junction7_treesR := by
  decide +kernel
theorem junction7_cell : CellRatio3 (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy)) := by decide +kernel
theorem junction7_valid : SourceValid3 (mpiece7.node3 0) (mpiece6.node3 (1 - mpiece6.Dy)) (mpiece6.node3 (1 - mpiece6.Dy)) := by
  refine sourceValid3_of_certs _ _ _ junction7_validC ?_ junction7_cell
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction7_highL⟩
  · exact ⟨_, junction7_highR⟩


end QRH.MixedStep.Family
