/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node02
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node03 : Source := ⟨(249536045041/250000000000),(43658498187001/10000000000000),(31/1000),(729023218173/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node03_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node03_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node03_validC : SourceValidC node03 node02 (some node02) := by decide +kernel
theorem node03_highL : HighCertAt node03 node02 node02 8 (crossing node03 node02) node03_treesL := by
  decide +kernel
theorem node03_highR : HighCertAt node03 node02 node02 8 node03.cap node03_treesR := by
  decide +kernel
theorem node03_cell : CellRatio node03 node02 := by decide +kernel
theorem node03_valid : SourceValid2 node03 node02 (some node02) := by
  refine ⟨node03_validC, ?_, by decide +kernel, node03_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node03_highL⟩
  · exact ⟨_, node03_highR⟩
end QRH.RepeatedMarks.Finite
