/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node00
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node01 : Source := ⟨(79911905709/80000000000),(22085066342687/5000000000000),(3/100),(737012945907/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node01_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node01_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node01_validC : SourceValidC node01 node00 (some node00) := by decide +kernel
theorem node01_highL : HighCertAt node01 node00 node00 8 (crossing node01 node00) node01_treesL := by
  decide +kernel
theorem node01_highR : HighCertAt node01 node00 node00 8 node01.cap node01_treesR := by
  decide +kernel
theorem node01_cell : CellRatio node01 node00 := by decide +kernel
theorem node01_valid : SourceValid2 node01 node00 (some node00) := by
  refine ⟨node01_validC, ?_, by decide +kernel, node01_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node01_highL⟩
  · exact ⟨_, node01_highR⟩
end QRH.RepeatedMarks.Finite
