/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node03
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node04 : Source := ⟨(4988746950207/5000000000000),(1085094872053/250000000000),(63/2000),(181265272717/250000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node04_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node04_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node04_validC : SourceValidC node04 node03 (some node03) := by decide +kernel
theorem node04_highL : HighCertAt node04 node03 node03 8 (crossing node04 node03) node04_treesL := by
  decide +kernel
theorem node04_highR : HighCertAt node04 node03 node03 8 node04.cap node04_treesR := by
  decide +kernel
theorem node04_cell : CellRatio node04 node03 := by decide +kernel
theorem node04_valid : SourceValid2 node04 node03 (some node03) := by
  refine ⟨node04_validC, ?_, by decide +kernel, node04_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node04_highL⟩
  · exact ⟨_, node04_highR⟩
end QRH.RepeatedMarks.Finite
