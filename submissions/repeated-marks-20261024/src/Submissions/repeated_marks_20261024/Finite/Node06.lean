/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node05
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node06 : Source := ⟨(4983994663981/5000000000000),(42817594832713/10000000000000),(13/400),(357964057587/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node06_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node06_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node06_validC : SourceValidC node06 node05 (some node05) := by decide +kernel
theorem node06_highL : HighCertAt node06 node05 node05 8 (crossing node06 node05) node06_treesL := by
  decide +kernel
theorem node06_highR : HighCertAt node06 node05 node05 8 node06.cap node06_treesR := by
  decide +kernel
theorem node06_cell : CellRatio node06 node05 := by decide +kernel
theorem node06_valid : SourceValid2 node06 node05 (some node05) := by
  refine ⟨node06_validC, ?_, by decide +kernel, node06_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node06_highL⟩
  · exact ⟨_, node06_highR⟩
end QRH.RepeatedMarks.Finite
