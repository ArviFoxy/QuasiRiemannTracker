/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node30
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node31 : Source := ⟨(9808361219421/10000000000000),(8971213120859/2500000000000),(9/200),(609898093433/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node31_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node31_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node31_validC : SourceValidC node31 node30 (some node30) := by decide +kernel
theorem node31_highL : HighCertAt node31 node30 node30 8 (crossing node31 node30) node31_treesL := by
  decide +kernel
theorem node31_highR : HighCertAt node31 node30 node30 8 node31.cap node31_treesR := by
  decide +kernel
theorem node31_cell : CellRatio node31 node30 := by decide +kernel
theorem node31_valid : SourceValid2 node31 node30 (some node30) := by
  refine ⟨node31_validC, ?_, by decide +kernel, node31_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node31_highL⟩
  · exact ⟨_, node31_highR⟩
end QRH.RepeatedMarks.Finite
