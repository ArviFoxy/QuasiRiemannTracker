/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node37
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node38 : Source := ⟨(4874407145171/5000000000000),(530699431993/156250000000),(97/2000),(58088219909/100000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node38_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node38_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node38_validC : SourceValidC node38 node37 (some node37) := by decide +kernel
theorem node38_highL : HighCertAt node38 node37 node37 8 (crossing node38 node37) node38_treesL := by
  decide +kernel
theorem node38_highR : HighCertAt node38 node37 node37 8 node38.cap node38_treesR := by
  decide +kernel
theorem node38_cell : CellRatio node38 node37 := by decide +kernel
theorem node38_valid : SourceValid2 node38 node37 (some node37) := by
  refine ⟨node38_validC, ?_, by decide +kernel, node38_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node38_highL⟩
  · exact ⟨_, node38_highR⟩
end QRH.RepeatedMarks.Finite
