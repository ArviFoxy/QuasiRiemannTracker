/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node33
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node34 : Source := ⟨(9783822889137/10000000000000),(35066889944449/10000000000000),(93/2000),(298765750461/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node34_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node34_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node34_validC : SourceValidC node34 node33 (some node33) := by decide +kernel
theorem node34_highL : HighCertAt node34 node33 node33 8 (crossing node34 node33) node34_treesL := by
  decide +kernel
theorem node34_highR : HighCertAt node34 node33 node33 8 node34.cap node34_treesR := by
  decide +kernel
theorem node34_cell : CellRatio node34 node33 := by decide +kernel
theorem node34_valid : SourceValid2 node34 node33 (some node33) := by
  refine ⟨node34_validC, ?_, by decide +kernel, node34_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node34_highL⟩
  · exact ⟨_, node34_highR⟩
end QRH.RepeatedMarks.Finite
