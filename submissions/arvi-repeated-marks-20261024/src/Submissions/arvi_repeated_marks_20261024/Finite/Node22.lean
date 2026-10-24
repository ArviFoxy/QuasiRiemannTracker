/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node21
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node22 : Source := ⟨(987610832943/1000000000000),(1535809595223/400000000000),(81/2000),(80998779663/125000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node22_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node22_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node22_validC : SourceValidC node22 node21 (some node21) := by decide +kernel
theorem node22_highL : HighCertAt node22 node21 node21 8 (crossing node22 node21) node22_treesL := by
  decide +kernel
theorem node22_highR : HighCertAt node22 node21 node21 8 node22.cap node22_treesR := by
  decide +kernel
theorem node22_cell : CellRatio node22 node21 := by decide +kernel
theorem node22_valid : SourceValid2 node22 node21 (some node21) := by
  refine ⟨node22_validC, ?_, by decide +kernel, node22_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node22_highL⟩
  · exact ⟨_, node22_highR⟩
end QRH.RepeatedMarks.Finite
