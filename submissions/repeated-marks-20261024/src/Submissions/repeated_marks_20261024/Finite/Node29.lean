/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node28
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node29 : Source := ⟨(2455873166563/2500000000000),(36410522240789/10000000000000),(11/250),(617844210317/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node29_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), (.p .leaf .leaf), (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node29_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node29_validC : SourceValidC node29 node28 (some node28) := by decide +kernel
theorem node29_highL : HighCertAt node29 node28 node28 8 (crossing node29 node28) node29_treesL := by
  decide +kernel
theorem node29_highR : HighCertAt node29 node28 node28 8 node29.cap node29_treesR := by
  decide +kernel
theorem node29_cell : CellRatio node29 node28 := by decide +kernel
theorem node29_valid : SourceValid2 node29 node28 (some node28) := by
  refine ⟨node29_validC, ?_, by decide +kernel, node29_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node29_highL⟩
  · exact ⟨_, node29_highR⟩
end QRH.RepeatedMarks.Finite
