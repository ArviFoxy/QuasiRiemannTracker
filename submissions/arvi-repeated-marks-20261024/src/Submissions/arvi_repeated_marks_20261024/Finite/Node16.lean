/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node15
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node16 : Source := ⟨(4957228341791/5000000000000),(8008856312271/2000000000000),(3/80),(16829434357/25000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node16_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node16_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node16_validC : SourceValidC node16 node15 (some node15) := by decide +kernel
theorem node16_highL : HighCertAt node16 node15 node15 8 (crossing node16 node15) node16_treesL := by
  decide +kernel
theorem node16_highR : HighCertAt node16 node15 node15 8 node16.cap node16_treesR := by
  decide +kernel
theorem node16_cell : CellRatio node16 node15 := by decide +kernel
theorem node16_valid : SourceValid2 node16 node15 (some node15) := by
  refine ⟨node16_validC, ?_, by decide +kernel, node16_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node16_highL⟩
  · exact ⟨_, node16_highR⟩
end QRH.RepeatedMarks.Finite
