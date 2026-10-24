/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node43
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node44 : Source := ⟨(1211771889793/1250000000000),(32371352365813/10000000000000),(103/2000),(556856899057/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node44_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p .leaf .leaf) .leaf)), .leaf, (.p .leaf (.p (.p .leaf .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node44_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node44_validC : SourceValidC node44 node43 (some node43) := by decide +kernel
theorem node44_highL : HighCertAt node44 node43 node43 8 (crossing node44 node43) node44_treesL := by
  decide +kernel
theorem node44_highR : HighCertAt node44 node43 node43 8 node44.cap node44_treesR := by
  decide +kernel
theorem node44_cell : CellRatio node44 node43 := by decide +kernel
theorem node44_valid : SourceValid2 node44 node43 (some node43) := by
  refine ⟨node44_validC, ?_, by decide +kernel, node44_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node44_highL⟩
  · exact ⟨_, node44_highR⟩
end QRH.RepeatedMarks.Finite
