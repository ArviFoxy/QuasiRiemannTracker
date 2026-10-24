/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node34
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node35 : Source := ⟨(9774683793993/10000000000000),(27165687831/7812500000),(47/1000),(593066871077/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node35_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p .leaf .leaf) .leaf)), (.p .leaf .leaf), (.p .leaf (.p (.p .leaf .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node35_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node35_validC : SourceValidC node35 node34 (some node34) := by decide +kernel
theorem node35_highL : HighCertAt node35 node34 node34 8 (crossing node35 node34) node35_treesL := by
  decide +kernel
theorem node35_highR : HighCertAt node35 node34 node34 8 node35.cap node35_treesR := by
  decide +kernel
theorem node35_cell : CellRatio node35 node34 := by decide +kernel
theorem node35_valid : SourceValid2 node35 node34 (some node34) := by
  refine ⟨node35_validC, ?_, by decide +kernel, node35_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node35_highL⟩
  · exact ⟨_, node35_highR⟩
end QRH.RepeatedMarks.Finite
