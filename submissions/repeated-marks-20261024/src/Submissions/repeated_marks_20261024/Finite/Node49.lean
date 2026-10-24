/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node48
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node49 : Source := ⟨(9646618592717/10000000000000),(3885863667333/1250000000000),(27/500),(537503572389/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node49_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node49_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node49_validC : SourceValidC node49 node48 (some node48) := by decide +kernel
theorem node49_highL : HighCertAt node49 node48 node48 8 (crossing node49 node48) node49_treesL := by
  decide +kernel
theorem node49_highR : HighCertAt node49 node48 node48 8 node49.cap node49_treesR := by
  decide +kernel
theorem node49_cell : CellRatio node49 node48 := by decide +kernel
theorem node49_valid : SourceValid2 node49 node48 (some node48) := by
  refine ⟨node49_validC, ?_, by decide +kernel, node49_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node49_highL⟩
  · exact ⟨_, node49_highR⟩
end QRH.RepeatedMarks.Finite
