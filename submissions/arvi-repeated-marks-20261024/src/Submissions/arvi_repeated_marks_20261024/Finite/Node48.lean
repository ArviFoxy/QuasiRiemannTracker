/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node47
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node48 : Source := ⟨(9657410425921/10000000000000),(3921363118659/1250000000000),(107/2000),(541694531097/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node48_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node48_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node48_validC : SourceValidC node48 node47 (some node47) := by decide +kernel
theorem node48_highL : HighCertAt node48 node47 node47 8 (crossing node48 node47) node48_treesL := by
  decide +kernel
theorem node48_highR : HighCertAt node48 node47 node47 8 node48.cap node48_treesR := by
  decide +kernel
theorem node48_cell : CellRatio node48 node47 := by decide +kernel
theorem node48_valid : SourceValid2 node48 node47 (some node47) := by
  refine ⟨node48_validC, ?_, by decide +kernel, node48_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node48_highL⟩
  · exact ⟨_, node48_highR⟩
end QRH.RepeatedMarks.Finite
