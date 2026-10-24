/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node54
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node55 : Source := ⟨(2396781017053/2500000000000),(1849477929673/625000000000),(549989/10000000),(515046554473/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node55_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p (.p .leaf .leaf) .leaf), (.p .leaf .leaf), (.p (.p .leaf .leaf) .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node55_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, (.p .leaf (.p .leaf (.p .leaf (.p .leaf (.p (.p .leaf (.p .leaf (.p .leaf .leaf))) .leaf)))))]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node55_validC : SourceValidC node55 node54 (some node54) := by decide +kernel
theorem node55_highL : HighCertAt node55 node54 node54 8 (crossing node55 node54) node55_treesL := by
  decide +kernel
theorem node55_highR : HighCertAt node55 node54 node54 8 node55.cap node55_treesR := by
  decide +kernel
theorem node55_cell : CellRatio node55 node54 := by decide +kernel
theorem node55_valid : SourceValid2 node55 node54 (some node54) := by
  refine ⟨node55_validC, ?_, by decide +kernel, node55_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node55_highL⟩
  · exact ⟨_, node55_highR⟩
end QRH.RepeatedMarks.Finite
