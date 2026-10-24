/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node52
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node53 : Source := ⟨(9607555161997/10000000000000),(15046291634169/5000000000000),(549989/10000000),(20902373407/40000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node53_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), (.p .leaf .leaf), (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node53_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node53_validC : SourceValidC node53 node52 (some node52) := by decide +kernel
theorem node53_highL : HighCertAt node53 node52 node52 8 (crossing node53 node52) node53_treesL := by
  decide +kernel
theorem node53_highR : HighCertAt node53 node52 node52 8 node53.cap node53_treesR := by
  decide +kernel
theorem node53_cell : CellRatio node53 node52 := by decide +kernel
theorem node53_valid : SourceValid2 node53 node52 (some node52) := by
  refine ⟨node53_validC, ?_, by decide +kernel, node53_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node53_highL⟩
  · exact ⟨_, node53_highR⟩
end QRH.RepeatedMarks.Finite
