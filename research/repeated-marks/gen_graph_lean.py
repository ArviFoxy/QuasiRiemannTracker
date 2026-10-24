"""Emit the graph induction (Graph/Chain.lean) over the 59 repeated-mark nodes.

usage: python3 gen_graph_lean.py NNODES IC IP OUTDIR
Node k is SourceValid2 with LOW = HIGH = node k-1 (node 0: Collet's natural source)."""
import sys, os

PKG = 'Submissions.repeated_marks_20261024'
CPKG = 'Submissions.hailey_collet_1252270103'


def main():
    nn, iC, iP, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    os.makedirs(os.path.join(out, 'Graph'), exist_ok=True)
    L = ['/- Repeated marks: the finite induction over the repeated-mark source graph.',
         'Each node is `SourceValid2` with its predecessor as LOW and HIGH parent; the first parent is',
         "Collet's natural source (Record1252270103Graph/Natural.lean, Apache-2.0). -/",
         f'import {CPKG}.Record1252270103Graph.FinalSources']
    L += [f'import {PKG}.Finite.Node{k:02d}' for k in range(nn)]
    L += ['set_option autoImplicit false', 'set_option maxHeartbeats 400000',
          'namespace QRH.RepeatedMarks.Graph', 'noncomputable section',
          'open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite',
          '',
          '/-- The source step of the repeated-mark graph: a HIGH parent is always present. -/',
          'def NFStep2 : Prop := ∀ n low h : Source,',
          ' (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤finalK →',
          ' SourceValid2 n low (some h) → ParentGood low → NFAccounting n →',
          ' P low → P h → P n',
          '',
          'lemma parent_good_of_valid2 {n low : Source} {h : Option Source}',
          ' (hv : SourceValid2 n low h) : ParentGood n :=',
          ' ⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.1.2.2.2.1,hv.1.2.2.2.2.1⟩',
          '',
          'theorem chain_sources (step : NFStep2) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)',
          f' (hk : 6*(2*HeckeZeroSupremum.beta-1)≤finalK) : P node{iC:02d} ∧ P node{iP:02d} := by',
          ' have p_natural : P natural := by',
          '  simpa [P,natural,finalK] using natural_global_source finalK',
          '   (by norm_num [finalK]) (by norm_num [finalK]) hβ hk',
          ' have g_natural : ParentGood natural := by norm_num [ParentGood,natural]']
    prev = 'natural'
    for k in range(nn):
        nm = f'node{k:02d}'
        L += [f' have p_{nm} : P {nm} := step {nm} {prev} {prev} hβ hk {nm}_valid g_{prev}',
              f'  (Or.inl (by norm_num [{nm}])) p_{prev} p_{prev}',
              f' have g_{nm} : ParentGood {nm} := parent_good_of_valid2 {nm}_valid']
        prev = nm
    L += [f' exact ⟨p_node{iC:02d},p_node{iP:02d}⟩', 'end', 'end QRH.RepeatedMarks.Graph', '']
    open(os.path.join(out, 'Graph', 'Chain.lean'), 'w').write('\n'.join(L))


if __name__ == '__main__':
    main()
