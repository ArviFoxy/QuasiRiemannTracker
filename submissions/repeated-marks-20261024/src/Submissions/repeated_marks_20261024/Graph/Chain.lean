/- Repeated marks: the finite induction over the repeated-mark source graph.
Each node is `SourceValid2` with its predecessor as LOW and HIGH parent; the first parent is
Collet's natural source (Record1252270103Graph/Natural.lean, Apache-2.0). -/
import Submissions.hailey_collet_1252270103.Record1252270103Graph.FinalSources
import Submissions.repeated_marks_20261024.Finite.Node00
import Submissions.repeated_marks_20261024.Finite.Node01
import Submissions.repeated_marks_20261024.Finite.Node02
import Submissions.repeated_marks_20261024.Finite.Node03
import Submissions.repeated_marks_20261024.Finite.Node04
import Submissions.repeated_marks_20261024.Finite.Node05
import Submissions.repeated_marks_20261024.Finite.Node06
import Submissions.repeated_marks_20261024.Finite.Node07
import Submissions.repeated_marks_20261024.Finite.Node08
import Submissions.repeated_marks_20261024.Finite.Node09
import Submissions.repeated_marks_20261024.Finite.Node10
import Submissions.repeated_marks_20261024.Finite.Node11
import Submissions.repeated_marks_20261024.Finite.Node12
import Submissions.repeated_marks_20261024.Finite.Node13
import Submissions.repeated_marks_20261024.Finite.Node14
import Submissions.repeated_marks_20261024.Finite.Node15
import Submissions.repeated_marks_20261024.Finite.Node16
import Submissions.repeated_marks_20261024.Finite.Node17
import Submissions.repeated_marks_20261024.Finite.Node18
import Submissions.repeated_marks_20261024.Finite.Node19
import Submissions.repeated_marks_20261024.Finite.Node20
import Submissions.repeated_marks_20261024.Finite.Node21
import Submissions.repeated_marks_20261024.Finite.Node22
import Submissions.repeated_marks_20261024.Finite.Node23
import Submissions.repeated_marks_20261024.Finite.Node24
import Submissions.repeated_marks_20261024.Finite.Node25
import Submissions.repeated_marks_20261024.Finite.Node26
import Submissions.repeated_marks_20261024.Finite.Node27
import Submissions.repeated_marks_20261024.Finite.Node28
import Submissions.repeated_marks_20261024.Finite.Node29
import Submissions.repeated_marks_20261024.Finite.Node30
import Submissions.repeated_marks_20261024.Finite.Node31
import Submissions.repeated_marks_20261024.Finite.Node32
import Submissions.repeated_marks_20261024.Finite.Node33
import Submissions.repeated_marks_20261024.Finite.Node34
import Submissions.repeated_marks_20261024.Finite.Node35
import Submissions.repeated_marks_20261024.Finite.Node36
import Submissions.repeated_marks_20261024.Finite.Node37
import Submissions.repeated_marks_20261024.Finite.Node38
import Submissions.repeated_marks_20261024.Finite.Node39
import Submissions.repeated_marks_20261024.Finite.Node40
import Submissions.repeated_marks_20261024.Finite.Node41
import Submissions.repeated_marks_20261024.Finite.Node42
import Submissions.repeated_marks_20261024.Finite.Node43
import Submissions.repeated_marks_20261024.Finite.Node44
import Submissions.repeated_marks_20261024.Finite.Node45
import Submissions.repeated_marks_20261024.Finite.Node46
import Submissions.repeated_marks_20261024.Finite.Node47
import Submissions.repeated_marks_20261024.Finite.Node48
import Submissions.repeated_marks_20261024.Finite.Node49
import Submissions.repeated_marks_20261024.Finite.Node50
import Submissions.repeated_marks_20261024.Finite.Node51
import Submissions.repeated_marks_20261024.Finite.Node52
import Submissions.repeated_marks_20261024.Finite.Node53
import Submissions.repeated_marks_20261024.Finite.Node54
import Submissions.repeated_marks_20261024.Finite.Node55
import Submissions.repeated_marks_20261024.Finite.Node56
import Submissions.repeated_marks_20261024.Finite.Node57
import Submissions.repeated_marks_20261024.Finite.Node58
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite

/-- The source step of the repeated-mark graph: a HIGH parent is always present. -/
def NFStep2 : Prop := ∀ n low h : Source,
 (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤finalK →
 SourceValid2 n low (some h) → ParentGood low → NFAccounting n →
 P low → P h → P n

lemma parent_good_of_valid2 {n low : Source} {h : Option Source}
 (hv : SourceValid2 n low h) : ParentGood n :=
 ⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.1.2.2.2.1,hv.1.2.2.2.2.1⟩

theorem chain_sources (step : NFStep2) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
 (hk : 6*(2*HeckeZeroSupremum.beta-1)≤finalK) : P node58 ∧ P node52 := by
 have p_natural : P natural := by
  simpa [P,natural,finalK] using natural_global_source finalK
   (by norm_num [finalK]) (by norm_num [finalK]) hβ hk
 have g_natural : ParentGood natural := by norm_num [ParentGood,natural]
 have p_node00 : P node00 := step node00 natural natural hβ hk node00_valid g_natural
  (Or.inl (by norm_num [node00])) p_natural p_natural
 have g_node00 : ParentGood node00 := parent_good_of_valid2 node00_valid
 have p_node01 : P node01 := step node01 node00 node00 hβ hk node01_valid g_node00
  (Or.inl (by norm_num [node01])) p_node00 p_node00
 have g_node01 : ParentGood node01 := parent_good_of_valid2 node01_valid
 have p_node02 : P node02 := step node02 node01 node01 hβ hk node02_valid g_node01
  (Or.inl (by norm_num [node02])) p_node01 p_node01
 have g_node02 : ParentGood node02 := parent_good_of_valid2 node02_valid
 have p_node03 : P node03 := step node03 node02 node02 hβ hk node03_valid g_node02
  (Or.inl (by norm_num [node03])) p_node02 p_node02
 have g_node03 : ParentGood node03 := parent_good_of_valid2 node03_valid
 have p_node04 : P node04 := step node04 node03 node03 hβ hk node04_valid g_node03
  (Or.inl (by norm_num [node04])) p_node03 p_node03
 have g_node04 : ParentGood node04 := parent_good_of_valid2 node04_valid
 have p_node05 : P node05 := step node05 node04 node04 hβ hk node05_valid g_node04
  (Or.inl (by norm_num [node05])) p_node04 p_node04
 have g_node05 : ParentGood node05 := parent_good_of_valid2 node05_valid
 have p_node06 : P node06 := step node06 node05 node05 hβ hk node06_valid g_node05
  (Or.inl (by norm_num [node06])) p_node05 p_node05
 have g_node06 : ParentGood node06 := parent_good_of_valid2 node06_valid
 have p_node07 : P node07 := step node07 node06 node06 hβ hk node07_valid g_node06
  (Or.inl (by norm_num [node07])) p_node06 p_node06
 have g_node07 : ParentGood node07 := parent_good_of_valid2 node07_valid
 have p_node08 : P node08 := step node08 node07 node07 hβ hk node08_valid g_node07
  (Or.inl (by norm_num [node08])) p_node07 p_node07
 have g_node08 : ParentGood node08 := parent_good_of_valid2 node08_valid
 have p_node09 : P node09 := step node09 node08 node08 hβ hk node09_valid g_node08
  (Or.inl (by norm_num [node09])) p_node08 p_node08
 have g_node09 : ParentGood node09 := parent_good_of_valid2 node09_valid
 have p_node10 : P node10 := step node10 node09 node09 hβ hk node10_valid g_node09
  (Or.inl (by norm_num [node10])) p_node09 p_node09
 have g_node10 : ParentGood node10 := parent_good_of_valid2 node10_valid
 have p_node11 : P node11 := step node11 node10 node10 hβ hk node11_valid g_node10
  (Or.inl (by norm_num [node11])) p_node10 p_node10
 have g_node11 : ParentGood node11 := parent_good_of_valid2 node11_valid
 have p_node12 : P node12 := step node12 node11 node11 hβ hk node12_valid g_node11
  (Or.inl (by norm_num [node12])) p_node11 p_node11
 have g_node12 : ParentGood node12 := parent_good_of_valid2 node12_valid
 have p_node13 : P node13 := step node13 node12 node12 hβ hk node13_valid g_node12
  (Or.inl (by norm_num [node13])) p_node12 p_node12
 have g_node13 : ParentGood node13 := parent_good_of_valid2 node13_valid
 have p_node14 : P node14 := step node14 node13 node13 hβ hk node14_valid g_node13
  (Or.inl (by norm_num [node14])) p_node13 p_node13
 have g_node14 : ParentGood node14 := parent_good_of_valid2 node14_valid
 have p_node15 : P node15 := step node15 node14 node14 hβ hk node15_valid g_node14
  (Or.inl (by norm_num [node15])) p_node14 p_node14
 have g_node15 : ParentGood node15 := parent_good_of_valid2 node15_valid
 have p_node16 : P node16 := step node16 node15 node15 hβ hk node16_valid g_node15
  (Or.inl (by norm_num [node16])) p_node15 p_node15
 have g_node16 : ParentGood node16 := parent_good_of_valid2 node16_valid
 have p_node17 : P node17 := step node17 node16 node16 hβ hk node17_valid g_node16
  (Or.inl (by norm_num [node17])) p_node16 p_node16
 have g_node17 : ParentGood node17 := parent_good_of_valid2 node17_valid
 have p_node18 : P node18 := step node18 node17 node17 hβ hk node18_valid g_node17
  (Or.inl (by norm_num [node18])) p_node17 p_node17
 have g_node18 : ParentGood node18 := parent_good_of_valid2 node18_valid
 have p_node19 : P node19 := step node19 node18 node18 hβ hk node19_valid g_node18
  (Or.inl (by norm_num [node19])) p_node18 p_node18
 have g_node19 : ParentGood node19 := parent_good_of_valid2 node19_valid
 have p_node20 : P node20 := step node20 node19 node19 hβ hk node20_valid g_node19
  (Or.inl (by norm_num [node20])) p_node19 p_node19
 have g_node20 : ParentGood node20 := parent_good_of_valid2 node20_valid
 have p_node21 : P node21 := step node21 node20 node20 hβ hk node21_valid g_node20
  (Or.inl (by norm_num [node21])) p_node20 p_node20
 have g_node21 : ParentGood node21 := parent_good_of_valid2 node21_valid
 have p_node22 : P node22 := step node22 node21 node21 hβ hk node22_valid g_node21
  (Or.inl (by norm_num [node22])) p_node21 p_node21
 have g_node22 : ParentGood node22 := parent_good_of_valid2 node22_valid
 have p_node23 : P node23 := step node23 node22 node22 hβ hk node23_valid g_node22
  (Or.inl (by norm_num [node23])) p_node22 p_node22
 have g_node23 : ParentGood node23 := parent_good_of_valid2 node23_valid
 have p_node24 : P node24 := step node24 node23 node23 hβ hk node24_valid g_node23
  (Or.inl (by norm_num [node24])) p_node23 p_node23
 have g_node24 : ParentGood node24 := parent_good_of_valid2 node24_valid
 have p_node25 : P node25 := step node25 node24 node24 hβ hk node25_valid g_node24
  (Or.inl (by norm_num [node25])) p_node24 p_node24
 have g_node25 : ParentGood node25 := parent_good_of_valid2 node25_valid
 have p_node26 : P node26 := step node26 node25 node25 hβ hk node26_valid g_node25
  (Or.inl (by norm_num [node26])) p_node25 p_node25
 have g_node26 : ParentGood node26 := parent_good_of_valid2 node26_valid
 have p_node27 : P node27 := step node27 node26 node26 hβ hk node27_valid g_node26
  (Or.inl (by norm_num [node27])) p_node26 p_node26
 have g_node27 : ParentGood node27 := parent_good_of_valid2 node27_valid
 have p_node28 : P node28 := step node28 node27 node27 hβ hk node28_valid g_node27
  (Or.inl (by norm_num [node28])) p_node27 p_node27
 have g_node28 : ParentGood node28 := parent_good_of_valid2 node28_valid
 have p_node29 : P node29 := step node29 node28 node28 hβ hk node29_valid g_node28
  (Or.inl (by norm_num [node29])) p_node28 p_node28
 have g_node29 : ParentGood node29 := parent_good_of_valid2 node29_valid
 have p_node30 : P node30 := step node30 node29 node29 hβ hk node30_valid g_node29
  (Or.inl (by norm_num [node30])) p_node29 p_node29
 have g_node30 : ParentGood node30 := parent_good_of_valid2 node30_valid
 have p_node31 : P node31 := step node31 node30 node30 hβ hk node31_valid g_node30
  (Or.inl (by norm_num [node31])) p_node30 p_node30
 have g_node31 : ParentGood node31 := parent_good_of_valid2 node31_valid
 have p_node32 : P node32 := step node32 node31 node31 hβ hk node32_valid g_node31
  (Or.inl (by norm_num [node32])) p_node31 p_node31
 have g_node32 : ParentGood node32 := parent_good_of_valid2 node32_valid
 have p_node33 : P node33 := step node33 node32 node32 hβ hk node33_valid g_node32
  (Or.inl (by norm_num [node33])) p_node32 p_node32
 have g_node33 : ParentGood node33 := parent_good_of_valid2 node33_valid
 have p_node34 : P node34 := step node34 node33 node33 hβ hk node34_valid g_node33
  (Or.inl (by norm_num [node34])) p_node33 p_node33
 have g_node34 : ParentGood node34 := parent_good_of_valid2 node34_valid
 have p_node35 : P node35 := step node35 node34 node34 hβ hk node35_valid g_node34
  (Or.inl (by norm_num [node35])) p_node34 p_node34
 have g_node35 : ParentGood node35 := parent_good_of_valid2 node35_valid
 have p_node36 : P node36 := step node36 node35 node35 hβ hk node36_valid g_node35
  (Or.inl (by norm_num [node36])) p_node35 p_node35
 have g_node36 : ParentGood node36 := parent_good_of_valid2 node36_valid
 have p_node37 : P node37 := step node37 node36 node36 hβ hk node37_valid g_node36
  (Or.inl (by norm_num [node37])) p_node36 p_node36
 have g_node37 : ParentGood node37 := parent_good_of_valid2 node37_valid
 have p_node38 : P node38 := step node38 node37 node37 hβ hk node38_valid g_node37
  (Or.inl (by norm_num [node38])) p_node37 p_node37
 have g_node38 : ParentGood node38 := parent_good_of_valid2 node38_valid
 have p_node39 : P node39 := step node39 node38 node38 hβ hk node39_valid g_node38
  (Or.inl (by norm_num [node39])) p_node38 p_node38
 have g_node39 : ParentGood node39 := parent_good_of_valid2 node39_valid
 have p_node40 : P node40 := step node40 node39 node39 hβ hk node40_valid g_node39
  (Or.inl (by norm_num [node40])) p_node39 p_node39
 have g_node40 : ParentGood node40 := parent_good_of_valid2 node40_valid
 have p_node41 : P node41 := step node41 node40 node40 hβ hk node41_valid g_node40
  (Or.inl (by norm_num [node41])) p_node40 p_node40
 have g_node41 : ParentGood node41 := parent_good_of_valid2 node41_valid
 have p_node42 : P node42 := step node42 node41 node41 hβ hk node42_valid g_node41
  (Or.inl (by norm_num [node42])) p_node41 p_node41
 have g_node42 : ParentGood node42 := parent_good_of_valid2 node42_valid
 have p_node43 : P node43 := step node43 node42 node42 hβ hk node43_valid g_node42
  (Or.inl (by norm_num [node43])) p_node42 p_node42
 have g_node43 : ParentGood node43 := parent_good_of_valid2 node43_valid
 have p_node44 : P node44 := step node44 node43 node43 hβ hk node44_valid g_node43
  (Or.inl (by norm_num [node44])) p_node43 p_node43
 have g_node44 : ParentGood node44 := parent_good_of_valid2 node44_valid
 have p_node45 : P node45 := step node45 node44 node44 hβ hk node45_valid g_node44
  (Or.inl (by norm_num [node45])) p_node44 p_node44
 have g_node45 : ParentGood node45 := parent_good_of_valid2 node45_valid
 have p_node46 : P node46 := step node46 node45 node45 hβ hk node46_valid g_node45
  (Or.inl (by norm_num [node46])) p_node45 p_node45
 have g_node46 : ParentGood node46 := parent_good_of_valid2 node46_valid
 have p_node47 : P node47 := step node47 node46 node46 hβ hk node47_valid g_node46
  (Or.inl (by norm_num [node47])) p_node46 p_node46
 have g_node47 : ParentGood node47 := parent_good_of_valid2 node47_valid
 have p_node48 : P node48 := step node48 node47 node47 hβ hk node48_valid g_node47
  (Or.inl (by norm_num [node48])) p_node47 p_node47
 have g_node48 : ParentGood node48 := parent_good_of_valid2 node48_valid
 have p_node49 : P node49 := step node49 node48 node48 hβ hk node49_valid g_node48
  (Or.inl (by norm_num [node49])) p_node48 p_node48
 have g_node49 : ParentGood node49 := parent_good_of_valid2 node49_valid
 have p_node50 : P node50 := step node50 node49 node49 hβ hk node50_valid g_node49
  (Or.inl (by norm_num [node50])) p_node49 p_node49
 have g_node50 : ParentGood node50 := parent_good_of_valid2 node50_valid
 have p_node51 : P node51 := step node51 node50 node50 hβ hk node51_valid g_node50
  (Or.inl (by norm_num [node51])) p_node50 p_node50
 have g_node51 : ParentGood node51 := parent_good_of_valid2 node51_valid
 have p_node52 : P node52 := step node52 node51 node51 hβ hk node52_valid g_node51
  (Or.inl (by norm_num [node52])) p_node51 p_node51
 have g_node52 : ParentGood node52 := parent_good_of_valid2 node52_valid
 have p_node53 : P node53 := step node53 node52 node52 hβ hk node53_valid g_node52
  (Or.inl (by norm_num [node53])) p_node52 p_node52
 have g_node53 : ParentGood node53 := parent_good_of_valid2 node53_valid
 have p_node54 : P node54 := step node54 node53 node53 hβ hk node54_valid g_node53
  (Or.inl (by norm_num [node54])) p_node53 p_node53
 have g_node54 : ParentGood node54 := parent_good_of_valid2 node54_valid
 have p_node55 : P node55 := step node55 node54 node54 hβ hk node55_valid g_node54
  (Or.inl (by norm_num [node55])) p_node54 p_node54
 have g_node55 : ParentGood node55 := parent_good_of_valid2 node55_valid
 have p_node56 : P node56 := step node56 node55 node55 hβ hk node56_valid g_node55
  (Or.inl (by norm_num [node56])) p_node55 p_node55
 have g_node56 : ParentGood node56 := parent_good_of_valid2 node56_valid
 have p_node57 : P node57 := step node57 node56 node56 hβ hk node57_valid g_node56
  (Or.inl (by norm_num [node57])) p_node56 p_node56
 have g_node57 : ParentGood node57 := parent_good_of_valid2 node57_valid
 have p_node58 : P node58 := step node58 node57 node57 hβ hk node58_valid g_node57
  (Or.inl (by norm_num [node58])) p_node57 p_node57
 have g_node58 : ParentGood node58 := parent_good_of_valid2 node58_valid
 exact ⟨p_node58,p_node52⟩
end
end QRH.RepeatedMarks.Graph
