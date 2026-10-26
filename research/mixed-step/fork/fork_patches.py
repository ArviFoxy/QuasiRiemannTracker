"""Semantic edits to the mechanically forked modules (applied by fork_source.py after renaming).

Each entry maps a module (path relative to Collet's package) to a list of (old, new) replacements,
each of which must apply exactly once. The edits are the places where the repeated-mark proof
differs from Collet's beyond the renaming:
  * witnesses: the repeated-mark count asks for detector witnesses at the cutoff of each amplitude
    class (`binCutoff_rm`), so the hypotheses request witnesses at every admissible cutoff
    `t ∈ [1,3/2]` instead of at Collet's uniform cutoff of each slot set;
  * payment slack: Lemma C pays the common losses exactly, without Collet's `(c+d+forced)/12`
    reserve; the retained-exponent payments drop that term, which no later step uses;
  * kept gates: for a HIGH parent the six HIGH facet gates of Collet's source validity are
    certified by `HighValid` instead, so the width margins cover the kept density gates only.
"""

WITNESS_ALL_T = '''(∀t : ℝ,1≤t → t≤3/2 →
        Nonempty (∀u,SupportedWitness (B.family u) U a ε t T allowance i)) →'''

PATCHES = {
    'Record1252270103Source.High.MaxWeighted': [
        ('''(∀selected : Finset Slot,selected⊆B.slots →
        Nonempty (∀u,SupportedWitness (B.family u) U a ε
          (cutoff (2*a-1) capacity lam cap (∑s∈selected,B.widths s) 1) T allowance i)) →''',
         WITNESS_ALL_T),
        ('''    obtain ⟨witness⟩ := hwitness selected hs
''',
         '''    have hsel0 : 0≤∑s∈selected,B.widths s :=
      Finset.sum_nonneg (fun s hsel=>(B.widthsPositive s (hs hsel)).le)
    have witness : ∀bin : BinLabel B'.slots ((2*a-1)/2) binWidth,∀u,
        SupportedWitness (B'.family u) U a ε
          (binCutoff_rm capacity lam cap B'.slots B'.widths a binWidth bin) T allowance i := fun bin=>
      (hwitness _ (binCutoff_rm_bounds B'.slots B'.widths bin ha0 ha hB0 hlam hh0 hh1.le hsel0).1
        (binCutoff_rm_bounds B'.slots B'.widths bin ha0 ha hB0 hlam hh0 hh1.le hsel0).2).some
'''),
        ('''hh hf
      (fun s hsel=>hv s (hs hsel)) ht (fun _=>witness) (fun u hu s hsel=>hQ u hu s (hs hsel))''',
         '''hh hf
      (fun s hsel=>hv s (hs hsel)) ht witness (fun u hu s hsel=>hQ u hu s (hs hsel))'''),
    ],
    'Record1252270103Source.High.ActualBinSourceTau': [
        ('''    have hwit (selected : Finset Slot) (hsel : selected⊆B'.slots) :
        Nonempty (∀u,SupportedWitness (B'.family u) (Z^d) a ε
          (cutoff (2*a-1) capacity lam cap (∑s∈selected,B'.widths s) 1) (Z^τ) ((Z^d)^(τ/(2*dmax))) i) :=
      hw Z hZ₀ d hd hd' B pick hpick hn a i hi' ha ha' hnext hcurrent hmod _
        (Finset.sum_nonneg (fun s hs=>(B.widthsPositive s (hsel hs)).le))''',
         '''    have hwit (t : ℝ) (ht1 : 1≤t) (ht2 : t≤3/2) :
        Nonempty (∀u,SupportedWitness (B'.family u) (Z^d) a ε t (Z^τ) ((Z^d)^(τ/(2*dmax))) i) :=
      hw Z hZ₀ d hd hd' B pick hpick hn a i hi' ha ha' hnext hcurrent hmod t ht1 ht2'''),
    ],
    'Record1252270103Source.HighScalar.LabelPayment': [
        ('''        unmarkedDensity ν*err+errv)-D*((n.highFee:ℝ)+reserve)-
        (labelC reflected l Z+Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced)/12 := by''',
         '''        unmarkedDensity ν*err+errv)-D*((n.highFee:ℝ)+reserve) := by'''),
    ],
    'Record1252270103Source.HighScalar.ModifiedPayment': [
        ('''      D*((n.highFee:ℝ)+reserve)-
      (labelC reflected l Z+Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)+forced)/12 := by''',
         '''      D*((n.highFee:ℝ)+reserve) := by'''),
    ],
    'Record1252270103Source.Low.GlobalInitialAssemblyMargins': [
        ('''        ∀j,margin/2≤sourceDensityWidthReal n low high''',
         '''        ∀j,QRH.RepeatedMarks.Finite.KeptGate high j →margin/2≤sourceDensityWidthReal n low high'''),
        ('''fun j=>by linarith [hd j]⟩''', '''fun j hj=>by linarith [hd j hj]⟩'''),
    ],
    'Record1252270103Source.Low.GlobalInitialCallbacks': [
        ('''      ∀j,nfWidthMargin_rm n low high hv ha loss/2≤sourceDensityWidthReal n low high''',
         '''      ∀j,QRH.RepeatedMarks.Finite.KeptGate high j →
        nfWidthMargin_rm n low high hv ha loss/2≤sourceDensityWidthReal n low high'''),
    ],
}
