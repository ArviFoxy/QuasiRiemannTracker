"""Parent-split patches for the LOW spine (mixed step, F3).

The LOW wrappers of Collet's `SelectedLowSource*`, `SelectedLowBufferedSource`,
`SelectedRegularLowSource(Data)`, … all restate one statement shape. `split_statement` applies the
common two-parent / two-amplitude / price edits to such a statement; module scripts add the proof
edits (intro patterns, argument lists) and call `fork_module`.
"""
import re
CROOT = '/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/Record1252270103Source'
OROOT = '/home/user/lean-env/qrh/Submissions/arvi_mixed_step/ForkMx/Record1252270103Source'

class Patch:
    def __init__(self, text):
        self.d = text
    def R(self, a, b, cnt=1):
        c = self.d.count(a)
        if c != cnt:
            raise SystemExit(f'patch applies {c} times (expected {cnt}):\n{a[:160]}')
        self.d = self.d.replace(a, b)
    def R1(self, a, b):
        """Replace the first occurrence only (the statement precedes the proof)."""
        if a not in self.d:
            raise SystemExit(f'patch does not apply:\n{a[:160]}')
        self.d = self.d.replace(a, b, 1)
    def Ropt(self, a, b):
        self.d = self.d.replace(a, b)
    def sub(self, pat, rep, flags=0):
        self.d = re.sub(pat, rep, self.d, flags=flags)

def split_statement(p, name):
    """Common statement edits. `p` is a Patch on the declaration text."""
    p.sub(r'theorem ' + re.escape(name) + r' \(Kgraph:ℚ\)\(n low:Source\)\(bcell εsource:ℝ\)\n    \(hg:RealGeometry Kgraph n low bcell\)\(hn:ParentGood n\)\(hlow:ParentGood low\)',
          'theorem ' + name + '_mx (n low:Source)(bcell φ εsource:ℝ)\n    (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)(hlow:ParentGood low)')
    p.R('∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)',
        '∀(reflected second : Bool){α₀ : Type}[Fintype α₀][DecidableEq α₀](s₀ : Input α₀)(s : Input α)\n      (Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)')
    p.R('      s.η=ηanchor →', '      s₀.η=ηanchor →')
    p.R('fixedParentUnit left s.η l:O)', 'fixedParentUnit left s₀.η l:O)')
    p.sub(r'(?<![A-Za-z_0-9.₀])s modifier\b', 's₀ modifier')
    p.R('geometryRawFixedMask s R₀', 'geometryRawFixedMask s₀ R₀', 2)
    p.R('((actualAllocations s.pools (if reflected', '((actualAllocations s₀.pools (if reflected')
    p.R('''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s)) hK bin''', '''CoupledFirst.balancedColumnScalar reflected s₀ modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s₀)) hK bin''')
    p.R('''    ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤radiusMax) →''',
    '''    ∀(P:Finset (Ideal O))(poolAmp poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z poolAmp ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤radiusMax) →''')
    p.R('''        ((mainRadius l+6*sourceAReal n low bcell)/ell);''', '''        ((mainRadius l+6*poolAmp)/ell);''')
    p.R('''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →''',
        '''    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →
    s₀.W₁=(p.profile 0:ℝ→ℂ) → s₀.W₂=(p.profile 1:ℝ→ℂ) → Fintype.card α₀≤N → 1≤s₀.lower →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s₀≤Z^Bmass →''')
    p.R('''    (∀l,omega l≤''', '''    ∀κ:ℝ,sourceAReal n low bcell-poolAmp≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ →
    (∀l,φ≤(∑i,w i)-∑i∈liveIndices (sel l).B₁.val,w i) →
    (∀l,omega l≤''')
    p.R1('Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+', 'Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+κ+Bmass*εmass+')

def split_intro(p):
    """Common edits of the main `intro` of a wrapper's proof."""
    p.R('intro T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor',
        'intro T reflected second α₀ _ _ s₀ s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor')
    p.R('hseed hsourceRadius hC₂ ht', 'hseed hsourceRadius hW₁₀ hW₂₀ hN₀ hslower₀ hsourceRadius₀ hC₂ ht')
    p.R('P poolMesh BD Bsource depth H0 mainRadius', 'P poolAmp poolMesh BD Bsource depth H0 mainRadius')
    p.R('hcommon₁ hcommon₂ extra hphase', 'hcommon₁ hcommon₂ extra κ hshift hφ hphase')

def fork_module(rel, names, header_note, imports, edit):
    src = open(f'{CROOT}/{rel}.lean').read()
    first = src.split('\n', 1)[0]
    starts = [src.index('theorem ' + n) for n in names]
    i = min(starts)
    ns = re.findall(r'^namespace (\S+)', src[:i], re.M)
    endm = re.search(r'\nend\s*\nend ' + re.escape(ns[-1]), src)
    j = endm.start() if endm else src.rindex('\nend ' + ns[-1])
    head = src[src.index('set_option autoImplicit false'):i]
    head = re.sub(r'^(local instance)\s+([A-Za-z_][A-Za-z_0-9]*)', r'\1 \2_mx', head, flags=re.M)
    head = re.sub(r'^(local instance)\s*(\{)', r'\1 forkInst_mx \2', head, flags=re.M)
    p = Patch(src[i:j])
    edit(p)
    tail = ('\nend\n' if endm else '\n') + f'end {ns[-1]}\n' + ''.join(f'#print axioms {ns[-1]}.{n}_mx\n' for n in names)
    out = (first + '\n' + header_note.rstrip() + ' -/\n' + f'import Submissions.hailey_collet_1252270103.Record1252270103Source.{rel.replace("/", ".")}\n'
           + ''.join(f'import {x}\n' for x in imports) + head + p.d + tail)
    path = f'{OROOT}/{rel}.lean'
    open(path, 'w').write(out)
    print('wrote', path)
