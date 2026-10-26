"""Single-stage edits of the two endpoint modules of the forked final return (as in PR 76).

fork_return.py emits Collet's two-stage endpoints (an intermediate return, then the final one).
PR 76's package uses the final stage alone: the natural cap `2β − 1 ≤ 3/4` is the baseline's
`β ≤ 7/8` (`Graph/NaturalCap.lean` of PR 76's package). This script makes the same edits that PR 76
made by hand:
  * FinalReturn/EndpointFromSources.lean: the two-stage theorems `*_from_two_stage_global_sources`,
    their axiom prints and the two imports they need (Collet's IntermediateCount.Schedule and
    EndpointFromSources) are removed; everything else (the final-stage theorems, with the
    physical-face restriction at the numerator cap SP) is kept verbatim;
  * FinalReturn/EndpointFromGlobalSources.lean: replaced by PR 76's single-stage endpoint
    `beta_of_two_global_sources`, which imports `Graph.NaturalCap` from PR 76's package.

usage: python3 single_stage.py FINALRETURN_DIR PKG PR76_PKG
(FINALRETURN_DIR = the FinalReturn directory written by fork_return.py; edited in place)
Check: on the PR 76 regeneration (research/combined/sil_face.env) the output is byte-identical to
PR 76's two modules.
"""
import os, sys

GLOBAL_SOURCES = '''/- Repeated marks, single stage: the final return from the two final global sources.
The natural cap `2β − 1 ≤ naturalK/6 = 3/4` is the baseline's `β ≤ 7/8` (`Graph/NaturalCap.lean`),
so the intermediate return and the bootstrap of Collet's final stage are not used. -/
import {pkg}.FinalReturn.EndpointFromSources
import {pr76}.Graph.NaturalCap
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [QRH.RepeatedMarks.Return.naturalK]
 linarith

theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta :=
 Final.beta_of_global_sources hC hP natural_cap_return
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.beta_of_two_global_sources
'''

NS = 'QRH.RepeatedMarks.Return'
CPKG = 'Submissions.hailey_collet_1252270103'


def sub1(text, old, new):
    if text.count(old) != 1:
        raise SystemExit(f'single-stage edit applies {text.count(old)} times:\n{old}')
    return text.replace(old, new)


def endpoint_from_sources(text):
    text = sub1(text, "re-instantiated with the final constants of the repeated-mark graph. -/\n",
                "re-instantiated with the final constants of the repeated-mark graph. Single stage: the two-stage\n"
                "theorems (Collet's intermediate return) are removed. -/\n")
    text = sub1(text, f'import {CPKG}.Record1252270103Return.IntermediateCount.Schedule\n', '')
    text = sub1(text, f'import {CPKG}.Record1252270103Return.EndpointFromSources\n', '')
    i = text.index('theorem beta_from_two_stage_global_sources\n')
    j = text.index(f'end\nend {NS}\n', i)
    text = text[:i] + text[j:]
    for name in ('beta', 'hecke', 'dirichlet'):
        text = sub1(text, f'#print axioms {NS}.{name}_from_two_stage_global_sources\n', '')
    text = sub1(text, f'#print axioms {NS}.zeta_from_two_stage_global_sources\n', '\n')
    assert 'two_stage' not in text and 'Intermediate' not in text
    return text


def main():
    fr, pkg, pr76 = sys.argv[1], sys.argv[2], sys.argv[3]
    p = os.path.join(fr, 'EndpointFromSources.lean')
    text = endpoint_from_sources(open(p).read())
    open(p, 'w').write(text)
    open(os.path.join(fr, 'EndpointFromGlobalSources.lean'), 'w').write(GLOBAL_SOURCES.format(pkg=pkg, pr76=pr76))
    print('single stage: EndpointFromSources, EndpointFromGlobalSources')


if __name__ == '__main__':
    main()
