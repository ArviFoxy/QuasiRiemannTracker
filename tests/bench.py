"""Tests for the compile-cost benchmark that do not need Lean."""
from pathlib import Path
import json, os, sys, tempfile, threading, unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'bench'))
import aggregate, measure


def module(name, source, dependencies=(), owner='alpha', lines=10):
    return {'name': name, 'owner': owner, 'path': 'src/'+name.replace('.', '/')+'.lean', 'sha256': source,
            'bytes': lines*20, 'lines': lines, 'dependencies': list(dependencies), 'package_imports': []}


def plan(sid, modules):
    return {'id': sid, 'source_tree': 'a'*40, 'dependency_trees': {sid: 'b'*40}, 'modules': modules}


def record(key, net, work, **extra):
    return {'key': key, 'module': key, 'owner': 'alpha', 'kind': 'cost', 'status': 'ok', 'attempt': 1,
            'cpu_user': net+2, 'cpu_system': 1.0, 'net': net, 'work': work, 'wall': net+3,
            'maxrss_kib': 4_000_000, 'peak_anon_kib': 200_000, **extra}


class ProfileTests(unittest.TestCase):
    def test_phases_in_any_unit(self):
        text = 'warning: unused\n\ncumulative profiling times:\n\t.olean serialization 59.3ms\n' \
               '\timport 5.6s\n\tlinting 1.34e-05ms\n\ttactic execution 12µs\n\tblocked (unaccounted) 0.5s\n'
        phases = measure.parse_profile(text)
        self.assertAlmostEqual(phases['import'], 5.6)
        self.assertAlmostEqual(phases['.olean serialization'], 0.0593)
        self.assertAlmostEqual(phases['linting'], 1.34e-8)
        self.assertAlmostEqual(phases['tactic execution'], 12e-6)
        self.assertAlmostEqual(phases['blocked (unaccounted)'], 0.5)

    def test_the_last_summary_wins_and_no_summary_is_none(self):
        self.assertIsNone(measure.parse_profile('error: nothing was profiled'))
        text = 'cumulative profiling times:\n\timport 1s\ncumulative profiling times:\n\timport 2s\n'
        self.assertEqual(measure.parse_profile(text), {'import': 2.0})


class KeyTests(unittest.TestCase):
    base = [module('Submissions.alpha.A', 'a1'), module('Candidate.Main', 'm1', ['Submissions.alpha.A'])]

    def keys(self, modules, env='env'):
        return measure.module_keys(plan('alpha', modules), env)

    def test_keys_follow_sources_dependencies_and_environment(self):
        before = self.keys(self.base)
        changed_dep = self.keys([module('Submissions.alpha.A', 'a2'), self.base[1]])
        self.assertNotEqual(before['Submissions.alpha.A'], changed_dep['Submissions.alpha.A'])
        self.assertNotEqual(before['Candidate.Main'], changed_dep['Candidate.Main'])
        changed_top = self.keys([self.base[0], module('Candidate.Main', 'm2', ['Submissions.alpha.A'])])
        self.assertEqual(before['Submissions.alpha.A'], changed_top['Submissions.alpha.A'])
        self.assertNotEqual(before['Candidate.Main'], changed_top['Candidate.Main'])
        self.assertEqual(before, self.keys(self.base))
        self.assertNotEqual(before, self.keys(self.base, env='other'))

    def test_shared_modules_are_one_job_and_small_submissions_come_first(self):
        shared = module('Submissions.base.A', 'a1', owner='base')
        plans = {
            'big': plan('big', [shared, module('Candidate.Main', 'b', ['Submissions.base.A'], owner='big'), module('Candidate.X', 'x', owner='big')]),
            measure.BASELINE: plan(measure.BASELINE, [shared]),
            'small': plan('small', [shared, module('Candidate.Main', 's', ['Submissions.base.A'], owner='small')]),
        }
        order, jobs, members = measure.build_graph(plans, 'env')
        self.assertEqual(order, [measure.BASELINE, 'small', 'big'])
        self.assertEqual(len(jobs), 4)
        key = members[measure.BASELINE][0]
        self.assertEqual(jobs[key].submissions, [measure.BASELINE, 'small', 'big'])
        self.assertEqual(members['small'][0], key)
        self.assertNotEqual(members['small'][1], members['big'][1])


class MeasurementTests(unittest.TestCase):
    def test_a_run_whose_profile_and_cpu_time_disagree_is_inconsistent(self):
        self.assertTrue(measure.consistent(record('a', 5.0, 5.0 - measure.SLACK)))
        self.assertTrue(measure.consistent(record('a', 5.0, 5.0 - measure.SLACK + 0.1)))
        self.assertFalse(measure.consistent(record('a', 5.0, 5.9)))
        self.assertFalse(measure.consistent(record('a', 1.0, 0.2)))
        self.assertTrue(measure.consistent(record('a', 100.0, 100.0 - measure.SLACK + 3.0)))
        self.assertFalse(measure.consistent({'status': 'ok'}))

    def test_the_run_that_agrees_best_is_the_one_kept(self):
        records = [record('k', 9.0, 9.9), record('k', 8.4, 8.3, kind='repeat'), record('k', 8.9, 9.3, kind='repeat'),
                   record('j', 3.0, 2.9, kind='canary'), record('i', 2.0, 1.9, status='failed')]
        best = measure.best_costs(records)
        self.assertEqual(set(best), {'k'})
        self.assertEqual(best['k']['net'], 8.4)


class RunnerTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        for name, value in [('STORE', root/'store'), ('LIBS', root/'libs'), ('SCRATCH', root/'scratch'),
                            ('MEASUREMENTS', root/'measurements.jsonl'), ('STOP', root/'STOP')]:
            patcher = patch.object(measure, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        shared = module('Submissions.base.A', 'a1', owner='base')
        helper = module('Submissions.base.B', 'b1', ['Submissions.base.A'], owner='base')
        self.plans = {
            measure.BASELINE: plan(measure.BASELINE, [shared, helper]),
            'next': plan('next', [shared, helper, module('Candidate.Main', 'n', ['Submissions.base.B'], owner='next')]),
        }
        self.order, self.jobs, self.members = measure.build_graph(self.plans, 'env')
        self.compiled, self.lock = [], threading.Lock()

    def fake(self, job, view, env, **options):
        for dependency in job.module['dependencies']:
            self.assertTrue((view/(dependency.replace('.', '/')+'.olean')).exists(), f'{dependency} is not importable')
        if options.get('keep', True):
            entry = measure.STORE/job.key
            entry.mkdir(parents=True)
            (entry/'module.olean').write_bytes(b'olean')
        with self.lock:
            self.compiled.append(job.module['name'])
        return record(job.key, 2.0, 2.0 - measure.SLACK, module=job.module['name'], owner=job.module['owner'])

    def run_all(self):
        runner = measure.Runner({'lean': '/none', 'libraries': []}, self.order, self.jobs, self.members, self.order,
                                workers=2, anon_cap_kib=1, heavy_cap_kib=2, timeout=1)
        with patch.object(measure, 'compile_module', self.fake):
            return runner.run()

    def test_each_shared_module_is_compiled_once_after_its_dependencies_then_resumed(self):
        self.assertTrue(self.run_all())
        self.assertEqual(sorted(self.compiled), ['Candidate.Main', 'Submissions.base.A', 'Submissions.base.B'])
        self.assertLess(self.compiled.index('Submissions.base.A'), self.compiled.index('Submissions.base.B'))
        self.assertLess(self.compiled.index('Submissions.base.B'), self.compiled.index('Candidate.Main'))
        for sid in self.order:
            for m in self.plans[sid]['modules']:
                self.assertTrue((measure.LIBS/sid/(m['name'].replace('.', '/')+'.olean')).exists(), (sid, m['name']))
        costs = measure.best_costs(measure.read_measurements())
        self.assertEqual({k for sid in self.order for k in self.members[sid]}, set(costs))
        self.compiled.clear()
        self.assertTrue(self.run_all())
        self.assertEqual(self.compiled, [])

    def test_a_pause_request_stops_new_work(self):
        measure.STOP.write_text('')
        self.run_all()
        self.assertEqual(self.compiled, [])


class AggregateTests(unittest.TestCase):
    def test_costs_add_up_by_owner_and_peak_memory_is_the_largest(self):
        modules = [module('Submissions.base.A', 'a', owner='base'), module('Candidate.Main', 'm', ['Submissions.base.A'], owner='next')]
        costs = {'ka': record('ka', 10.0, 9.9, maxrss_kib=3_000_000), 'km': record('km', 4.5, 4.4, maxrss_kib=5_000_000)}
        summary = aggregate.summarize('next', plan('next', modules), ['ka', 'km'], costs, 'profile0001')
        compiled = summary['compile']
        self.assertEqual(compiled['cpu_seconds'], 14.5)
        self.assertEqual(compiled['cpu_seconds_by_submission'], {'base': 10.0, 'next': 4.5})
        self.assertEqual(compiled['gross_cpu_seconds'], 13.0 + 7.5)
        self.assertEqual(compiled['peak_rss_bytes'], 5_000_000 * 1024)
        self.assertEqual(compiled['heaviest_module'], {'name': 'Submissions.base.A', 'cpu_seconds': 10.0})
        self.assertEqual((summary['modules'], summary['lines']), (2, 20))

    def test_a_submission_with_unmeasured_modules_reports_only_its_sources(self):
        modules = [module('Candidate.Main', 'm', owner='next')]
        summary = aggregate.summarize('next', plan('next', modules), ['km'], {}, 'profile0001')
        self.assertNotIn('compile', summary)
        self.assertEqual(summary['modules'], 1)


if __name__ == '__main__':
    unittest.main()
