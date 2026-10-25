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
                            ('DUMPS', root/'dumps'), ('BENCH', root),
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
            (entry/'module.ilean').write_text('{}')
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

    def test_a_full_disk_stops_new_work_like_a_pause_request(self):
        from collections import namedtuple
        usage = namedtuple('usage', 'total used free')
        with patch.object(measure.shutil, 'disk_usage', return_value=usage(100, 99, 1)):
            self.run_all()
        self.assertEqual(self.compiled, [])

    def fake_dump(self, sid, plan, keys, env, **options):
        (measure.DUMPS/'index').mkdir(parents=True, exist_ok=True)
        self.dumped.append((sid, all((measure.STORE/k/'module.olean').exists() for k in keys)))
        if not self.dump_works:
            return False
        for key in keys:
            (measure.DUMPS/f'{key}.json.gz').write_bytes(b'graph')
        (measure.DUMPS/'index'/f'{sid}.json').write_text(json.dumps(keys))
        return True

    def run_clean(self, collect=True):
        runner = measure.Runner({'lean': '/none', 'libraries': []}, self.order, self.jobs, self.members, self.order,
                                workers=2, anon_cap_kib=1, heavy_cap_kib=2, timeout=1,
                                plans=self.plans, dump=True, collect=collect)
        with patch.object(measure, 'compile_module', self.fake), patch.object(measure, 'dump_submission', self.fake_dump):
            return runner.run()

    def test_a_finished_submission_leaves_its_graphs_and_only_what_others_build_on_is_kept(self):
        self.dumped, self.dump_works = [], True
        self.assertTrue(self.run_clean())
        # Each submission is dumped once, while every one of its modules is still compiled.
        self.assertEqual(sorted(self.dumped), [('next', True), (measure.BASELINE, True)])
        self.assertEqual(self.dumped[0][0], measure.BASELINE)
        # Nothing is left to build on once both are done, but the costs and graphs are.
        self.assertEqual(list(measure.STORE.glob('*')), [])
        self.assertEqual(list(measure.LIBS.glob('*')), [])
        self.assertEqual(len(measure.best_costs(measure.read_measurements())), 3)
        for sid in self.order:
            self.assertTrue((measure.DUMPS/'index'/f'{sid}.json').exists())
        # Finished work is not repeated, even though its modules are gone.
        self.compiled.clear()
        self.dumped.clear()
        self.assertTrue(self.run_clean())
        self.assertEqual((self.compiled, self.dumped), ([], []))

    def test_modules_a_later_submission_needs_survive_until_it_is_done(self):
        self.dumped, self.dump_works = [], True
        original = measure.collect_garbage
        released = []
        def spy(sid, jobs, order, members, finished):
            freed = original(sid, jobs, order, members, finished)
            released.append((sid, sorted(p.name for p in measure.STORE.glob('*'))))
            return freed
        with patch.object(measure, 'collect_garbage', spy):
            self.run_clean()
        # The baseline's modules are still there when its own clean-up is done, because
        # the next submission builds on them; whether the next one's own module has been
        # compiled by then depends on timing.
        self.assertTrue(set(self.members[measure.BASELINE]) <= set(dict(released)[measure.BASELINE]))
        self.assertEqual(dict(released)['next'], [])

    def test_compiled_modules_stay_when_their_graphs_could_not_be_kept(self):
        self.dumped, self.dump_works = [], False
        self.run_clean()
        self.assertEqual(len(list(measure.STORE.glob('*'))), 3)

    def test_a_fast_run_only_builds_and_is_finished_without_any_cost(self):
        self.dumped, self.dump_works = [], True
        flags = []
        def fast_fake(job, view, env, **options):
            flags.append(options.get('fast'))
            result = self.fake(job, view, env, **options)
            for field in ('net', 'work', 'profile'):
                result.pop(field, None)
            return result
        runner = measure.Runner({'lean': '/none', 'libraries': []}, self.order, self.jobs, self.members, self.order,
                                workers=2, anon_cap_kib=1, heavy_cap_kib=2, timeout=1,
                                plans=self.plans, dump=True, collect=True, fast=True)
        with patch.object(measure, 'compile_module', fast_fake), patch.object(measure, 'dump_submission', self.fake_dump):
            self.assertTrue(runner.run())
        self.assertEqual(flags, [True, True, True])
        records = measure.read_measurements()
        self.assertEqual({r['kind'] for r in records}, {'build'})
        self.assertEqual(measure.best_costs(records), {})
        # Both submissions are finished, so nothing is built again.
        self.compiled.clear()
        with patch.object(measure, 'compile_module', fast_fake), patch.object(measure, 'dump_submission', self.fake_dump):
            self.assertTrue(runner.run())
        self.assertEqual(self.compiled, [])
        # Measuring would still want costs for what was only built.
        self.assertFalse(measure.is_complete(measure.BASELINE, self.members[measure.BASELINE], {}))

    def test_the_clean_up_can_be_switched_off(self):
        self.dumped, self.dump_works = [], True
        self.run_clean(collect=False)
        self.assertEqual(len(list(measure.STORE.glob('*'))), 3)
        self.assertEqual(len(self.dumped), 2)

    def test_a_module_that_outgrows_its_memory_runs_with_at_most_one_light_neighbour(self):
        # Three independent modules; the first needs more than the ordinary cap.
        modules = [module(f'Submissions.base.M{i}', f'm{i}', owner='base') for i in range(5)]
        self.plans = {measure.BASELINE: plan(measure.BASELINE, modules)}
        self.order, self.jobs, self.members = measure.build_graph(self.plans, 'env')
        heavy = self.members[measure.BASELINE][0]
        live, calls = [], []
        def fake(job, view, env, **options):
            cap = options['anon_cap_kib']
            with self.lock:
                live.append((job.key, cap))
                calls.append((job.key, cap, len(live)))
            try:
                if job.key == heavy and cap <= 100:
                    status = 'memory'
                else:
                    status = 'ok'
                    entry = measure.STORE/job.key
                    entry.mkdir(parents=True, exist_ok=True)
                    (entry/'module.olean').write_bytes(b'olean')
                    (entry/'module.ilean').write_text('{}')
                import time as _time
                _time.sleep(0.05)
                result = record(job.key, 2.0, 2.0 - measure.SLACK, module=job.module['name'], owner=job.module['owner'])
                result['status'] = status
                result['peak_anon_kib'] = cap + 1
                return result
            finally:
                with self.lock:
                    live.remove((job.key, cap))
        runner = measure.Runner({'lean': '/none', 'libraries': []}, self.order, self.jobs, self.members, self.order,
                                workers=3, anon_cap_kib=100, heavy_cap_kib=1000, timeout=1, side_cap_kib=10)
        with patch.object(measure, 'compile_module', fake):
            self.assertTrue(runner.run())
        retry = [c for c in calls if c[0] == heavy and c[1] == 1000]
        self.assertEqual(len(retry), 1)
        # While the heavy module ran there was at most one other compile, under the light cap.
        self.assertEqual(retry[0][2], 1)
        others = [c for c in calls if c[1] == 10]
        self.assertTrue(all(c[2] <= 2 for c in others))
        self.assertEqual(len(measure.best_costs(measure.read_measurements())), 5)

    def test_the_names_a_declaration_mentions_come_from_the_ilean_file(self):
        ilean = {'references': {
            '{"c":{"m":"T.A","n":"T.helper"}}': {'definition': None, 'usages': [[4, 18, 4, 24, 'T.useSimp'], [7, 17, 7, 23]]},
            '{"c":{"m":"T.A","n":"T.unrelated"}}': {'definition': None, 'usages': [[6, 8, 6, 17, 'T.viaUnused']]},
            '{"c":{"m":"Mathlib.X","n":"Nat.add"}}': {'definition': None, 'usages': [[1, 1, 1, 2, 'T.useSimp']]},
            '{"c":{"m":"T.C","n":"T.useSimp"}}': {'definition': [3, 8, 3, 15], 'usages': [[9, 1, 9, 5, 'T.useSimp']]},
            '{"f":{"id":"x"}}': {'definition': [1, 1, 1, 2], 'usages': [[2, 1, 2, 2, 'T.useSimp']]},
        }}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'module.ilean'
            path.write_text(json.dumps(ilean))
            pairs, context = measure.text_references(path, {'T.A', 'T.C'})
        # Names of libraries and local variables are left out, and so is a declaration naming itself.
        self.assertEqual(pairs, [('T.useSimp', 'T.helper'), ('T.viaUnused', 'T.unrelated')])
        self.assertEqual(context, ['T.helper'])

    def test_a_module_is_built_only_with_its_name_references(self):
        entry = measure.STORE/'k'
        entry.mkdir(parents=True)
        (entry/'module.olean').write_bytes(b'x')
        self.assertFalse(measure.is_built('k'))
        (entry/'module.ilean').write_text('{}')
        self.assertTrue(measure.is_built('k'))

    def test_what_nobody_builds_on_is_named_per_submission(self):
        order, members = ['a', 'b', 'c'], {'a': ['x', 'y'], 'b': ['x', 'z'], 'c': ['y', 'w']}
        self.assertEqual(measure.unneeded(order, members, set(), 'a'), [])
        self.assertEqual(measure.unneeded(order, members, {'a'}, 'a'), [])
        self.assertEqual(measure.unneeded(order, members, {'a', 'b'}, 'b'), ['x', 'z'])
        self.assertEqual(measure.unneeded(order, members, {'a', 'b', 'c'}, 'c'), ['y', 'w'])


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

    def test_every_module_costs_what_it_takes_beyond_an_empty_file(self):
        modules = [module('Submissions.base.A', 'a', owner='base'),
                   module('Candidate.Main', 'm', ['Submissions.base.A'], owner='next', lines=3)]
        costs = {'ka': record('ka', 10.0, 9.9), 'km': record('km', 0.7, 0.6)}
        p = plan('next', modules)
        jobs = measure.build_graph({'next': p}, 'env')[1]
        keys = measure.module_keys(p, 'env')
        costs = {keys['Submissions.base.A']: costs['ka'], keys['Candidate.Main']: costs['km']}
        empty = aggregate.empty_module_seconds(jobs, costs)
        self.assertEqual(empty, 0.7)
        compiled = aggregate.summarize('next', p, [keys[m['name']] for m in modules], costs, 'profile0001', empty)['compile']
        self.assertEqual(compiled['cpu_seconds_by_submission'], {'base': 9.3, 'next': 0.0})
        self.assertEqual(compiled['cpu_seconds'], 9.3)
        self.assertEqual(aggregate.empty_module_seconds(jobs, {}), 0.0)

    def test_a_submission_with_unmeasured_modules_reports_only_its_sources(self):
        modules = [module('Candidate.Main', 'm', owner='next')]
        summary = aggregate.summarize('next', plan('next', modules), ['km'], {}, 'profile0001')
        self.assertNotIn('compile', summary)
        self.assertEqual(summary['modules'], 1)

    def test_alive_code_is_reported_for_the_sources_it_was_worked_out_from(self):
        modules = [module('Candidate.Main', 'm', owner='next')]
        p = plan('next', modules)
        alive = {'source_tree': p['source_tree'], 'modules': 1, 'declarations': 3, 'removed': 2,
                 'active_bytes': 900, 'gzip_bytes': 400, 'root': 'x', 'total_modules': 1}
        summary = aggregate.summarize('next', p, ['km'], {}, 'profile0001', alive=alive)
        self.assertEqual(summary['alive'], {'modules': 1, 'declarations': 3, 'removed': 2,
                                            'active_bytes': 900, 'gzip_bytes': 400})
        self.assertNotIn('alive', aggregate.summarize('next', p, ['km'], {}, 'profile0001'))
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(aggregate, 'BENCH', Path(directory)):
                self.assertIsNone(aggregate.read_alive('next', p))
                (Path(directory)/'alive').mkdir()
                (Path(directory)/'alive/next.json').write_text(json.dumps(alive))
                self.assertEqual(aggregate.read_alive('next', p)['gzip_bytes'], 400)
                (Path(directory)/'alive/next.json').write_text(json.dumps({**alive, 'source_tree': 'c'*40}))
                self.assertIsNone(aggregate.read_alive('next', p))


if __name__ == '__main__':
    unittest.main()
