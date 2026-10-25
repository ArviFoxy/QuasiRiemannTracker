"""Summarize measurements as one metrics file per submission.

  python3 bench/aggregate.py [--out metrics]

Each file binds the numbers to the exact sources they describe. Source totals
are always written; the compile block appears once every module of the
submission has been measured.
"""
from pathlib import Path
import argparse, json, os, platform, statistics

import measure
from measure import BASELINE, ROOT, best_costs, build_graph, digest, environment, environment_key, load_plans, read_measurements

SCHEMA = 1


def machine():
    cpu = next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                if line.startswith('model name')), platform.processor())
    memory = next((int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()
                   if line.startswith('MemTotal:')), 0)
    return {'cpu': cpu, 'cores': os.cpu_count(), 'memory_bytes': memory, 'kernel': platform.release()}


def noise(records, costs):
    """Spread of repeated measurements of the same module."""
    by_key = {}
    for r in records:
        if r['status'] == 'ok' and 'net' in r and r['kind'] in ('cost', 'repeat', 'canary', 'rebuild'):
            by_key.setdefault(r['key'], []).append(r['net'])
    ratios = [statistics.pstdev(v)/statistics.mean(v) for v in by_key.values() if len(v) > 1 and statistics.mean(v) > 2]
    return {'modules_repeated': len(ratios),
            'median_relative_spread': round(statistics.median(ratios), 4) if ratios else None}


def profile(env, records, costs):
    """What the numbers were measured with. Only the toolchain, the recipe and
    the processor identify it: how many compiles ran at once changes nothing."""
    machine_info = machine()
    identity = {'recipe': measure.RECIPE, 'lean': env['lean_sha256'], 'packages': env['packages'],
                'cpu': machine_info['cpu'], 'cores': machine_info['cores']}
    workers = sorted({r['workers'] for r in records if 'workers' in r})
    return {
        'schema_version': SCHEMA,
        'id': digest(identity)[:12],
        'recipe': measure.RECIPE,
        'lean_version': env['lean_version'],
        'lean': env['lean_sha256'],
        'packages': env['packages'],
        'machine': machine_info,
        'workers': workers[0] if len(workers) == 1 else workers,
        'modules_measured': len(costs),
        'noise': noise(records, costs),
    }


def summarize(sid, plan, keys, costs, profile_id):
    modules = plan['modules']
    summary = {
        'schema_version': SCHEMA,
        'result_id': sid,
        'source_tree': plan['source_tree'],
        'dependency_trees': plan['dependency_trees'],
        'profile': profile_id,
        'modules': len(modules),
        'lines': sum(m['lines'] for m in modules),
        'bytes': sum(m['bytes'] for m in modules),
    }
    if all(k in costs for k in keys):
        by_owner, gross, peak, heaviest = {}, 0.0, 0, ('', 0.0)
        for module, key in zip(modules, keys):
            r = costs[key]
            by_owner[module['owner']] = by_owner.get(module['owner'], 0.0) + r['net']
            gross += r['cpu_user'] + r['cpu_system']
            peak = max(peak, r['maxrss_kib'] * 1024)
            if r['net'] > heaviest[1]:
                heaviest = (module['name'], r['net'])
        summary['compile'] = {
            'cpu_seconds': round(sum(by_owner.values()), 1),
            'cpu_seconds_by_submission': {k: round(v, 1) for k, v in sorted(by_owner.items())},
            'gross_cpu_seconds': round(gross, 1),
            'peak_rss_bytes': peak,
            'heaviest_module': {'name': heaviest[0], 'cpu_seconds': round(heaviest[1], 1)},
        }
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--out', type=Path, default=ROOT/'metrics')
    args = parser.parse_args()
    env, plans = environment(), load_plans()
    order, jobs, members = build_graph(plans, environment_key(env))
    records = read_measurements()
    costs = best_costs(records)
    prof = profile(env, records, costs)
    args.out.mkdir(exist_ok=True)
    write = lambda name, value: (args.out/name).write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')
    write('profile.json', prof)
    for sid in order:
        summary = summarize(sid, plans[sid], members[sid], costs, prof['id'])
        write(f'{sid}.json', summary)
        print(f"{sid:44} {summary['modules']:6d} modules" +
              (f"  {summary['compile']['cpu_seconds']/3600:7.2f} CPU-hours" if 'compile' in summary else '  (compile cost not yet measured)'))


if __name__ == '__main__':
    main()
