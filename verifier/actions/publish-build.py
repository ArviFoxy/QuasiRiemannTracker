"""Publish a completed isolated server build using a host-owned signing key.

Run this from the protected checkout on the host, after copying a successful
worker run and its prepared libraries.json out of the VM. The signing key and
GitHub credentials remain on the host. Every supplied run directory is a trusted
operator input, never an artifact accepted from a submitter.
"""
from pathlib import Path
import argparse, datetime, json, os, subprocess, sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from standard.build_cache import build_inputs, digest, pack_cache


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--libraries', type=Path, required=True)
    parser.add_argument('--key', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--publish', action='store_true')
    args = parser.parse_args()
    run = args.run.resolve()
    report = json.loads((run/'result.json').read_text())
    contract = json.loads((run/'contract.json').read_text())
    if (report.get('status') != 'PASS' or report.get('judge_exit_code') != 0 or
        report.get('kernels') != ['Lean default','nanoda','con-ron'] or
        report.get('source_files') != contract['source_files'] or
        report.get('reviewed_pr_head') != contract['head_sha'] or
        report.get('artifacts',{}).get('contract.json') != digest(run/'contract.json') or
        digest(args.libraries) != contract['library_inventory_sha256']):
        raise ValueError('Server build has no matching successful verification record')
    inputs = build_inputs(contract, json.loads(args.profile.read_text()),
                          json.loads(args.libraries.read_text()), report['tool_pins'])
    args.out.mkdir(parents=True, exist_ok=True)
    archive = args.out/'candidate-build.tar.gz'
    pack_cache(run/'candidate-lib', archive, inputs)
    sha = digest(archive)
    destination = args.out/(sha+'.tar.gz')
    archive.replace(destination)
    index = args.out/'cache.json'
    index.write_text(json.dumps({'schema_version':1, 'sha256':sha, 'archive':destination.name,
        'size':destination.stat().st_size, 'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_head':contract['head_sha'], 'report_sha256':digest(run/'result.json'),
        'module_count':len(inputs['modules'])}, sort_keys=True)+'\n')
    signature = args.out/'cache.sig'
    subprocess.run(['openssl','pkeyutl','-sign','-inkey',str(args.key),'-rawin',
                    '-in',str(index),'-out',str(signature)], check=True)
    # Catch accidental publication using a key different from the protected pin.
    public = Path(__file__).resolve().parents[1]/'standard/build-cache-public.pem'
    subprocess.run(['openssl','pkeyutl','-verify','-pubin','-inkey',str(public),'-rawin',
                    '-in',str(index),'-sigfile',str(signature)], check=True)
    if args.publish:
        repo, tag = 'GTimG/QuasiRiemannTracker', 'submission-build-cache-v1'
        env = {**os.environ, 'GIT_CONFIG_NOSYSTEM':'1'}
        def gh(*command):
            subprocess.run(['gh',*command,'--repo',repo],env=env,check=True)
        # The release must be created by the operator; immutable bundle names
        # are uploaded first. A mixed index/signature during refresh is a miss.
        gh('release','upload',tag,str(destination))
        gh('release','upload',tag,str(index),str(signature),
           str(Path(__file__).resolve().parents[2]/'LICENSE'),
           str(Path(__file__).resolve().parents[2]/'NOTICE'),'--clobber')
    print(f'Published bundle prepared: {len(inputs["modules"])} modules, {destination.stat().st_size} bytes')


if __name__ == '__main__':
    main()
