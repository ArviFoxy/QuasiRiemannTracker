"""Fetch a server-signed source build before any candidate code executes."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, urllib.request
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from standard.build_cache import MAX_BYTES, digest, build_inputs, compatibility_error

RELEASE = 'https://github.com/GTimG/QuasiRiemannTracker/releases/download/submission-build-cache-v1/'
KEY = Path(__file__).resolve().parents[1]/'standard/build-cache-public.pem'


def download(url, destination, limit):
    with urllib.request.urlopen(url, timeout=60) as response, destination.open('xb') as output:
        count = 0
        while data := response.read(1024*1024):
            count += len(data)
            if count > limit:
                raise ValueError('Cache download exceeds size limit')
            output.write(data)


def authenticate(index, signature, key=KEY):
    subprocess.run(['openssl','pkeyutl','-verify','-pubin','-inkey',str(key),
                    '-rawin','-in',str(index),'-sigfile',str(signature)],
                   check=True, capture_output=True, timeout=15)
    value = json.loads(index.read_text())
    if (value.get('schema_version') != 1 or
        not re.fullmatch('[a-f0-9]{64}', value.get('sha256','')) or
        value.get('archive') != value['sha256']+'.tar.gz' or
        type(value.get('size')) is not int or not 0 < value['size'] <= MAX_BYTES):
        raise ValueError('Invalid signed cache index')
    return value


def main():
    out = Path('verification').resolve()
    profile_path = out/'profile.json'
    profile = json.loads(profile_path.read_text())
    profile.pop('candidate_cache', None)
    status = {'status':'miss'}
    try:
        with tempfile.TemporaryDirectory(dir=out, prefix='build-download-') as tmp:
            directory = Path(tmp)
            download(RELEASE+'cache.json', directory/'cache.json', 16*1024*1024)
            download(RELEASE+'cache.sig', directory/'cache.sig', 1024)
            index = authenticate(directory/'cache.json', directory/'cache.sig')
            prepared = out/'prepared'
            inputs = build_inputs(json.loads((prepared/'contract.json').read_text()), profile,
                json.loads((prepared/'libraries.json').read_text()), json.loads((out/'tool-pins.json').read_text()))
            status.update(cache_environment=index.get('environment'), worker_environment=inputs['environment'])
            if reason := compatibility_error(index, inputs):
                raise ValueError(reason)
            matches = sum(index.get('modules', {}).get(m) == k for m,k in inputs['modules'].items())
            status.update(matching_modules=matches, required_modules=len(inputs['modules']))
            if not matches:
                raise ValueError('Compiler and libraries match; no submitted module matches the server cache')
            archive = directory/index['archive']
            download(RELEASE+index['archive'], archive, index['size'])
            if archive.stat().st_size != index['size'] or digest(archive) != index['sha256']:
                raise ValueError('Authenticated cache archive differs')
            destination = out/'authenticated-build.tar.gz'
            shutil.move(archive, destination)
            profile['candidate_cache'] = {'path':str(destination), 'sha256':index['sha256'],
                'url':RELEASE+index['archive'], 'signer':digest(KEY)}
            status.update(status='hit', archive_sha256=index['sha256'])
            print(f'Authenticated server build: {matches}/{len(inputs["modules"])} compatible modules; checking archive during replay', flush=True)
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as error:
        status['reason'] = f'{type(error).__name__}: {error}'
        print(f'Build cache unavailable ({status["reason"]}); compiling submitted source',flush=True)
    (out/'build-cache-status.json').write_text(json.dumps(status,indent=2)+'\n')
    profile_path.write_text(json.dumps(profile,indent=2)+'\n')


if __name__ == '__main__':
    main()
