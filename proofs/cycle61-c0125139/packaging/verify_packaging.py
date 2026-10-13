"""Check the published source archive, transformation map and Candidate bytes.

Uses Python's standard library. Does not compile Lean or establish proof validity.
Run in the result checkout, or pass --candidate /path/to/submissions/<id>.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import runpy
import tarfile

HERE = Path(__file__).resolve().parent
PROOF = HERE.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path,
                        default=HERE.parents[2] / 'submissions' / PROOF.name)
    args = parser.parse_args()
    package = json.loads((HERE / 'package-manifest.json').read_text())
    for relative, expected in package['support_files'].items():
        name = PurePosixPath(relative)
        require(not name.is_absolute() and '..' not in name.parts,
                'Invalid support-file path')
        require(digest((PROOF / relative).read_bytes()) == expected,
                'Changed support file: ' + relative)
    mapping = json.loads((HERE / 'transformation.json').read_text())
    repairs = json.loads((HERE / 'repairs.json').read_text())
    sources = json.loads((PROOF / 'source-manifest.json').read_text())['modules']
    original = {}
    with tarfile.open(PROOF / 'original-sources.tar.gz', 'r:gz') as archive:
        seen = set()
        for member in archive.getmembers():
            path = PurePosixPath(member.name)
            require(member.isfile() and not path.is_absolute()
                    and '..' not in path.parts and member.name not in seen,
                    'Nonregular or duplicate archive member')
            seen.add(member.name)
            if not member.name.startswith('src/'):
                continue
            require(member.name.endswith('.lean'), 'Unexpected original source')
            module = member.name[4:-5].replace('/', '.')
            require(module in sources and not module.startswith('OAI.'),
                    'Unexpected archived module: ' + module)
            data = archive.extractfile(member).read()
            require(digest(data) == sources[module]['sha256']
                    and len(data) == sources[module]['bytes'],
                    'Original source differs: ' + module)
            require(module not in original, 'Duplicate original module')
            original[module] = data
    expected_originals = {name for name in sources if not name.startswith('OAI.')}
    require(set(original) == expected_originals == set(mapping['modules']),
            'Original source coverage differs')
    require(set(repairs) <= expected_originals, 'Unknown repaired original')
    generator = runpy.run_path(str(HERE / 'bundle_generator.py'))
    assignment = {name: row['bundle'] for name, row in mapping['modules'].items()}
    covered = []
    for bundle in mapping['bundles']:
        imports = sorted({assignment.get(dep, dep) for name in bundle['originals']
                          for dep in mapping['modules'][name]['imports']}
                         - {bundle['module']})
        require(imports == bundle['imports'], 'Remapped imports differ')
        text = '/- Packaging rehearsal. Original notices retained; separate replay required. -/\n'
        text += ''.join('import ' + dep + '\n' for dep in imports)
        for name in bundle['originals']:
            covered.append(name)
            row = mapping['modules'][name]
            require(row['source_sha256'] == sources[name]['sha256']
                    and row['bytes'] == len(original[name])
                    and row['imports'] == sources[name]['imports']
                    and assignment[name] == bundle['module'],
                    'Source-map binding differs: ' + name)
            body, removed = generator['remove_headers'](original[name].decode(), row['imports'])
            require(removed == row['removed_import_lines'], 'Import removal differs')
            repair = repairs.get(name)
            require(repair == row['qualification_repairs'], 'Repair map differs')
            if repair:
                require(repair['source_sha256'] == digest(original[name]),
                        'Repair source differs')
                for change in repair['replacements']:
                    body = generator['apply_change'](body, change, name)
            text += f"\n/- BEGIN ORIGINAL {name}; sha256 {row['source_sha256']} -/\nsection\n"
            text += body + f'\nend\n/- END ORIGINAL {name} -/\n'
        relative = 'src/' + bundle['module'].replace('.', '/') + '.lean'
        actual = (args.candidate / relative).read_bytes()
        require(actual == text.encode() and digest(actual) == bundle['sha256']
                and len(actual) == bundle['bytes'], 'Transformed bundle differs: ' + relative)
    require(len(covered) == len(set(covered)) and set(covered) == expected_originals,
            'Bundle coverage differs')
    actual_files = {}
    for path in args.candidate.rglob('*'):
        require(not path.is_symlink(), 'Symlink in Candidate package')
        if path.is_dir():
            continue
        require(path.is_file(), 'Nonregular Candidate member')
        relative = path.relative_to(args.candidate).as_posix()
        require(re.fullmatch(r'src/Candidate/(?:[A-Z][A-Za-z0-9_]*/)*[A-Z][A-Za-z0-9_]*\.lean', relative),
                'Unexpected Candidate member')
        data = path.read_bytes()
        actual_files[relative] = {'sha256': digest(data), 'bytes': len(data)}
    require(actual_files == package['candidate_files'], 'Candidate inventory differs')
    sizes = [row['bytes'] for row in actual_files.values()]
    require(len(sizes) <= 256 and sum(sizes) <= 10 * 1024**2
            and max(sizes) <= 2 * 1024**2, 'Submission size limit exceeded')
    print(json.dumps({'status': 'PASS', 'original_modules': len(original),
                      'candidate_files': len(sizes), 'candidate_bytes': sum(sizes),
                      'scope': 'Exact packaging reconstruction; not proof verification'}))


if __name__ == '__main__':
    main()
