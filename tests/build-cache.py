"""Regression and archive authentication tests adapted from PR #35."""
from pathlib import Path
import copy, importlib.util, io, json, os, subprocess, sys, tarfile, tempfile, unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'verifier'))
from standard.build_cache import build_inputs, pack_cache, restore_cache, digest
spec = importlib.util.spec_from_file_location('restore_build', ROOT/'verifier/actions/restore-build.py')
restore = importlib.util.module_from_spec(spec)
spec.loader.exec_module(restore)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.contract = {'build_order':['Submissions.base.Main','Candidate.Main'],
            'module_dependencies':{'Submissions.base.Main':[], 'Candidate.Main':['Submissions.base.Main']},
            'source_files':{'src/Submissions/base/Main.lean':'base', 'src/Candidate/Main.lean':'main'}}
        self.inputs = self.inputs_for(self.contract)
        self.library = self.root/'lib'
        for module in self.contract['build_order']:
            p = self.library/(module.replace('.','/')+'.olean')
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(module.encode())
            Path(str(p)+'.private').write_bytes(b'private')
            Path(str(p)+'.server').write_bytes(b'server')
        self.archive = self.root/'cache.tar.gz'
        pack_cache(self.library, self.archive, self.inputs)

    def inputs_for(self, contract=None, root='/worker', compiler='compiler', dep='mathlib'):
        return build_inputs(contract or self.contract, {'libraries':[root+'/lib']},
            {root+'/lib/Mathlib.olean':dep}, {'source_lean':compiler})

    def test_round_trip(self):
        selected = restore_cache(self.archive, self.root/'restored', self.inputs)
        self.assertEqual(selected, set(self.contract['build_order']))
        self.assertEqual((self.root/'restored/Candidate/Main.olean.private').read_bytes(), b'private')

    def test_changed_source_keeps_shared_dependency(self):
        changed = copy.deepcopy(self.contract)
        changed['source_files']['src/Candidate/Main.lean'] = 'new theorem'
        selected = restore_cache(self.archive, self.root/'restored', self.inputs_for(changed))
        self.assertEqual(selected, {'Submissions.base.Main'})
        self.assertFalse((self.root/'restored/Candidate/Main.olean').exists())

    def test_dependency_change_invalidates_importers(self):
        changed = copy.deepcopy(self.contract)
        changed['source_files']['src/Submissions/base/Main.lean'] = 'changed'
        self.assertEqual(restore_cache(self.archive,self.root/'restored',self.inputs_for(changed)), set())

    def test_metadata_and_commit_do_not_invalidate_modules(self):
        changed = copy.deepcopy(self.contract)
        changed['head_sha'] = 'new head'
        changed['source_files']['metadata.json'] = 'new metadata'
        self.assertEqual(self.inputs, self.inputs_for(changed))

    def test_compiler_and_library_invalidation(self):
        for inputs in [self.inputs_for(compiler='changed'), self.inputs_for(dep='changed')]:
            with self.assertRaisesRegex(ValueError, 'compiler or libraries'):
                restore_cache(self.archive, self.root/'restored', inputs)

    def test_paths_and_library_grouping_are_portable(self):
        self.assertEqual(self.inputs, self.inputs_for(root='/server'))
        grouped = build_inputs(self.contract, {'libraries':['/one','/two']},
            {'/one/Mathlib.olean':'mathlib','/two/Index.ilean':'editor-data'}, {'source_lean':'compiler'})
        self.assertEqual(self.inputs, grouped)

    def rewrite(self, transform):
        with tarfile.open(self.archive) as source:
            members = [(m, source.extractfile(m).read()) for m in source]
        transform(members)
        with tarfile.open(self.archive, 'w:gz') as target:
            for member, data in members:
                member.size = len(data)
                target.addfile(member, io.BytesIO(data))

    def test_corrupted_output_leaves_no_importable_files(self):
        self.rewrite(lambda members:members.__setitem__(-1,(members[-1][0],b'corrupt')))
        with self.assertRaisesRegex(ValueError,'checksum'):
            restore_cache(self.archive,self.root/'restored',self.inputs)
        self.assertFalse(list((self.root/'restored').rglob('*.olean')))

    def test_rejects_archive_attacks(self):
        for attack in ['traversal','symlink','hardlink','duplicate','missing']:
            pack_cache(self.library,self.archive,self.inputs)
            def change(members):
                if attack == 'traversal':members[1][0].name='../escape'
                if attack == 'symlink':members[1][0].type=tarfile.SYMTYPE
                if attack == 'hardlink':members[1][0].type=tarfile.LNKTYPE
                if attack == 'duplicate':members.append(members[1])
                if attack == 'missing':members.pop()
            self.rewrite(change)
            with self.subTest(attack=attack),self.assertRaises(ValueError):
                restore_cache(self.archive,self.root/'bad',self.inputs)
        self.assertFalse((self.root/'escape').exists())

    def test_rejects_invalid_module_graph(self):
        changed = copy.deepcopy(self.contract)
        changed['module_dependencies']['Submissions.base.Main']=['Candidate.Main']
        with self.assertRaisesRegex(ValueError,'ordering'):
            self.inputs_for(changed)

    def test_incompatible_signed_index_skips_large_download(self):
        out = self.root/'verification'
        (out/'prepared').mkdir(parents=True)
        (out/'profile.json').write_text(json.dumps({'libraries':['/worker/lib']}))
        (out/'prepared/contract.json').write_text(json.dumps(self.contract))
        (out/'prepared/libraries.json').write_text(json.dumps({'/worker/lib/Mathlib.olean':'mathlib'}))
        (out/'tool-pins.json').write_text(json.dumps({'source_lean':'compiler'}))
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with patch.object(restore, 'download') as download, patch.object(restore, 'authenticate',
                    return_value={'environment':'different','modules':{}}):
                restore.main()
                self.assertEqual(download.call_count, 2)
            self.assertNotIn('candidate_cache',json.loads((out/'profile.json').read_text()))
        finally:
            os.chdir(previous)

    def test_signature_binds_archive_and_rejects_wrong_key(self):
        key, public = self.root/'key.pem',self.root/'public.pem'
        subprocess.run(['openssl','genpkey','-algorithm','ED25519','-out',str(key)],check=True)
        subprocess.run(['openssl','pkey','-in',str(key),'-pubout','-out',str(public)],check=True)
        sha=digest(self.archive)
        index=self.root/'cache.json';signature=self.root/'cache.sig'
        index.write_text(json.dumps({'schema_version':1,'archive':sha+'.tar.gz','sha256':sha,'size':self.archive.stat().st_size}))
        subprocess.run(['openssl','pkeyutl','-sign','-inkey',str(key),'-rawin','-in',str(index),'-out',str(signature)],check=True)
        self.assertEqual(restore.authenticate(index,signature,public)['sha256'],sha)
        with self.assertRaises(subprocess.CalledProcessError):
            restore.authenticate(index,signature)  # Production key cannot accept a test signature.
        index.write_text(index.read_text()+' ')
        with self.assertRaises(subprocess.CalledProcessError):
            restore.authenticate(index,signature,public)


unittest.main()
