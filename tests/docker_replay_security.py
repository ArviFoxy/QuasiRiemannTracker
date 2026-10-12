import importlib.util,pathlib,tempfile,unittest
from unittest.mock import patch
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('sandbox',ROOT/'verifier/docker/sandbox.py');sandbox=importlib.util.module_from_spec(spec);spec.loader.exec_module(sandbox)
class Security(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=pathlib.Path(self.temp.name)
  for n in ['one','two']:(self.root/n).mkdir()
 def call(self,ro=(),rw=()):
  return sandbox.run(image='sha256:'+'a'*64,command=['/bin/true'],readonly=ro,writable=rw,stdout=self.root/'stdout',stderr=self.root/'stderr')
 def rejected(self,reason,ro=(),rw=()):
  with patch.object(sandbox.subprocess,'run',side_effect=AssertionError('container creation reached')):
   with self.assertRaisesRegex(ValueError,reason):self.call(ro,rw)
 def test_read_write_alias(self):self.rejected('Writable mount overlaps',[(self.root/'one','/input')],[(self.root/'one','/output')])
 def test_destination_ancestor(self):self.rejected('destinations overlap',[(self.root/'one','/input'),(self.root/'two','/input/child')])
 def test_destination_descendant(self):self.rejected('destinations overlap',[(self.root/'one','/input/child'),(self.root/'two','/input')])
 def test_system_library_destination(self):self.rejected('Protected container destination',[(self.root/'one','/lib')])
 def test_supervisor_output_hidden(self):self.rejected('Supervisor output is visible',[(self.root,'/input')])
 def test_host_symlink(self):
  (self.root/'link').symlink_to(self.root/'one',target_is_directory=True)
  self.rejected('Mount path contains a symlink',[(self.root/'link','/input')])
 def test_stopped_symlink_inventory(self):
  (self.root/'one/link').symlink_to('/etc/passwd')
  with self.assertRaisesRegex(ValueError,'Artifact symlink rejected'):sandbox.regular_inventory(self.root/'one')
 def test_stopped_directory_symlink_inventory(self):
  (self.root/'one/link').symlink_to('/etc',target_is_directory=True)
  with self.assertRaisesRegex(ValueError,'Artifact symlink rejected'):sandbox.regular_inventory(self.root/'one')
 def test_stopped_fifo_inventory(self):
  import os;os.mkfifo(self.root/'one/fifo')
  with self.assertRaisesRegex(ValueError,'Special artifact rejected'):sandbox.regular_inventory(self.root/'one')
 def test_inventory_binds_content(self):
  (self.root/'one/x').write_bytes(b'x')
  self.assertEqual(sandbox.regular_inventory(self.root/'one'),{'x':'2d711642b726b04401627ca9fbac32f5c8530fb1903cc4db02258717921a4881'})
 def test_inventory_size_limit(self):
  (self.root/'one/x').write_bytes(b'xx')
  with self.assertRaisesRegex(ValueError,'Artifact resource limit'):sandbox.regular_inventory(self.root/'one',maximum=1)
if __name__=='__main__':unittest.main()
