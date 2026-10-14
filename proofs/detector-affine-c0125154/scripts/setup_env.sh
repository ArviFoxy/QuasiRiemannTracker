#!/bin/bash
set -ex
ROOT=/home/user/QuasiRiemannTracker
ENV=/home/user/leanbuild
cd $ENV
# toolchain 4.34.1 (standalone, matches verifier)
if [ ! -d lean-4.34.1-linux ]; then
  curl --fail --location --retry 3 https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst -o lean.tar.zst
  echo "47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4  lean.tar.zst" | sha256sum -c
  tar --zstd -xf lean.tar.zst && rm lean.tar.zst
fi
export PATH=$ENV/lean-4.34.1-linux/bin:$PATH
export LEAN_NUM_THREADS=4
sha256sum openai-math/lean/ComparatorChallenges/DirichletSevenEighths.lean
mkdir -p project && cd project
[ -d OAI ] || cp -r ../openai-math/lean/OAI OAI
cp $ROOT/verifier/standard/lake-manifest.json lake-manifest.json
sed 's/roots := #\[`OAI.NumberTheory.DirichletL.Nonvanishing\]/globs := #[`OAI.+]/' $ROOT/verifier/standard/lakefile.lean > lakefile.lean
echo "leanprover/lean4:v4.34.1" > lean-toolchain
mkdir -p .lake/packages
python3 - <<'PY'
import json,subprocess,os
from pathlib import Path
pk=Path('.lake/packages')
for p in json.load(open('lake-manifest.json'))['packages']:
    name=p['name'].strip('«»'); dest=pk/name
    if not dest.exists():
        subprocess.run(['git','init','-q',str(dest)],check=True)
        subprocess.run(['git','-C',str(dest),'fetch','-q','--depth=1',p['url'],p['rev']],check=True)
        subprocess.run(['git','-C',str(dest),'checkout','-q','--detach','FETCH_HEAD'],check=True)
    if name in ['rellich-kondrachov','PrimeNumberTheoremAnd']:
        patch=Path('../openai-math/lean/patches')/(name+'-lean4341.patch')
        if subprocess.run(['git','-C',str(dest),'apply','--reverse','--check',str(patch.resolve())],capture_output=True).returncode:
            subprocess.run(['git','-C',str(dest),'apply',str(patch.resolve())],check=True)
    print('package ok',name,flush=True)
PY
lake exe cache get
echo SETUP_DONE
