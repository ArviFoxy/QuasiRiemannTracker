#!/usr/bin/env python3
"""Run the website checks in the actual isolated image, without host mounts."""

import io
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
files = set(filter(None, subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")))
files.update(str(path.relative_to(ROOT)) for path in (ROOT / "infra/actions-runner").rglob("*")
             if path.is_file() and "__pycache__" not in path.parts)
archive = io.BytesIO()
with tarfile.open(fileobj=archive, mode="w") as output:
    for name in sorted(files):
        if (ROOT / name).is_file():
            output.add(ROOT / name, arcname=name, recursive=False)

script = """
/usr/local/bin/runner-entrypoint --self-test
git clone --quiet --no-checkout https://github.com/GTimG/QuasiRiemannTracker.git /runner/_work/project
cd /runner/_work/project
tar --extract --file=-
git reset --mixed --quiet HEAD
python3 -m unittest discover -s infra/actions-runner -p 'test_*.py' -q
npm ci --ignore-scripts --no-audit --no-fund
QRH_BASE_PATH=/QuasiRiemannTracker/ npm run check
npx playwright install chromium
CI=1 npm run test:browser
QRH_BASE_PATH=/QuasiRiemannTracker/ node scripts/test-deployment.mjs
"""
command = ["docker", "compose", "-p", "qrh-runner", "-f", str(ROOT / "infra/actions-runner/compose.yaml"),
           "run", "--rm", "--no-deps", "-T", "--name", "qrh-runner-validation",
           "--entrypoint", "/usr/bin/setpriv", "runner", "--no-new-privs", "/bin/bash", "-euc", script]
try:
    result = subprocess.run(command, input=archive.getvalue(), timeout=600)
finally:
    subprocess.run(["docker", "rm", "--force", "qrh-runner-validation"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
raise SystemExit(result.returncode)
