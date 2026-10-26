#!/usr/bin/env bash
set -euo pipefail
umask 077

if [[ "$(id -u)" != 10001 ]]; then
  echo "Runner must execute as the unprivileged runner user." >&2
  exit 1
fi

# The image and the large bundled Node runtimes remain read-only. Copying the
# listener binaries gives .NET a writable runner root for its private config,
# logs and work directory. Every invocation starts with a new tmpfs.
cp -a /opt/runner/bin /runner/bin
ln -s /opt/runner/externals /runner/externals
mkdir -p "$HOME" /runner/_work /runner/toolcache/node/22.22.1 "$PLAYWRIGHT_BROWSERS_PATH"
ln -s /opt/node /runner/toolcache/node/22.22.1/x64
touch /runner/toolcache/node/22.22.1/x64.complete
# Playwright needs a writable cache root for install locks and package links,
# even when its browser binaries are already present in the immutable image.
for browser in /opt/playwright/*; do
  ln -s "$browser" "$PLAYWRIGHT_BROWSERS_PATH/$(basename "$browser")"
done
printf '%s\n' "$PATH" > /runner/.path
: > /runner/.env

if [[ "${1:-}" == "--self-test" ]]; then
  python3 - <<'PY'
import glob
import json
import os
from pathlib import Path
import subprocess

status = dict(line.split(":", 1) for line in Path("/proc/self/status").read_text().splitlines())
root_mount = next(line.split() for line in Path("/proc/mounts").read_text().splitlines() if line.split()[1] == "/")
cpu_quota, cpu_period = Path("/sys/fs/cgroup/cpu.max").read_text().split()
checks = {
    "unprivileged_uid": os.getuid() == 10001,
    "read_only_root": "ro" in root_mount[3].split(","),
    "no_capabilities": all(int(status[key].strip(), 16) == 0 for key in ("CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb")),
    "no_new_privileges": status["NoNewPrivs"].strip() == "1",
    "seccomp_enabled": status["Seccomp"].strip() == "2",
    "apparmor_enabled": Path("/proc/self/attr/current").read_text().startswith("docker-default (enforce)"),
    "no_docker_socket": not any(Path(path).exists() for path in ("/var/run/docker.sock", "/run/docker.sock")),
    "private_cgroup_namespace": Path("/proc/self/cgroup").read_text().strip() == "0::/",
    "bounded_cpu": cpu_quota != "max" and int(cpu_quota) <= 4 * int(cpu_period),
    "bounded_memory": int(Path("/sys/fs/cgroup/memory.max").read_text()) <= 8 * 1024**3,
    "swap_disabled": Path("/sys/fs/cgroup/memory.swap.max").read_text().strip() == "0",
    "bounded_processes": int(Path("/sys/fs/cgroup/pids.max").read_text()) <= 512,
    "node_available": subprocess.check_output(["node", "--version"], text=True).strip() == "v22.22.1",
    "runner_executable": subprocess.check_output(["/runner/bin/Runner.Listener", "--version"], text=True,
        env={**os.environ, "ACTIONS_RUNNER_PRINT_LOG_TO_STDOUT": "0"}).strip() == "2.338.0",
}
browser_paths = glob.glob("/opt/playwright/chromium-*/chrome-linux/chrome") + glob.glob("/opt/playwright/chromium-*/chrome-linux64/chrome")
checks["chromium_installed"] = len(browser_paths) == 1
if browser_paths:
    browser = subprocess.run([browser_paths[0], "--headless", "--no-sandbox", "--disable-gpu", "--dump-dom", "data:text/html,<p>runner-browser-ok</p>"], capture_output=True, text=True, timeout=30)
    checks["chromium_runs"] = browser.returncode == 0 and "runner-browser-ok" in browser.stdout
print(json.dumps(checks, indent=2))
if not all(checks.values()):
    raise SystemExit("Runner isolation self-test failed")
PY
  exit 0
fi

if [[ "${1:-}" == "--register" && "$#" == 1 ]]; then
  # A separate, job-free container consumes this short-lived token. Its only
  # stdout is the new ephemeral runner identity for the trusted host launcher.
  IFS= read -r registration_token || [[ -n "${registration_token:-}" ]]
  if [[ ! "$registration_token" =~ ^[A-Za-z0-9_]{20,128}$ ]]; then
    echo "Invalid runner registration token format." >&2
    exit 1
  fi
  runner_name="${QRH_RUNNER_NAME:-Zoo-MM-QuasiRiemannTracker-docker-${HOSTNAME}}"
  if [[ ! "$runner_name" =~ ^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$ ]]; then
    echo "Invalid runner name format." >&2
    exit 1
  fi
  /runner/bin/Runner.Listener configure \
    --unattended \
    --url https://github.com/GTimG/QuasiRiemannTracker \
    --token "$registration_token" \
    --name "$runner_name" \
    --labels qrh-docker \
    --work _work \
    --ephemeral \
    --disableupdate >&2
  unset registration_token
  python3 -c 'import json; assert json.load(open("/runner/.runner", encoding="utf-8-sig")).get("ephemeral") is True, "Registration must be ephemeral"'
  exec tar --create --file=- --directory=/runner -- .runner .credentials .credentials_rsaparams
fi

if [[ "$#" != 0 ]]; then
  echo "Usage: runner-entrypoint [--self-test|--register]" >&2
  exit 1
fi

# Receive only the existing runner identity over stdin. No credential appears
# in image layers, Docker environment/arguments, or a bind mount. Never source
# the host runner's .env or .path files.
python3 -c '
import json
import os
import sys
import tarfile

required = {".runner", ".credentials", ".credentials_rsaparams"}
received = set()
with tarfile.open(fileobj=sys.stdin.buffer, mode="r|") as archive:
    for member in archive:
        if member.name not in required or member.name in received or not member.isfile():
            raise SystemExit("Unexpected runner bootstrap archive entry")
        if not 0 < member.size <= 262144:
            raise SystemExit("Invalid runner bootstrap file size")
        source = archive.extractfile(member)
        content = source.read()
        if member.name == ".runner":
            settings = json.loads(content.decode("utf-8-sig"))
            if settings.get("ephemeral") is not True:
                raise SystemExit("Persistent runner identities are not permitted")
            settings["workFolder"] = "_work"
            settings["disableUpdate"] = True
            content = json.dumps(settings).encode("utf-8")
        with open(os.path.join("/runner", member.name), "xb") as destination:
            destination.write(content)
        received.add(member.name)
if received != required:
    raise SystemExit("Incomplete runner bootstrap archive")
'

# GitHub assigns this registered ephemeral identity at most one job. Do not
# wrap the listener in a retry loop or reuse this container after it exits.
exec /runner/bin/Runner.Listener run
