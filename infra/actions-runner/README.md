# Isolated GitHub Actions runner

Three runner slots accept jobs concurrently. Each slot uses a fresh Docker
container and ephemeral GitHub runner identity for each job. Node and Chromium
dependencies are installed in the image; jobs need no host sudo. Browser tests
use three Playwright workers per job.

Only `ci.test` uses `[self-hosted, Linux, X64, qrh-docker]`. Publishing and
admission stay on GitHub-hosted VMs because they have write permissions. The
proof verifier stays hosted because its sandbox needs AppArmor management and
delegated cgroups.

## Isolation

- Nonroot, no capabilities, no-new-privileges, Docker seccomp and AppArmor.
- Read-only image, private PID/cgroup namespaces, no host mounts or Docker socket.
- Each job: four CPUs, 8 GiB memory without swap, 512 processes, bounded tmpfs
  and logs. Three jobs total at most 12 CPUs and 24 GiB; each proxy adds a limit
  of 0.5 CPU and 128 MiB.
- Internal network with no direct host, LAN or Internet route. A separate HTTPS
  proxy allows required GitHub, npm, Node and Playwright hosts, checks resolved
  addresses, and blocks private addresses and the host's public addresses.
- Each slot has its own networks and proxy, so jobs cannot connect to each other.
  Host identity files and supervisor locks are also separate for each slot.
- Containers and identities are discarded after one job or two hours, including
  idle time. Registration failure stops the service; identities are never reused.

Docker shares the host kernel. Keep Docker, the kernel and images updated. The
proxy limits destinations but allows uploads to permitted GitHub/Azure services.
Keep personal secrets, host mounts and Docker access out of jobs.

The immutable entrypoint sets `no-new-privs` after Docker's AppArmor transition,
working around [Snap Docker's limitation](https://github.com/canonical/docker-snap#usage).
Registration uses a separate container that never runs jobs. Only its ephemeral
identity files reach the job container; registration tokens and host credentials
stay out of jobs.

## Setup

From the repository root, with Docker access and Python 3:

```sh
python3 infra/actions-runner/manage.py build
```

For automatic registration, authenticate the host's `gh` with repository
runner-administration access. A fine-grained token needs repository
[Administration write permission](https://docs.github.com/en/rest/actions/self-hosted-runners#create-a-registration-token-for-a-repository).
Alternatively, enter a registration token from **Settings → Actions → Runners →
New self-hosted runner** using `python3 infra/actions-runner/manage.py token`.
The hidden prompt saves it mode 0600 under `~/.local/share/qrh-actions-runner/`.
Registration tokens expire after one hour; an already registered runner can
finish its job, but future registrations need a fresh token or admin `gh` login.

```sh
python3 infra/actions-runner/manage.py install-service
python3 infra/actions-runner/manage.py start
python3 infra/actions-runner/manage.py status
```

Installation disables the previous single-slot Docker service and enables
`qrh-actions-runner@1.service` through `qrh-actions-runner@3.service`. User
lingering is required for operation after logout or reboot. Keep the previous
host runner service disabled.

## Operations

```sh
journalctl --user -u 'qrh-actions-runner@*.service' -f
python3 infra/actions-runner/manage.py stop
python3 -m unittest discover -s infra/actions-runner -p 'test_*.py'
```

After a failure, inspect the journal, refresh registration credentials if needed,
and run `manage.py start`. Admins can remove unused offline registrations in
GitHub runner settings.

`start`, `stop` and `status` apply to all three slots. Add `--slot 1`, `--slot 2`
or `--slot 3` to operate on one. To register an identity before starting a slot,
use `manage.py register --slot 1`. Registration tokens are shared on the host;
pending identities and locks live separately under `slot-1/`, `slot-2/`, `slot-3/`.

For image updates, stop the service, update version/checksum pins and rebuild.
Remove only `qrh-runner-proxy-1`, `qrh-runner-proxy-2` and `qrh-runner-proxy-3` to
pick up the new proxy image, then restart. Runner automatic updates are disabled; follow
[GitHub's update requirements](https://docs.github.com/en/actions/reference/runners/self-hosted-runners).
Keep Node 22.22.1 in the image, toolcache and CI configuration in sync for native
fetch proxy support. Keep the prebaked Playwright version in sync with the lockfile.
