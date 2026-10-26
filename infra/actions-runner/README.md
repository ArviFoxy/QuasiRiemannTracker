# Isolated GitHub Actions runner

The host supervisor runs one job at a time, using a fresh Docker container and
ephemeral GitHub runner identity for each job. Node and Chromium dependencies
are installed in the image; jobs need no host sudo.

Only `ci.test` uses `[self-hosted, Linux, X64, qrh-docker]`. Publishing and
admission stay on GitHub-hosted VMs because they have write permissions. The
proof verifier stays hosted because its sandbox needs AppArmor management and
delegated cgroups.

## Isolation

- Nonroot, no capabilities, no-new-privileges, Docker seccomp and AppArmor.
- Read-only image, private PID/cgroup namespaces, no host mounts or Docker socket.
- Four CPUs, 8 GiB memory without swap, 512 processes, bounded tmpfs and logs.
- Internal network with no direct host, LAN or Internet route. A separate HTTPS
  proxy allows required GitHub, npm, Node and Playwright hosts, checks resolved
  addresses, and blocks private addresses and the host's public addresses.
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

The user service is `qrh-actions-runner.service`. User lingering is required for
operation after logout or reboot. Keep the previous host runner service disabled.

## Operations

```sh
journalctl --user -u qrh-actions-runner.service -f
python3 infra/actions-runner/manage.py stop
python3 -m unittest discover -s infra/actions-runner -p 'test_*.py'
```

After a failure, inspect the journal, refresh registration credentials if needed,
and run `manage.py start`. Admins can remove unused offline registrations in
GitHub runner settings.

For image updates, stop the service, update version/checksum pins and rebuild.
Remove only the dedicated `qrh-runner-proxy` container to pick up its new image,
then restart. Runner automatic updates are disabled; follow
[GitHub's update requirements](https://docs.github.com/en/actions/reference/runners/self-hosted-runners).
Keep Node 22.22.1 in the image, toolcache and CI configuration in sync for native
fetch proxy support. Keep the prebaked Playwright version in sync with the lockfile.
