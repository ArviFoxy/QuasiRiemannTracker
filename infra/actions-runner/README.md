# Isolated GitHub Actions runner

The host supervisor starts a fresh Docker container and a fresh **ephemeral
GitHub runner identity for every job**. Dependencies are installed while building
the image. Jobs do not need the host user's sudo permissions.

The `ci.test` job uses `[self-hosted, Linux, X64, qrh-docker]`. The other six jobs
remain on GitHub-hosted Ubuntu VMs: publishing and admission have write
permissions, and the proof verifier requires AppArmor management and writable
delegated cgroups. Those capabilities are deliberately unavailable to this
container.

## Isolation

- Nonroot UID 10001, all Linux capabilities dropped, no-new-privileges enabled,
  default Docker seccomp and enforced AppArmor.
- Read-only image, private PID/cgroup namespaces, no host directories, Docker
  socket, devices, ports, shared caches, or persistent job volumes.
- Four CPUs, 8 GiB total memory, no swap, 512 processes, and bounded temporary
  storage. Docker logs are rotated; the user service rate-limits journal output.
- An internal Docker network with an isolated gateway. Jobs have no direct route
  to the host, LAN, metadata endpoints, or Internet, including by ignoring proxy
  environment variables.
- A separate HTTPS CONNECT proxy permits only required GitHub, npm, Node, and
  Playwright destinations. It validates DNS answers as public, pins the address
  used for connection, and blocks the host's public interface addresses.
- Each container and identity is discarded after one job. A two-hour external
  lifetime limit also bounds a job that interferes with the runner process. This
  limit includes idle listening time. Expired containers rotate to a fresh
  identity; registration failures stop the service without reusing identities.

Docker remains the isolation boundary and shares the host kernel. Keep Docker,
the kernel, and the images updated. The proxy restricts destinations; it does
not prevent uploads to allowed GitHub/Azure services. Never pass personal
secrets to jobs or add host mounts, Docker access, privileged mode, writable
cgroups, or unconfined security profiles.

On Snap Docker, setting no-new-privileges before its AppArmor transition can
prevent every executable from starting. The immutable image entrypoint instead
uses `setpriv --no-new-privs` immediately after that transition, before any job
code runs. The runtime self-test verifies the effective protection. See
[Canonical's documented limitation](https://github.com/canonical/docker-snap#usage).

## Setup

Run these commands from the repository root with Docker access and Python 3:

```sh
python3 infra/actions-runner/manage.py build
python3 infra/actions-runner/manage.py check
python3 infra/actions-runner/check_network.py --host-ip YOUR_HOST_PUBLIC_IP
python3 infra/actions-runner/check_project.py
```

Automatic registration uses the **host's** `gh` authentication. The account
must have repository runner-administration access; ordinary push access is
insufficient. For a fine-grained credential, GitHub documents repository
Administration write permission for the registration-token endpoint. Keep this
credential on the host; it is never passed into either container. See the
[GitHub API requirements](https://docs.github.com/en/rest/actions/self-hosted-runners#create-a-registration-token-for-a-repository).

Alternatively, enter a short-lived token from the repository's **Settings →
Actions → Runners → New self-hosted runner** page:

```sh
python3 infra/actions-runner/manage.py token
```

The prompt hides the token and stores it mode 0600 under
`~/.local/share/qrh-actions-runner/`, outside the checkout. GitHub registration
tokens expire after one hour. An already registered runner can finish its one
job, but subsequent registration needs a fresh token or an admin `gh` login.
The supervisor stops safely if registration is unavailable.

Registration happens in a separate container that never accepts a job. Only
its three ephemeral identity files pass to the job container, over stdin. The
registration token, host environment, and `gh` credentials are excluded.

```sh
python3 infra/actions-runner/manage.py register
python3 infra/actions-runner/manage.py install-service
python3 infra/actions-runner/manage.py start
python3 infra/actions-runner/manage.py status
```

The user service is `qrh-actions-runner.service`. Starting it after logout or
reboot requires systemd user lingering; it is already enabled on this host.
The previous host-installed runner service must remain stopped and disabled.

## Operations and updates

```sh
journalctl --user -u qrh-actions-runner.service -f
python3 infra/actions-runner/manage.py stop
python3 -m unittest discover -s infra/actions-runner -p 'test_*.py'
```

After a failure, inspect the journal, refresh registration authentication if
needed, then run `manage.py start`. A stopped or failed job's identity is never
reused. Unused registrations may remain offline in GitHub; repository admins
can remove those from runner settings. The old host registration can also be
removed there.

To update, stop the service, update the version/checksum pins, rebuild, remove
only the dedicated `qrh-runner-proxy` container so its new image is used, rerun
the checks, then start the service. Never run a global Docker prune. Runner
automatic updates are disabled to keep the image reproducible; GitHub requires
prompt image updates and may stop queueing jobs for outdated versions. See
[GitHub's ephemeral runner and update guidance](https://docs.github.com/en/actions/reference/runners/self-hosted-runners).

Node 22.22.1 is pinned for native `fetch` proxy support. Keep the image, its
toolcache path, and `ci.test`'s `setup-node` version in sync. Playwright 1.56.1
matches the repository lockfile; update the prebaked browser when that changes.

Changing local workflow files does not change GitHub routing until those edits
are committed and pushed.
