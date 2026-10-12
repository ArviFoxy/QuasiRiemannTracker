#!/usr/bin/env python3
"""Offline Docker process confinement for independently reviewed proof replay.

The trusted setpriv launcher applies NoNewPrivs after the container runtime's
AppArmor transition and before the requested process starts. No candidate may
supply this module, the image, command, environment or mount allowlist.
"""
from pathlib import Path, PurePosixPath
import json
import hashlib
import os
import resource
import stat
import subprocess
import time
import uuid


def require(ok, message):
    if not ok:
        raise ValueError(message)


def real_path(path):
    path = Path(path).absolute()
    require(path.exists(), 'Missing mount input')
    for parent in (path, *path.parents):
        require(not parent.is_symlink(), 'Mount path contains a symlink')
    require(path.is_dir() or path.is_file(), 'Mount input must be a file or directory')
    require(',' not in str(path) and '\n' not in str(path), 'Unsafe mount path')
    return path


def output_size(roots, maximum, count_limit=150000):
    size, count = 0, 0
    for root in roots:
        for directory, dirs, names in os.walk(root, followlinks=False):
            for name in (*dirs, *names):
                try:
                    info = (Path(directory) / name).lstat()
                except FileNotFoundError:
                    continue
                count += 1
                if stat.S_ISREG(info.st_mode):
                    size += info.st_size
                require(count <= count_limit and size <= maximum,
                        'Sandbox output resource limit exceeded')
    return size


def regular_inventory(root, maximum=24*1024**3, count_limit=150000):
    """Authenticate a stopped phase's regular artifacts before any later read."""
    root = real_path(root)
    inventory, total = {}, 0
    for directory, dirs, names in os.walk(root, followlinks=False):
        for name in (*dirs, *names):
            path = Path(directory) / name
            info = path.lstat()
            require(not stat.S_ISLNK(info.st_mode), 'Artifact symlink rejected')
            require(stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode),
                    'Special artifact rejected')
            if stat.S_ISDIR(info.st_mode):
                continue
            require(info.st_nlink == 1, 'Artifact hard link rejected')
            total += info.st_size
            require(total <= maximum and len(inventory) < count_limit,
                    'Artifact resource limit exceeded')
            with path.open('rb') as handle:
                inventory[str(path.relative_to(root))] = hashlib.file_digest(handle, 'sha256').hexdigest()
    return inventory


def run(*, image, command, readonly, writable, stdout, stderr, cwd='/work',
        environment=None, timeout=600, memory=24*1024**3, cpus=8, pids=256,
        output_limit=24*1024**3, stream_limit=12*1024**2):
    """Run one allowlisted command; supervisor output files stay outside mounts."""
    require(os.getuid() != 0, 'Replay operator must be unprivileged')
    require(image.startswith('sha256:') and len(image) == 71, 'Pin the Docker image ID')
    require(command and command[0].startswith('/'), 'Use an absolute trusted executable')
    require(0 < timeout <= 14400 and 0 < cpus <= 16 and 0 < pids <= 512,
            'Invalid process resource limits')
    require(0 < memory <= 32*1024**3 and 0 < stream_limit <= 32*1024**3,
            'Invalid memory or stream limits')
    stdout, stderr = Path(stdout).absolute(), Path(stderr).absolute()
    require(not stdout.exists() and not stderr.exists(), 'Fresh supervisor outputs required')
    mounts, writes, targets = [], [], set()
    for rw, rows in [(False, readonly), (True, writable)]:
        for source, target in rows:
            source = real_path(source)
            destination = PurePosixPath(target)
            require(destination.is_absolute() and str(destination) == target and
                    '..' not in destination.parts and target not in targets,
                    'Unsafe or repeated container destination')
            require(target not in ['/', '/proc', '/sys', '/dev', '/etc', '/usr', '/bin',
                                   '/lib', '/lib64', '/run', '/var/run', '/var/run/docker.sock', '/home'],
                    'Protected container destination')
            require(not any(destination.is_relative_to(PurePosixPath(other)) or
                            PurePosixPath(other).is_relative_to(destination) for other in targets),
                    'Container mount destinations overlap')
            targets.add(target)
            require(source != Path.home() and source != Path('/') and
                    not str(source).startswith('/var/run'), 'Broad or socket host mount')
            if rw:
                require(source.is_dir(), 'Writable grants must be directories')
                writes.append(source)
            require(not stdout.is_relative_to(source) and not stderr.is_relative_to(source),
                    'Supervisor output is visible inside the container')
            mounts.append((source, target, rw))
    for source in writes:
        require(sum(source.is_relative_to(other) or other.is_relative_to(source)
                    for other, _, _ in mounts) == 1, 'Writable mount overlaps another grant')
    name = 'qrh-replay-' + uuid.uuid4().hex
    args = ['docker', 'create', '--name', name, '--network', 'none', '--read-only', '--log-driver', 'none',
            '--cap-drop', 'ALL', '--user', f'{os.getuid()}:{os.getgid()}',
            '--pids-limit', str(pids), '--memory', str(memory), '--memory-swap', str(memory),
            '--cpus', str(cpus), '--ulimit', f'fsize={output_limit}:{output_limit}',
            '--ulimit', 'nofile=65536:65536', '--tmpfs', '/tmp:rw,nosuid,nodev,noexec,size=256m',
            '--workdir', cwd]
    allowed_env = {'PATH', 'HOME', 'TMPDIR', 'LANG', 'LEAN_PATH', 'LEAN_NUM_THREADS',
                   'LEAN_ABORT_ON_PANIC', 'LD_LIBRARY_PATH'}
    for key, value in (environment or {}).items():
        require(key in allowed_env and isinstance(value, str) and '\x00' not in value,
                'Environment is not allowlisted')
        args += ['--env', key + '=' + value]
    for source, target, rw in mounts:
        args += ['--mount', f'type=bind,src={source},dst={target}' + ('' if rw else ',readonly')]
    args += [image, '/usr/bin/setpriv', '--no-new-privs', *command]
    subprocess.run(args, check=True, capture_output=True, text=True, timeout=60)
    started = time.monotonic()
    try:
        configured = json.loads(subprocess.check_output(['docker', 'inspect', name], text=True))[0]
        settings = configured['HostConfig']
        require(configured['Image'] == image and settings['NetworkMode'] == 'none' and
                settings['ReadonlyRootfs'] and settings['CapDrop'] == ['ALL'] and
                not settings['Privileged'] and settings['Memory'] == memory and
                settings['MemorySwap'] == memory and settings['PidsLimit'] == pids and
                settings['NanoCpus'] == cpus*10**9,
                'Docker did not preserve the reviewed security policy')
        require(not settings.get('CapAdd') and settings.get('PidMode') != 'host' and
                settings.get('IpcMode') != 'host' and settings.get('UsernsMode') != 'host' and
                not any('unconfined' in value for value in settings.get('SecurityOpt') or []) and
                settings.get('LogConfig', {}).get('Type') == 'none' and
                settings.get('Tmpfs') == {'/tmp': 'rw,nosuid,nodev,noexec,size=256m'},
                'Docker isolation or logging configuration differs')
        require(configured['Config']['User'] == f'{os.getuid()}:{os.getgid()}' and
                configured['Path'] == '/usr/bin/setpriv' and
                configured['Args'] == ['--no-new-privs', *command],
                'Docker changed the trusted launcher')
        actual = sorted((r['Source'], r['Destination'], r['RW']) for r in configured['Mounts']
                        if r['Type'] == 'bind')
        require(actual == sorted((str(s), t, rw) for s, t, rw in mounts),
                'Container bind mounts differ from the allowlist')
        def stream_bound():
            resource.setrlimit(resource.RLIMIT_FSIZE, (stream_limit, stream_limit))
        with stdout.open('xb') as out, stderr.open('xb') as err:
            proc = subprocess.Popen(['docker', 'start', '-a', name], stdout=out, stderr=err,
                                    preexec_fn=stream_bound)
            try:
                while proc.poll() is None:
                    require(time.monotonic() - started <= timeout, 'Sandbox timed out')
                    output_size(writes, output_limit)
                    time.sleep(1)
            except BaseException:
                subprocess.run(['docker', 'kill', name], capture_output=True, timeout=30)
                proc.wait(timeout=30)
                raise
        final = json.loads(subprocess.check_output(['docker', 'inspect', name], text=True))[0]
        require(not final['State']['OOMKilled'], 'Sandbox exceeded memory limit')
        require(proc.returncode == final['State']['ExitCode'], 'Container transport failed')
        output_size(writes, output_limit)
        require(stdout.stat().st_size < stream_limit and stderr.stat().st_size < stream_limit,
                'Supervisor output exceeded its bound')
        return {'exit_code': final['State']['ExitCode'], 'image': image,
                'elapsed_seconds': round(time.monotonic() - started, 3),
                'isolation': 'Docker network none, read-only root, nonroot, caps0, seccomp, setpriv NoNewPrivs',
                'memory_bytes': memory, 'cpu_limit': cpus, 'pids_limit': pids,
                'timeout_seconds': timeout, 'output_limit_bytes': output_limit,
                'stream_limit_bytes': stream_limit}
    finally:
        subprocess.run(['docker', 'rm', '-f', name], check=True, capture_output=True, timeout=30)
