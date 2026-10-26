"""Credential-boundary and lifecycle tests without Docker or GitHub access."""

import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import manage


def identity_archive(settings=None, *, entries=None, bom=False):
    settings = settings if settings is not None else {
        "agentId": 1,
        "ephemeral": True,
        "disableUpdate": True,
        "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
    }
    encoded = json.dumps(settings).encode("utf-8-sig" if bom else "utf-8")
    if entries is None:
        entries = [
            (".runner", encoded, tarfile.REGTYPE),
            (".credentials", b'{"test": "credential"}', tarfile.REGTYPE),
            (".credentials_rsaparams", b'{"test": "key"}', tarfile.REGTYPE),
        ]
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w") as archive:
        for name, content, kind in entries:
            item = tarfile.TarInfo(name)
            item.type = kind
            if item.isfile():
                item.size = len(content)
            elif kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                item.linkname = "/outside-runner"
            archive.addfile(item, io.BytesIO(content) if item.isfile() else None)
    return output.getvalue()


class IdentityBoundaryTests(unittest.TestCase):
    def test_accepts_only_repository_ephemeral_identity_including_utf8_bom(self):
        for bom in (False, True):
            with self.subTest(bom=bom):
                data = identity_archive(bom=bom)
                self.assertEqual(manage.validate_identity(data), data)

    def test_rejects_reusable_and_automatically_updating_identities(self):
        base = {
            "ephemeral": True,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        }
        for field in ("ephemeral", "disableUpdate"):
            for value in (False, None, "true", 1):
                with self.subTest(field=field, value=value):
                    with self.assertRaises(RuntimeError):
                        manage.validate_identity(identity_archive({**base, field: value}))
            with self.subTest(field=field, value="missing"):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive({k: v for k, v in base.items() if k != field}))

    def test_rejects_other_repositories_and_misleading_urls(self):
        for repository in (
            "https://github.com/attacker/repository",
            "https://github.com/GTimG",
            "http://github.com/GTimG/QuasiRiemannTracker",
            "https://github.com.evil.test/GTimG/QuasiRiemannTracker",
            "https://github.com/GTimG/QuasiRiemannTracker/../other",
            "https://github.com/GTimG/QuasiRiemannTracker?repository=other",
            "",
        ):
            with self.subTest(repository=repository):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive({
                        "ephemeral": True, "disableUpdate": True, "gitHubUrl": repository,
                    }))

    def test_rejects_extra_missing_duplicate_and_path_escape_entries(self):
        good = [
            (".runner", b"{}", tarfile.REGTYPE),
            (".credentials", b"{}", tarfile.REGTYPE),
            (".credentials_rsaparams", b"{}", tarfile.REGTYPE),
        ]
        attacks = [good[:2], good + [(".env", b"injected", tarfile.REGTYPE)]]
        for name in (".runner", "../.credentials_rsaparams", "/.credentials_rsaparams", "./.credentials_rsaparams"):
            attacks.append(good[:2] + [(name, b"{}", tarfile.REGTYPE)])
        for entries in attacks:
            with self.subTest(names=[entry[0] for entry in entries]):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=entries))

    def test_rejects_link_device_and_directory_entries(self):
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE):
            with self.subTest(kind=kind):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=[
                        (".runner", b"{}", tarfile.REGTYPE),
                        (".credentials", b"{}", tarfile.REGTYPE),
                        (".credentials_rsaparams", b"", kind),
                    ]))

    def test_rejects_empty_oversized_and_unbounded_bootstrap_data(self):
        for content in (b"", b"x" * 262145):
            with self.subTest(size=len(content)):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=[
                        (".runner", b"{}", tarfile.REGTYPE),
                        (".credentials", b"{}", tarfile.REGTYPE),
                        (".credentials_rsaparams", content, tarfile.REGTYPE),
                    ]))
        with self.assertRaises(RuntimeError):
            manage.validate_identity(b"x" * (1024 * 1024 + 1))


class IdentityLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.state = Path(self.temporary.name)
        self.registered = []
        self.started = []
        for target, value in (("STATE", self.state), ("STOPPING", False)):
            patcher = patch.object(manage, target, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        for target in ("ensure_proxy", "signal.signal", "time.sleep"):
            patcher = patch("manage." + target)
            patcher.start()
            self.addCleanup(patcher.stop)

    def register_identity(self):
        data = identity_archive({
            "agentId": len(self.registered) + 1,
            "ephemeral": True,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        })
        self.registered.append(data)
        manage.private_write(self.state / "pending-identity.tar", data)

    def record_launch(self, args, **kwargs):
        if args[:len(manage.COMPOSE)] == manage.COMPOSE:
            self.assertFalse((self.state / "pending-identity.tar").exists())
            self.started.append(kwargs["input"])
            return True
        return False

    def test_every_completed_job_consumes_identity_and_registers_a_new_one(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs) and len(self.started) == 2:
                manage.STOPPING = True
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(self.started, self.registered)
        self.assertEqual(len(self.started), 2)
        self.assertNotEqual(*self.started)
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_failed_job_identity_is_not_reused_after_supervisor_restart(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                if len(self.started) == 1:
                    return subprocess.CompletedProcess(args, 17)
                manage.STOPPING = True
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                with self.assertRaises(RuntimeError):
                    manage.serve()
                self.assertFalse((self.state / "pending-identity.tar").exists())
                manage.serve()
        self.assertEqual(len(self.started), 2)
        self.assertNotEqual(*self.started)

    def test_interrupted_container_start_never_leaves_reusable_credentials(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                raise OSError("container startup interrupted")
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                with self.assertRaises(OSError):
                    manage.serve()
        self.assertEqual(len(self.started), 1)
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_watchdog_removes_timed_out_container_and_rotates_identity(self):
        events = []

        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                events.append("launch")
                if len(self.started) == 1:
                    raise subprocess.TimeoutExpired(args, 7200)
                manage.STOPPING = True
            elif args == ["docker", "rm", "--force", manage.CONTAINER]:
                events.append("remove")
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(len(self.started), 2)
        self.assertEqual(self.started, self.registered)
        self.assertNotEqual(*self.started)
        first_launch = events.index("launch")
        second_launch = events.index("launch", first_launch + 1)
        self.assertIn("remove", events[first_launch + 1:second_launch])
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_registration_failure_cannot_fall_back_to_an_old_identity(self):
        with patch.object(manage, "register", side_effect=RuntimeError("registration unavailable")):
            with patch.object(manage.subprocess, "run") as execute:
                with self.assertRaises(RuntimeError):
                    manage.serve()
                execute.assert_not_called()
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_shutdown_during_registration_does_not_launch_a_job(self):
        def register_then_stop():
            self.register_identity()
            manage.STOPPING = True

        def execute(args, **kwargs):
            self.record_launch(args, **kwargs)
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=register_then_stop):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(self.started, [])


class RegistrationIsolationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.state = Path(temporary.name)
        patcher = patch.object(manage, "STATE", self.state)
        patcher.start()
        self.addCleanup(patcher.stop)
        patcher = patch.object(manage, "registration_token", return_value="registration-token-test-secret")
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_registration_secret_is_only_sent_to_job_free_container_stdin(self):
        identity = identity_archive()
        calls = []

        def execute(args, **kwargs):
            calls.append((args, kwargs))
            return subprocess.CompletedProcess(args, 0, stdout=identity)

        with patch.object(manage.subprocess, "run", side_effect=execute):
            manage.register()
        registration = [(args, kwargs) for args, kwargs in calls if args[:len(manage.COMPOSE)] == manage.COMPOSE]
        self.assertEqual(len(registration), 1)
        args, options = registration[0]
        self.assertEqual(args[-1], "--register")
        self.assertNotIn("registration-token-test-secret", str(args))
        self.assertNotIn("registration-token-test-secret", str(options.get("env", {})))
        self.assertEqual(options["input"], b"registration-token-test-secret\n")
        pending = self.state / "pending-identity.tar"
        self.assertEqual(pending.read_bytes(), identity)
        self.assertNotIn(b"registration-token-test-secret", pending.read_bytes())
        self.assertEqual(pending.stat().st_mode & 0o777, 0o600)

    def test_invalid_registration_output_is_never_published_for_jobs(self):
        data = identity_archive({
            "ephemeral": False,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        })
        with patch.object(manage.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, stdout=data)):
            with self.assertRaises(RuntimeError):
                manage.register()
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_registration_timeout_removes_container_and_publishes_no_identity(self):
        cleanup = []

        def execute(args, **kwargs):
            if args[:len(manage.COMPOSE)] == manage.COMPOSE:
                raise subprocess.TimeoutExpired(args, 120)
            cleanup.append(args)
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage.subprocess, "run", side_effect=execute):
            with self.assertRaises(subprocess.TimeoutExpired):
                manage.register()
        self.assertIn(["docker", "rm", "--force", "qrh-runner-register"], cleanup)
        self.assertFalse((self.state / "pending-identity.tar").exists())


if __name__ == "__main__":
    unittest.main()
