#!/usr/bin/env python3
"""Exercise the actual runner image/network without registering a runner.

Run from any directory after starting the proxy:
  python3 check_network.py --host-ip YOUR_HOST_PUBLIC_IP

Uses one temporary container with the same Compose restrictions as a job. It
passes no credentials, mounts no host files, and removes only its own container.
"""

import argparse
import ipaddress
import json
from pathlib import Path
import selectors
import subprocess
import sys
import uuid

NETWORK = "qrh-runner-internal"
CONTAINER_CHECKS = r'''
import json
from pathlib import Path
import os
import socket
import subprocess
import sys
import urllib.parse
import urllib.request

print("READY", flush=True)
if sys.stdin.readline().strip() != "CONTINUE":
    raise SystemExit("Host verification did not complete")

failures = []

def check(name, function):
    try:
        function()
        print("PASS " + name, flush=True)
    except Exception as error:
        failures.append(name)
        print("FAIL " + name + ": " + str(error), flush=True)

def routes():
    rows = Path("/proc/net/route").read_text().splitlines()[1:]
    assert all(row.split()[1] != "00000000" for row in rows), "IPv4 default route exists"
    assert Path("/proc/sys/net/ipv6/conf/eth0/disable_ipv6").read_text().strip() == "1", "eth0 IPv6 enabled"
    assert all(row.split()[-1] == "lo" for row in Path("/proc/net/if_inet6").read_text().splitlines()), "non-loopback IPv6 address exists"

def privileges():
    status = Path("/proc/self/status").read_text()
    assert "NoNewPrivs:\t1" in status
    assert "CapEff:\t0000000000000000" in status
    assert os.getuid() == 10001

def https(url):
    request = urllib.request.Request(url, headers={"User-Agent": "qrh-runner-network-check"})
    with urllib.request.urlopen(request, timeout=15) as response:
        assert response.status == 200, response.status
        response.read(16)

def proxy_denied(authority):
    proxy = urllib.parse.urlsplit(os.environ["https_proxy"])
    with socket.create_connection((proxy.hostname, proxy.port), timeout=3) as client:
        client.sendall(("CONNECT " + authority + " HTTP/1.1\r\nHost: " + authority + "\r\n\r\n").encode("ascii"))
        response = client.recv(1024)
        assert response.startswith(b"HTTP/1.1 403 "), response[:100]

def direct_denied(host, port):
    try:
        client = socket.create_connection((host, port), timeout=1.5)
    except OSError:
        return
    client.close()
    raise AssertionError("direct connection succeeded")

def node_fetch():
    source = """
      if (process.env.NODE_USE_ENV_PROXY !== '1') throw Error('NODE_USE_ENV_PROXY missing');
      for (const url of ['https://api.github.com/rate_limit', 'https://registry.npmjs.org/typescript/latest']) {
        const response = await fetch(url, { signal: AbortSignal.timeout(15000) });
        if (response.status !== 200) throw Error(`${url}: ${response.status}`);
        await response.body.cancel();
      }
    """
    result = subprocess.run(["node", "--input-type=module", "-e", source], capture_output=True, text=True, timeout=35)
    assert result.returncode == 0, result.stderr[-1800:]

check("no default route; only loopback IPv6", routes)
check("nonroot, no capabilities, no_new_privs", privileges)
check("HTTPS GitHub API via proxy", lambda: https("https://api.github.com/rate_limit"))
check("HTTPS npm registry via proxy", lambda: https("https://registry.npmjs.org/typescript/latest"))
check("Node native fetch honors proxy", node_fetch)
for authority in ("example.com:443", "169.254.169.254:443", "127.0.0.1:443", "192.168.1.1:443"):
    check("proxy rejects " + authority, lambda authority=authority: proxy_denied(authority))
for host in sys.argv[1:]:
    check("proxy rejects host address " + host, lambda host=host: proxy_denied(host + ":443"))
    check("direct host connection blocked " + host, lambda host=host: direct_denied(host, 443))
check("direct public Internet blocked", lambda: direct_denied("1.1.1.1", 443))
check("direct metadata connection blocked", lambda: direct_denied("169.254.169.254", 80))
check("direct private network blocked", lambda: direct_denied("192.168.1.1", 443))
raise SystemExit(bool(failures))
'''


def output_json(command):
    return json.loads(subprocess.check_output(command, text=True, timeout=15))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host-ip", action="append", required=True, help="actual host IP to test; repeat for additional addresses")
    arguments = parser.parse_args()
    host_addresses = [str(ipaddress.IPv4Address(value)) for value in arguments.host_ip]
    network = output_json(["docker", "network", "inspect", NETWORK])[0]
    assert network["Driver"] == "bridge" and network["Internal"]
    assert not network["EnableIPv6"]
    assert network["Options"].get("com.docker.network.bridge.gateway_mode_ipv4") == "isolated"
    assert all(not entry.get("Gateway") for entry in network["IPAM"]["Config"])
    bridge = network["Options"].get("com.docker.network.bridge.name", "br-" + network["Id"][:12])
    interfaces = output_json(["ip", "-j", "address", "show", "dev", bridge])
    assert all(address["family"] != "inet" for interface in interfaces for address in interface["addr_info"]), "host bridge has an IPv4 address"
    print("PASS internal isolated bridge has no IPv4 host address or gateway", flush=True)

    name = "qrh-network-check-" + uuid.uuid4().hex[:12]
    command = [
        "docker", "compose", "-p", "qrh-runner", "-f", str(Path(__file__).with_name("compose.yaml")),
        "run", "--rm", "--no-deps", "-T", "--name", name,
        "--entrypoint", "/usr/bin/setpriv", "runner", "--no-new-privs",
        "python3", "-c", CONTAINER_CHECKS, *host_addresses,
    ]
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    try:
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            if not selector.select(45):
                raise TimeoutError("test container did not start within 45 seconds")
            line = process.stdout.readline()
        if line.strip() != "READY":
            raise RuntimeError("test container failed to initialize: " + line.strip())
        container = output_json(["docker", "inspect", name])[0]
        assert set(container["NetworkSettings"]["Networks"]) == {NETWORK}, "runner has unexpected network attachments"
        assert container["HostConfig"]["ReadonlyRootfs"]
        assert not container["HostConfig"]["Privileged"]
        assert container["HostConfig"]["CapDrop"] == ["ALL"]
        assert not container["HostConfig"].get("Binds"), "host bind mount exists"
        print("PASS runner attached only to isolated network; read-only root; no host mounts", flush=True)
        output, _ = process.communicate("CONTINUE\n", timeout=100)
        print(output, end="")
        return process.returncode
    finally:
        if process.poll() is None:
            process.terminate()
            subprocess.run(["docker", "rm", "--force", name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15, check=False)
            process.wait(timeout=15)


if __name__ == "__main__":
    sys.exit(main())
