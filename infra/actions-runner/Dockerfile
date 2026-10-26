FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG RUNNER_VERSION=2.338.0
ARG RUNNER_SHA256=af4b794c1bc41d73d40535e3fe092a39f9679cd8d965954c2aca25a05ca41d32
ARG NODE_VERSION=22.22.1
ARG NODE_SHA256=9a6bc82f9b491279147219f6a18add1e18424dce90d41d2a5fcd69d4924ba3aa
ARG PLAYWRIGHT_VERSION=1.56.1

ENV DEBIAN_FRONTEND=noninteractive \
    LANG=C.UTF-8 \
    HOME=/runner/home \
    RUNNER_TOOL_CACHE=/runner/toolcache \
    AGENT_TOOLSDIRECTORY=/runner/toolcache \
    PLAYWRIGHT_BROWSERS_PATH=/runner/playwright \
    PATH=/opt/node/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

# All elevated package installation happens during image construction. Jobs run
# without sudo, capabilities, a Docker client/socket, or host filesystem mounts.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates curl git jq libicu74 liblttng-ust1t64 libssl3t64 \
       libunwind8 procps python3 tar unzip util-linux xz-utils zlib1g \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /opt/node /opt/runner /opt/playwright /runner

RUN curl --fail --silent --show-error --location \
      "https://nodejs.org/dist/v${NODE_VERSION}/node-v${NODE_VERSION}-linux-x64.tar.xz" \
      --output /tmp/node.tar.xz \
    && echo "${NODE_SHA256}  /tmp/node.tar.xz" | sha256sum --check --strict \
    && tar --extract --xz --file /tmp/node.tar.xz --strip-components=1 --directory /opt/node \
    && rm /tmp/node.tar.xz \
    && curl --fail --silent --show-error --location \
      "https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz" \
      --output /tmp/runner.tar.gz \
    && echo "${RUNNER_SHA256}  /tmp/runner.tar.gz" | sha256sum --check --strict \
    && tar --extract --gzip --file /tmp/runner.tar.gz --directory /opt/runner \
    && rm /tmp/runner.tar.gz

RUN HOME=/tmp/build-home PLAYWRIGHT_BROWSERS_PATH=/opt/playwright npm exec --yes --package="playwright@${PLAYWRIGHT_VERSION}" -- \
      playwright install --with-deps chromium \
    && rm -rf /tmp/build-home /var/lib/apt/lists/* \
    && chmod -R a+rX /opt/node /opt/runner /opt/playwright \
    && groupadd --gid 10001 runner \
    && useradd --uid 10001 --gid 10001 --home-dir /runner/home --no-create-home --shell /bin/bash runner

COPY --chmod=0555 entrypoint.sh /usr/local/bin/runner-entrypoint

USER 10001:10001
WORKDIR /runner
# Apply NNP after Docker enters its AppArmor profile: snap-packaged Docker
# cannot make that profile transition when Docker sets NNP before exec.
ENTRYPOINT ["/usr/bin/setpriv", "--no-new-privs", "/usr/local/bin/runner-entrypoint"]
