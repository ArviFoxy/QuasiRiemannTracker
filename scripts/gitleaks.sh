#!/bin/sh
# Trusted CI wrapper, invoked only when traces exist. Cache within this checkout;
# candidate files are read as data and never checked out alongside this script.
set -eu
scanner_cache="$(dirname "$0")/../.work/trace-gitleaks-8.30.1"
if [ ! -x "$scanner_cache/gitleaks" ]; then
  # Reserve exit 1 for Gitleaks findings, including when installation fails.
  mkdir -p "$scanner_cache" || exit 2
  curl --fail --silent --show-error --location --retry 2 --max-time 30 \
    https://github.com/gitleaks/gitleaks/releases/download/v8.30.1/gitleaks_8.30.1_linux_x64.tar.gz \
    --output "$scanner_cache/package.tar.gz" || exit 2
  printf '%s  %s\n' 551f6fc83ea457d62a0d98237cbad105af8d557003051f41f3e7ca7b3f2470eb "$scanner_cache/package.tar.gz" | sha256sum --check --status || exit 2
  tar -xzf "$scanner_cache/package.tar.gz" -C "$scanner_cache" gitleaks || exit 2
  rm "$scanner_cache/package.tar.gz" || exit 2
fi
exec "$scanner_cache/gitleaks" "$@"
