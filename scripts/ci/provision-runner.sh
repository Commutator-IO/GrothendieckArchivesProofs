#!/usr/bin/env bash
# One-time setup of the self-hosted Lean CI runner (issue #34): Ubuntu LTS, 32 cores, 128 GB, SSD >= 256 GB.
# Run as root:  RUNNER_TOKEN=<registration token> ./provision-runner.sh
# The token comes from Settings > Actions > Runners > New self-hosted runner (valid one hour); it is
# the only credential the machine holds. The runner is registered with --ephemeral (one job, then it
# exits): a plain systemd service does not re-register it, so for fork PRs use Actions Runner Controller
# on AKS or a VM re-imaged between jobs (issue #34, Security); until then, keep fork PRs on approval.
set -euo pipefail
: "${RUNNER_TOKEN:?registration token}"
REPO_URL="${REPO_URL:-https://github.com/Commutator-IO/GrothendieckArchivesProofs}"
RUNNER_VERSION="${RUNNER_VERSION:-2.329.0}"   # check https://github.com/actions/runner/releases
LABELS="self-hosted,linux,x64,lean"

apt-get update && apt-get install -y curl git rsync util-linux build-essential
id runner >/dev/null 2>&1 || useradd -m -s /bin/bash runner
install -d -o runner -g runner "${LEAN_CI_STORE:-/var/lib/lean-ci}" /opt/actions-runner

# elan (toolchain of lean-toolchain is installed per job by lean-action)
sudo -u runner bash -c 'command -v elan >/dev/null || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none'

cd /opt/actions-runner
if [ ! -x ./config.sh ]; then
  curl -fsSL -o r.tgz "https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz"
  tar xzf r.tgz && rm r.tgz && chown -R runner:runner .
fi
sudo -u runner ./config.sh --unattended --url "$REPO_URL" --token "$RUNNER_TOKEN" \
  --labels "$LABELS" --name "lean-$(hostname)" --ephemeral --replace
./svc.sh install runner && ./svc.sh start
echo "Done. Firewall: allow outbound only to github.com, *.githubusercontent.com, releases.lean-lang.org, the Mathlib cache and the git hosts of the dependencies."
