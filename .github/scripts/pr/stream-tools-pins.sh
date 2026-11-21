set -euo pipefail
# This job's verdict is whatever these tools say, so they are pinned by version and by the hash of the
# file pip installs.  Unpinned, a release that renames a message or adds a rule turns a red tree green
# or a green tree red with no commit here: the pull request that added this job records one such case,
# where `ruff format --check` was read for a phrase ruff 0.17.3 no longer prints.  `--only-binary`
# keeps pip to the wheels those hashes name.
#
# The versions and hashes are NOT written here.  dev/stream/uv.lock is what resolves this package's
# environment, so the list the job installs is a group of dev/stream/pyproject.toml (`ci`) exported
# from that lock.  Written out here instead, the list is a second copy of the lock, and the copy
# drifts: it pinned pytest 8.4.2 while the lock resolved 9.2.0, a major apart, under a comment
# claiming the two agreed (the quality review of pull request 496, round 5).  Raise a version with
# `uv lock --upgrade-package <name>` in dev/stream and this job takes it with no edit.
#
# uv itself is the one pin this file writes, because uv is what reads the lock and so cannot come out
# of it: it resolves this repository's dependencies rather than being one of them.  It is installed
# for its own sake too -- uv builds the environment a box runs from (src/ossv/tools.py,
# install_package), and without it a deploy falls back to `python3 -m venv` and pip and resolves
# afresh; tests/test_ossv_tools.py takes the same branch, so a job without uv proves only the
# fallback.  The hash is the manylinux x86_64 wheel, which is what a GitHub runner takes.
cat > "$RUNNER_TEMP/uv-requirement.txt" <<'UV_REQUIREMENT'
uv==0.13.6 \
    --hash=sha256:22759b8895e1103578de6fb4cd27e94b4399d021023378d29f01333717751fba
UV_REQUIREMENT
python -m pip install --quiet --require-hashes --only-binary=:all: -r "$RUNNER_TEMP/uv-requirement.txt"
# `--locked`: refuse to re-resolve AND fail when the lock no longer matches pyproject.toml, so a `ci`
# group changed without `uv lock` fails the job instead of quietly installing the old list.  `--frozen`
# alone is only the first half: measured, an unlocked `ci` dependency exports the stale set and exits 0,
# while `--locked` exits 2 with "The lockfile at uv.lock needs to be updated" (496, round 5.2, R5-3).
uv export --project head/dev/stream --locked --only-group ci --no-emit-project \
  --output-file "$RUNNER_TEMP/stream-tools-requirements.txt"
python -m pip install --quiet --require-hashes --only-binary=:all: \
  -r "$RUNNER_TEMP/stream-tools-requirements.txt"
ruff --version && uv --version && python -m pytest --version
