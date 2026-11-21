set -euo pipefail
if [ "$EVERY" != true ]; then
  echo "the plan did not name every unit with a made-from record: the tests of dev/licence/ do not run"
  exit 0
fi
if [ "$KIND" = contributor ]; then
  echo "KIND=contributor: the tests of dev/licence/ are code of this change, which this job does not run"
  exit 0
fi
if [ ! -f head/dev/licence/made_from.py ]; then
  echo "no dev/licence/made_from.py in this checkout: no tests of dev/licence/ to run"
  exit 0
fi
# as the records step: no code of the change runs while head/.git/config holds a git credential
rc=0
git -C head config --local --get-regexp '^http\..*\.extraheader$' > /dev/null || rc=$?
case "$rc" in
  1) ;;
  0) echo "::error::head/.git/config holds an http extraheader, a git credential: this job runs no code of the change while it is there"; exit 1 ;;
  *) echo "::error::git config cannot read head/.git/config (exit $rc), so this job runs no code of the change"; exit 1 ;;
esac
rc=0
# as the records step: the tests run with no command file of the runner in their environment
out=$(cd head && env -u GITHUB_OUTPUT -u GITHUB_ENV -u GITHUB_PATH -u GITHUB_STATE -u GITHUB_STEP_SUMMARY \
  timeout 900 python3 -B -m unittest discover -s dev/licence -t dev/licence -v 2>&1) || rc=$?
# What the tests wrote, on stdout and stderr alike.  The runner reads no workflow command between these
# two lines, and the token is this block's alone.
if [ -n "$out" ]; then
  token=$(od -An -tx1 -N16 /dev/urandom | tr -d ' \n')
  echo "::stop-commands::$token"
  printf '%s\n' "$out"
  echo "::$token::"
fi
case "$rc" in
  0) echo "the tests of dev/licence/ passed" ;;
  5) echo "::error::the tests of dev/licence/ exited 5: no test ran, so nothing is passed"; exit 1 ;;
  124) echo "::error::the tests of dev/licence/ did not finish within 900 s and were stopped, so nothing is passed"; exit 1 ;;
  *) echo "::error::the tests of dev/licence/ exited $rc: a test failed, or the tests did not finish"; exit 1 ;;
esac
