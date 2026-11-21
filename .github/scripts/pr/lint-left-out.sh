set -euo pipefail
if [ -n "$RECORD_KEY" ] && [ -z "$SINCE" ]; then
  echo "::error title=re-run this run::the plan job read lint record $RECORD_KEY and chose this job's checkout by it, and that record does not hold here (the step above says why), so lint would read files this checkout leaves out. Re-run the whole run (gh run rerun <id>, not --failed, which keeps the plan job's old answers): its plan job reads the record again and chooses the checkout and the runner by what it finds."
  exit 1
fi
python - "${SINCE:-$BASE}" <<'EOF'
import os, subprocess, sys, time
started = time.monotonic()
git = ["git", "-C", "head", "-c", "core.quotePath=false"]
# a blob that is not here is answered "missing", or fails the checkout; it is not fetched one at a time
quiet = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_LITERAL_PATHSPECS="1")
diff = subprocess.run(git + ["diff", "--no-renames", "--name-only", "-z", sys.argv[1], "HEAD", "--"],
                      check=True, capture_output=True).stdout.split(b"\0")
listed = subprocess.run(git + ["ls-files", "-z", "-t", "--cached"], check=True, capture_output=True).stdout
skipped = {rec[2:] for rec in listed.split(b"\0") if rec.startswith(b"S ")}
want = sorted(p for p in diff if p and p in skipped)
print("%d file(s) that differ from %s are left out of the checkout: checked out here"
      % (len(want), sys.argv[1]), flush=True)
if not want:
    sys.exit(0)
# the blob of each file at HEAD, which the checkout writes
wanted = set(want)
oids = set()
tree = subprocess.run(git + ["ls-tree", "-r", "-z", "HEAD"], check=True, capture_output=True, env=quiet).stdout
for rec in tree.split(b"\0"):
    meta, _, path = rec.partition(b"\t")
    if path in wanted:
        kind, oid = meta.split(b" ")[1:]
        if kind == b"blob":
            oids.add(oid)


def missing(ids):
    listed = subprocess.run(git + ["cat-file", "--batch-check"], input=b"".join(o + b"\n" for o in ids),
                            check=True, capture_output=True, env=quiet).stdout
    return [line.split(b" ")[0] for line in listed.splitlines() if line.endswith(b" missing")]


absent = missing(sorted(oids))
requests = 0
if absent:
    for attempt in (1, 2, 3):
        requests += 1
        r = subprocess.run(git + ["-c", "fetch.negotiationAlgorithm=noop", "fetch", "--no-tags",
                                  "--no-write-fetch-head", "--recurse-submodules=no", "--filter=blob:none",
                                  "--stdin", "origin"], input=b"".join(o + b"\n" for o in absent))
        if r.returncode == 0:
            break
        if attempt < 3:
            print("::warning::the fetch of %d blob(s) from origin failed (try %d of 3). The step tries again."
                  % (len(absent), attempt), flush=True)
            subprocess.run(["sleep", "30" if attempt == 1 else "90"], stdin=subprocess.DEVNULL, check=True)
left = missing(absent)
checkout = 0
if not left:
    checkout = subprocess.run(git + ["checkout", "--ignore-skip-worktree-bits", "--pathspec-from-file=-",
                                     "--pathspec-file-nul", "HEAD", "--"],
                              input=b"\0".join(want) + b"\0", env=quiet).returncode
print("left-out files: %d file(s), %d blob(s), %d missing here, %d fetched in %d request(s), %.1f s"
      % (len(want), len(oids), len(absent), len(absent) - len(left), requests, time.monotonic() - started),
      flush=True)
if left:
    print("::error::%d blob(s) of the left-out files that lint reads could not be fetched from origin, so lint "
          "cannot read them" % len(left))
    sys.exit(1)
if checkout:
    print("::error::git checkout of the %d left-out file(s) that lint reads exited %d" % (len(want), checkout))
    sys.exit(1)
EOF
