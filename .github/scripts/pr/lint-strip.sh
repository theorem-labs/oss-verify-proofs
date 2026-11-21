set -euo pipefail
python3 - <<'EOF'
import collections, functools, hashlib, os, re, subprocess, sys, threading, time

started = time.monotonic()
BASE = os.environ["BASE"]
GIT = ["git", "-C", "head", "-c", "core.quotePath=false"]
# a blob that is not here is answered "missing", not fetched one at a time; present() fetches in bulk
QUIET = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_LITERAL_PATHSPECS="1")
# the rules of dev/licence/made_from.py, the shared generator ("made_from.py" below), written again here:
# this step runs no file of the change.  Its HEADER_LINES, ANTHROPIC, LICENCE and PROGRAM are here, the rules
# of its headerless() are in declarable(), and those of its left_bare() are in left_bare() and declared().
HEADER_LINES = 10
ANTHROPIC = re.compile(r"Copyright \d{4} Anthropic PBC")
LICENCE = re.compile(r"\(\* (?:Copyright \d{4} |SPDX-License-Identifier:|Modified by )")
PROGRAM = re.compile(r"^\(\* (?:Machine-generated data computed|This file states or restates instruction words)",
                     re.M)
TOKEN = re.compile(r'\(\*|\*\)|"')
BLANK = re.compile(r"[ \t\r\n\f]*")
LICENCE_DIR = b"/proofs/provenance/evidence/licence/"
GITLINK = b"160000"
FILE_MODES = (b"100644", b"100755")
count = {"head": 0, "base": 0, "fetched": 0, "requests": 0}


def say(line):
    sys.stdout.buffer.write(line + b"\n")
    sys.stdout.buffer.flush()


def fail(text):
    say(b"::error::" + text.encode())
    sys.exit(1)


def escape(name):
    """A name as data of one workflow command line, as escape() of the made_from job's records step: GitHub
    reads %0A as a new line."""
    return name.replace(b"%", b"%25").replace(b"\r", b"%0D").replace(b"\n", b"%0A")


def git(*args, data=b""):
    r = subprocess.run(GIT + list(args), input=data, stdout=subprocess.PIPE, env=QUIET)
    if r.returncode:
        fail("git %s exited %d, so nothing is passed" % (args[0], r.returncode))
    return r.stdout


def unit_of(path):
    """projects/<p>/<h> of a .v file under its proofs/ and outside proofs/provenance/, else None."""
    parts = path.split(b"/")
    if (len(parts) > 4 and parts[0] == b"projects" and parts[3] == b"proofs" and parts[4] != b"provenance"
            and path.endswith(b".v")):
        return b"/".join(parts[:3])
    return None


def present(oids):
    """Puts every blob of oids in head/.git: the missing ones in one fetch from origin, tried 3 times."""
    def missing(ids):
        listed = git("cat-file", "--batch-check", data=b"".join(o + b"\n" for o in ids))
        return [line.split(b" ")[0] for line in listed.splitlines() if line.endswith(b" missing")]
    want = missing(oids) if oids else []
    if not want:
        return
    count["fetched"] += len(want)
    for attempt in (1, 2, 3):
        count["requests"] += 1
        r = subprocess.run(GIT + ["-c", "fetch.negotiationAlgorithm=noop", "fetch", "--no-tags",
                                  "--no-write-fetch-head", "--recurse-submodules=no", "--filter=blob:none",
                                  "--stdin", "origin"], input=b"".join(o + b"\n" for o in want))
        if r.returncode == 0:
            break
        if attempt < 3:
            say(b"::warning::the fetch of %d blob(s) from origin failed (try %d of 3). The step tries again."
                % (len(want), attempt))
            subprocess.run(["sleep", "30" if attempt == 1 else "90"], stdin=subprocess.DEVNULL, check=True)
    left = missing(want)
    if left:
        fail("%d blob(s) that this step must read could not be fetched from origin, so nothing is passed"
             % len(left))


def blobs(oids, side):
    """(id, bytes) of each blob of oids, in order, from one git cat-file --batch.  One blob is in memory at a
    time, and a thread writes the ids, so neither pipe waits for the other."""
    if not oids:
        return
    p = subprocess.Popen(GIT + ["cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         env=QUIET, bufsize=1 << 20)

    def feed():
        try:
            for o in oids:
                p.stdin.write(o + b"\n")
            p.stdin.close()
        except BrokenPipeError:
            pass
    writer = threading.Thread(target=feed, daemon=True)
    writer.start()
    for o in oids:
        head = p.stdout.readline().split(b" ")
        if len(head) != 3 or head[0] != o or head[1] != b"blob":
            fail("git cat-file did not give the blob %s, so nothing is passed" % o.decode())
        size = int(head[2])
        data = p.stdout.read(size)
        if len(data) != size or p.stdout.read(1) != b"\n":
            fail("git cat-file gave a short blob %s, so nothing is passed" % o.decode())
        count[side] += 1
        yield o, data
    writer.join()
    p.stdout.close()
    if p.wait():
        fail("git cat-file --batch exited %d, so nothing is passed" % p.returncode)


def first_lines(data):
    """The first HEADER_LINES lines of a blob, as made_from.py reads them."""
    i = -1
    for _ in range(HEADER_LINES):
        i = data.find(b"\n", i + 1)
        if i < 0:
            return data.decode("utf-8", "surrogateescape")
    return data[:i].decode("utf-8", "surrogateescape")


def carries(data):
    return ANTHROPIC.search(first_lines(data)) is not None


def declarable(data):
    """Whether left-bare.tsv can declare this file: made_from.py reads it (UTF-8) and its headerless() is
    true of it."""
    head = first_lines(data)
    if ANTHROPIC.search(head) or LICENCE.search(head) or PROGRAM.search(head):
        return False
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return False
    return True


def keys(data):
    """The two texts that pair a deleted and an added file, as SHA-256 digests: (a) the text after the
    leading licence lines, read as made_from.py's licence_lines() reads them but without its test that the
    comment closes on its line, (b) the text after every leading blank and every leading comment, comments
    nested as Rocq nests them (a string in a comment is one token).  A text that is empty or only white space
    is None: it pairs no file."""
    text = data.decode("utf-8", "surrogateescape")
    pos = 0
    for _ in range(HEADER_LINES):
        if not LICENCE.match(text, pos):
            break
        end = text.find("\n", pos)
        pos = len(text) if end < 0 else end + 1
    after_licence = text[pos:]
    i, n = 0, len(text)
    while True:
        i = BLANK.match(text, i).end()
        if not text.startswith("(*", i):
            break
        depth, i = 1, i + 2
        while depth:
            m = TOKEN.search(text, i)
            if m is None:
                i = n
                break
            i = m.end()
            if m.group() == "(*":
                depth += 1
            elif m.group() == "*)":
                depth -= 1
            else:
                close = text.find('"', i)
                i = n if close < 0 else close + 1
    return tuple(hashlib.sha256(t.encode("utf-8", "surrogateescape")).digest() if t.strip() else None
                 for t in (after_licence, text[i:]))


# The rows of the whole tree.  git's own stderr (the rename limit's warning) goes to the log.
diff_file = os.path.join(os.environ["RUNNER_TEMP"], "strip-diff")
with open(diff_file, "wb") as f:
    rc = subprocess.run(GIT + ["diff", "--raw", "-z", "--no-abbrev", "-M", BASE, "HEAD"], stdout=f,
                        stdin=subprocess.DEVNULL).returncode
if rc:
    fail("git diff of the base %s and HEAD exited %d, so nothing is passed" % (BASE, rc))
with open(diff_file, "rb") as f:
    fields = f.read().split(b"\0")
if fields == [b""]:
    say(b"no file differs between the base %s and HEAD: nothing was compared" % BASE.encode())
    sys.exit(0)
Pair = collections.namedtuple("Pair", "base_path head_path base_id head_id base_mode head_mode")
pairs, deleted, added = [], [], []
i = 0
while i < len(fields) - 1:
    meta = fields[i].split(b" ")
    if len(meta) != 5 or not meta[0].startswith(b":") or not meta[4]:
        fail("git diff --raw gave a row that this step cannot read, so nothing is passed")
    base_mode, head_mode, base_id, head_id, status = meta[0][1:], meta[1], meta[2], meta[3], meta[4]
    letter = status[:1]
    if letter not in (b"M", b"T", b"R", b"D", b"A"):
        fail("git diff gave a row of status %s, and this step reads only M, T, R, D and A, so nothing is passed"
             % letter.decode("ascii", "replace"))
    n = 2 if letter == b"R" else 1
    paths = fields[i + 1:i + 1 + n]
    i += 1 + n
    # a head side that is no blob (a submodule) is a deletion
    on_base = letter != b"A" and base_mode != GITLINK
    on_head = letter != b"D" and head_mode != GITLINK
    if not on_base or unit_of(paths[0]) is None:
        # an added file, or the head of a row whose base side is no proof file (another path, or a
        # submodule): it can hold a deleted file's text, also with the base's own bytes (an exact rename).
        # A link's text is a path: it lacks the line, no keys.
        if on_head and head_mode in FILE_MODES:
            added.append((paths[-1], head_id, head_mode))
    elif not on_head:
        if base_mode in FILE_MODES:  # only a regular file carries the line
            deleted.append((paths[0], base_id))
    # equal ids: the same bytes, so no base blob is read, unless a regular file became a link
    elif base_id != head_id or (base_mode in FILE_MODES and head_mode not in FILE_MODES):
        pairs.append(Pair(paths[0], paths[-1], base_id, head_id, base_mode, head_mode))
    elif head_mode in FILE_MODES:
        # the same bytes under another path or mode (an exact rename, a mode change): the head is no pair of
        # its own, but it can hold a deleted file's text, as an added file can
        added.append((paths[-1], head_id, head_mode))

# The blobs.  The head blobs of the pairs, and the base blobs of the deleted files when there is an added file
# (or a head of a row whose base path is no proof file or whose bytes did not change) or a pair to pair them
# with, come in one fetch.  The deleted files are read first, so that the keys of a head that lacks the line
# are computed only when a deleted file carries the line.  Then the head blobs, and the base blobs only of the
# pairs whose head lacks the line.  A side that is no regular file is not read: a head lacks the line, and a
# base does not carry it.
heads = list(dict.fromkeys(p.head_id for p in pairs if p.head_mode in FILE_MODES))
dels = list(dict.fromkeys(o for _, o in deleted)) if deleted and (added or heads) else []
present(list(dict.fromkeys(heads + dels)))
key_of = {o: keys(data) for o, data in blobs(dels, "base") if carries(data)}  # deleted blob id: keys()
bare_ok = {}  # head blob id: declarable()
head_keys = {}  # head blob id: keys(), only when a deleted file carries the line
for o, data in blobs(heads, "head"):
    if not carries(data):
        bare_ok[o] = declarable(data)
        if key_of:
            head_keys[o] = keys(data)
todo = [p for p in pairs if p.head_mode not in FILE_MODES or p.head_id in bare_ok]
bases = list(dict.fromkeys(p.base_id for p in todo if p.base_mode in FILE_MODES))
present(bases)
carrying = {o for o, data in blobs(bases, "base") if carries(data)}
# head path: (base paths, head blob id, head mode)
strips = {p.head_path: ({p.base_path}, p.head_id, p.head_mode) for p in todo
          if p.base_mode in FILE_MODES and p.base_id in carrying}

# Deleted and added files.  A deleted file and an added or changed file with the same text, by either key.
# Each added file, each head of a row whose base path is no proof file or whose bytes did not change, and each
# head of a pair above, that lacks the line is paired with every deleted file that carries it and matches it:
# git's rename detection may have taken an added file as the rename of a twin, of a file that is no proof file
# or of a file of the same bytes, and a change can write the text over another file.
read_d, read_a = len(dels), 0
if key_of:
    by_a, by_b = {}, {}
    for path, o in deleted:
        for k, index in zip(key_of.get(o, ()), (by_a, by_b)):
            if k is not None:
                index.setdefault(k, []).append(path)

    def match(k):
        return {path for key, index in zip(k, (by_a, by_b)) if key is not None for path in index.get(key, [])}
    read_a = len(head_keys)
    for p in pairs:
        found = (match(head_keys[p.head_id]) if p.head_mode in FILE_MODES and p.head_id in head_keys
                 else None)
        if found:
            strips.setdefault(p.head_path, (set(), p.head_id, p.head_mode))[0].update(found)
    adds = list(dict.fromkeys(o for _, o, _ in added))
    present(adds)
    read_a += len(adds)
    matched = {}
    for o, data in blobs(adds, "head"):
        if not carries(data):
            found = match(keys(data))
            if found:
                matched[o] = found
                bare_ok[o] = declarable(data)
    for path, o, mode in added:
        if o in matched:
            strips[path] = (set(matched[o]), o, mode)

# The verdict of each strip: the unit of its base path decides, and the head's left-bare.tsv of the unit that
# the head path is in can declare it.
@functools.cache
def has_record(unit):
    tsv = unit + LICENCE_DIR + b"made-from.tsv"
    return any(git("ls-tree", "-z", rev, "--", tsv) for rev in (BASE, "HEAD"))


@functools.cache
def left_bare(unit):
    """{path under <unit>/proofs/: reason} of HEAD's left-bare.tsv, by the rules of made_from.py's
    left_bare(): bytes a line at a time, a line that is not UTF-8 declares nothing, blank lines and lines that
    start with # or path<TAB> are skipped, a path named on two rows declares nothing, and a row declares only
    with exactly two columns and a reason that is not blank.  declared() checks the rest of its rules."""
    rows = {}
    listed = git("ls-tree", "-z", "HEAD", "--", unit + LICENCE_DIR + b"left-bare.tsv")
    meta = listed.split(b"\t", 1)[0].split(b" ")
    if len(meta) == 3 and meta[0] in FILE_MODES and meta[1] == b"blob":
        present([meta[2]])
        [(_, data)] = list(blobs([meta[2]], "head"))
        seen = set()
        for line8 in data.split(b"\n"):
            try:
                line = line8.decode("utf-8")
            except UnicodeDecodeError:
                continue
            if not line.strip() or line.startswith(("#", "path\t")):
                continue
            cols = line.rstrip("\r").split("\t")
            path, reason = cols[0], (cols[1].strip() if len(cols) == 2 else "")
            if path in seen:
                rows.pop(path, None)
                continue
            seen.add(path)
            if reason:
                rows[path] = reason
    return rows


def declared(path, oid, mode):
    """The rest of the rules of made_from.py's left_bare(): the row names a .v file of the unit, and
    made_from.py's headerless() is true of it.  This step also asks for a regular file, not a link: a link's
    blob is a path, not the file's text."""
    unit = unit_of(path)
    if unit is None or mode not in FILE_MODES or not bare_ok.get(oid):
        return False
    try:
        rel = path[len(unit) + len(b"/proofs/"):].decode("utf-8")
    except UnicodeDecodeError:
        return False
    return rel in left_bare(unit)


failed, noticed, kept = [], [], 0
for head_path, (base_set, oid, mode) in strips.items():
    base_paths = sorted(base_set)
    if not any(has_record(unit_of(b)) for b in base_paths):
        noticed.append((head_path, base_paths))
    elif declared(head_path, oid, mode):
        kept += 1
    else:
        failed.append((head_path, base_paths))


def named(head_path, base_paths):
    name = escape(head_path)
    if base_paths != [head_path]:
        name += b" (at the base: " + b", ".join(map(escape, base_paths)) + b")"
    return name


# The output: counts only on a plain line, file names only in the data of ::notice:: and ::error:: lines.
say(b"strip check: compared %d pair(s) at one path or a rename and %d deleted with %d added or changed file(s), "
    b"read %d blob(s) of HEAD and %d of the base, fetched %d blob(s) in %d request(s), %.1f s"
    % (len(pairs), read_d, read_a, count["head"], count["base"], count["fetched"], count["requests"],
       time.monotonic() - started))
for head_path, base_paths in sorted(noticed):
    say(b"::notice::" + named(head_path, base_paths) + b" lost Anthropic's copyright line. Its unit at the base "
        b"has no licence record (proofs/provenance/evidence/licence/made-from.tsv), so the strip check does "
        b"not fail on it.")
if failed:
    lines = [b"%d proof file(s) lost Anthropic's copyright line (Copyright <year> Anthropic PBC, in the first %d "
             b"lines). The unit of each file at the base has a licence record "
             b"(proofs/provenance/evidence/licence/made-from.tsv):" % (len(failed), HEADER_LINES)]
    lines += [b"  " + named(h, b) for h, b in sorted(failed)]
    lines.append(b"If a file is our own, declare it in the left-bare.tsv of the unit that its path is in: "
                 b"<unit>/proofs/provenance/evidence/licence/left-bare.tsv. Write one row: the path relative "
                 b"to <unit>/proofs/, a tab, and the reason. A declared file has no licence lines in its first "
                 b"%d lines: no copyright line, no SPDX-License-Identifier line and no Modified by line. "
                 b"The made-from check of a unit (made_from.py --check) also reads that unit's "
                 b"left-bare.tsv, through dev/licence/made_from.py. If a file holds Anthropic's code, keep "
                 b"its licence lines." % HEADER_LINES)
    say(b"::error::" + b"%0A".join(lines))
    sys.exit(1)
if strips:
    say(b"no proof file of a unit with a licence record lost Anthropic's copyright line without a declaration: "
        b"%d declared in left-bare.tsv, %d in units with no licence record" % (kept, len(noticed)))
else:
    say(b"no proof file lost Anthropic's copyright line")
EOF
