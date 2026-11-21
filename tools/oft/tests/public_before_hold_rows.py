"""Each row of tools/publish/public-before-hold.tsv (disclosure.PUBLIC_BEFORE_HOLD) checked against what it says.

    cd tools && python3 -m unittest oft.tests.public_before_hold_rows

A unit row says that the first release of theorem-labs/oss-verify-proofs whose tree holds a fuzz target is the one it
names, and a statement row that the first release whose harness.yaml of the fuzz target lists the statement (in its
`statements`) is the one it names; and each says that its pull request is the hold of the fuzz target's project,
merged into main after that release was published.  check_row checks each part.  From GitHub's API (GitHub): the
release is published (no draft), its tree holds the regular file projects/<project>/<harness>/harness.yaml (for a
statement row, one whose `statements` lists the statement: the contents API gives the file's bytes with the answer, so
the same request serves both kinds of row), and no release published before it does.  A release is read at the commit
its tag names (its ref, through an annotated tag object, to a commit GitHub shows with its tree), so that GitHub's 404
of a path there means the path is not in that tree: a tag deleted or renamed answers 404 too ("No commit found for the
ref ..."), and would make an older release read as one that did not carry the fuzz target.  A file counts, for a row
of either kind, only when the contents API's answer is a file of that very path whose bytes hash to the git blob id it
gives, and the release's own tree (git/trees, walked from the commit's root tree down the path) holds that blob there
with the mode of a regular file, 100644 or 100755.  The contents API follows a symbolic link to the file it names and
answers `type: "file"` with the link's own path and blob id and the target's bytes, so the hash and the mode each
refuse it.  So a tag that resolves to no such commit, a 404 of any other message, an answer that is no such file (a
directory's listing, a symbolic link's or a submodule's entry, a followed link, a file of another path), a tree that
cannot be read whole, and a file that is no YAML mapping with a `statements` mapping are each Unchecked.  From this
clone's git (History): exactly one commit of HEAD's first-parent line names the pull request (its subject ends
`(#<n>)`, as GitHub's squash and queue merges write it, or begins `Merge pull request #<n> `); the project's
project.yaml says `release: private` at that commit and does not at its first parent; and the release was published
before that commit's committer time, when the merge reached main.  On a pull request's run HEAD is the merge commit
GitHub builds, which names no pull request: OFT_CHANGE_PULL_REQUEST names the pull request this run checks, and a row
whose hold is that pull request reads HEAD as its merge (its first parent is the base), so a hold's pull request can
add its own rows.  A merge queue group's commit, and main's after the merge, name their pull request.

It needs the network and main's history up to each hold.  A row whose part cannot be checked here fails, naming the
row and why: GitHub cannot be reached or refuses (60 requests an hour from one address without a token; GH_TOKEN or
GITHUB_TOKEN, when set, is sent), no commit names the pull request (not merged yet, or a clone whose history stops
short of the merge).  Nothing here skips.

`unittest discover` does not find this module (its name does not begin with `test`), so oft.tests.parallel, which
pr.yml's tests job runs, does not run it.  That job's checkout is one commit deep (actions/checkout's default, with no
fetch-depth) and it sets no token: it reaches api.github.com, but no hold's merge is in its history, so every row
would fail there.  pr.yml's public_rows job runs it, when a change touches the record: with this commit's whole
history and GH_TOKEN, the job's token.  The record is in tools/publish/, which no release keeps, so this module checks
rows only in the repository the releases are cut from.  The tests of check_row itself, which read neither the
network nor the history, are tools/oft/tests/test_disclosure.py's.
"""
import base64
import datetime
import hashlib
import json
import os
import re
import subprocess
import unittest
import urllib.error
import urllib.parse
import urllib.request

from oft import disclosure, yamlio

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))   # tools/oft/tests -> the repository
PUBLIC = "theorem-labs/oss-verify-proofs"
API = "https://api.github.com"
# a git object id as GitHub's API gives it
SHA = re.compile(r"[0-9a-f]{40}")
# the most annotated tag objects followed from a tag's ref to its commit: a release tag is one at most
TAG_DEPTH = 4


class Unchecked(Exception):
    """A part of a row that cannot be checked here, and why."""


def _when(text):
    """An ISO 8601 time (GitHub's `2026-10-22T21:11:04Z`, git's %cI) as an aware datetime."""
    return datetime.datetime.fromisoformat(text.replace("Z", "+00:00"))


class GitHub:
    """The public repository's releases and their trees, through GitHub's REST API.  opener stands for
    urllib.request.urlopen."""

    def __init__(self, repo=PUBLIC, token=None, opener=urllib.request.urlopen):
        self.repo, self.opener = repo, opener
        self.token = token if token is not None else os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
        self._published, self._commits, self._roots, self._trees, self._holds = None, {}, {}, {}, {}

    def _get(self, path):
        """(HTTP status, JSON document) of GET path: 200 and its document, or 404 and GitHub's {"message": ...} (None
        when it sent none), so that a caller can tell a path's "Not Found" from a ref's "No commit found for the ref";
        Unchecked when GitHub cannot be reached or answers anything else."""
        req = urllib.request.Request(API + path, headers={"Accept": "application/vnd.github+json",
                                                          "User-Agent": "oft-public-before-hold-rows"})
        if self.token:
            req.add_header("Authorization", "Bearer " + self.token)
        try:
            with self.opener(req, timeout=60) as r:
                return r.status, json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            if e.code == 404:
                try:
                    return 404, json.loads(e.read().decode("utf-8"))
                except (OSError, ValueError):
                    return 404, None
            limit = e.headers.get("x-ratelimit-remaining") if e.headers else None
            raise Unchecked("GitHub answered HTTP %d to GET %s%s" % (
                e.code, path, ", with no requests left this hour (set GH_TOKEN)" if limit == "0" else ""))
        except (urllib.error.URLError, OSError, ValueError) as e:
            raise Unchecked("GET %s%s failed: %s" % (API, path, e))

    def published(self):
        """{tag: when it was published} of every release of the repository that is no draft."""
        if self._published is None:
            out, page = {}, 1
            while True:
                status, data = self._get("/repos/%s/releases?per_page=100&page=%d" % (self.repo, page))
                if status != 200 or not isinstance(data, list):
                    raise Unchecked("GitHub lists no releases of %s (HTTP %d)" % (self.repo, status))
                out.update((r["tag_name"], _when(r["published_at"])) for r in data
                           if not r.get("draft") and r.get("published_at"))
                if len(data) < 100:
                    break
                page += 1
            self._published = out
        return self._published

    def commit(self, tag):
        """The commit release tag names: its ref refs/tags/<tag>, through annotated tag objects, to a commit GitHub
        shows with its tree.  Unchecked when there is no such ref (a tag deleted or renamed), it names no commit, or
        the commit cannot be read with its tree."""
        if tag not in self._commits:
            why = "the tag %s of %s" % (tag, self.repo)
            status, ref = self._get("/repos/%s/git/ref/tags/%s" % (self.repo, urllib.parse.quote(tag, safe="")))
            if status != 200 or not isinstance(ref, dict) or ref.get("ref") != "refs/tags/" + tag:
                raise Unchecked("%s cannot be resolved: GitHub has no ref refs/tags/%s (HTTP %d%s)" % (
                    why, tag, status, ", %s" % ref.get("message") if isinstance(ref, dict) and ref.get("message")
                    else ""))
            obj = ref.get("object")
            for _ in range(TAG_DEPTH):
                if not (isinstance(obj, dict) and obj.get("type") == "tag" and SHA.fullmatch(str(obj.get("sha")))):
                    break
                status, tagged = self._get("/repos/%s/git/tags/%s" % (self.repo, obj["sha"]))
                obj = tagged.get("object") if status == 200 and isinstance(tagged, dict) else None
            if not (isinstance(obj, dict) and obj.get("type") == "commit" and SHA.fullmatch(str(obj.get("sha")))):
                raise Unchecked("%s names no commit (it resolves to %s)" % (
                    why, "%s %s" % (obj.get("type"), obj.get("sha")) if isinstance(obj, dict) else "nothing"))
            status, commit = self._get("/repos/%s/git/commits/%s" % (self.repo, obj["sha"]))
            if status != 200 or not isinstance(commit, dict) or commit.get("sha") != obj["sha"]:
                raise Unchecked("%s names the commit %s, which GitHub does not show (HTTP %d)" % (
                    why, obj["sha"], status))
            tree = commit.get("tree")
            if not (isinstance(tree, dict) and SHA.fullmatch(str(tree.get("sha")))):
                raise Unchecked("%s names the commit %s, which GitHub shows with no tree" % (why, obj["sha"]))
            self._commits[tag], self._roots[tag] = obj["sha"], tree["sha"]
        return self._commits[tag]

    def _tree(self, sha, where):
        """{name: (mode, type, object id)} of the git tree sha, which where names (a path at a release), read once;
        Unchecked when GitHub does not show it whole, as the tree of that id, with entries of that shape."""
        if sha not in self._trees:
            status, data = self._get("/repos/%s/git/trees/%s" % (self.repo, sha))
            entries = data.get("tree") if status == 200 and isinstance(data, dict) else None
            if not isinstance(entries, list) or data.get("sha") != sha or data.get("truncated") is not False:
                raise Unchecked("the tree %s of %s (%s) cannot be read whole (HTTP %d%s)" % (
                    sha, where, self.repo, status, ", truncated" if isinstance(data, dict) and data.get("truncated")
                    else ""))
            out = {}
            for e in entries:
                if not (isinstance(e, dict) and isinstance(e.get("path"), str) and SHA.fullmatch(str(e.get("sha")))):
                    raise Unchecked("the tree %s of %s (%s) holds an entry of no known shape: %.80r" % (
                        sha, where, self.repo, e))
                out[e["path"]] = (e.get("mode"), e.get("type"), e["sha"])
            self._trees[sha] = out
        return self._trees[sha]

    def _mode(self, tag, path):
        """(mode, type, object id) of the entry path in the tree of the commit release tag names (commit), walked from
        its root tree; None when a part of the path is not there.  Unchecked when a part before the last is no tree, or
        a tree on the way cannot be read whole (_tree)."""
        self.commit(tag)
        sha, walked = self._roots[tag], ""
        parts = path.split("/")
        for i, name in enumerate(parts):
            entry = self._tree(sha, "%s at %s" % (walked or "the root", tag)).get(name)
            walked = "%s/%s" % (walked, name) if walked else name
            if entry is None or i == len(parts) - 1:
                return entry
            if entry[1] != "tree":
                raise Unchecked("%s at %s (%s) is no directory: the tree gives it mode %s, type %s" % (
                    walked, tag, self.repo, entry[0], entry[1]))
            sha = entry[2]

    def _entry(self, tag, unit):
        """The bytes of the regular file projects/<unit>/harness.yaml in the tree of the commit release tag names
        (commit), or None for GitHub's 404 "Not Found" of it at that commit (module docstring).  Unchecked for the tag
        that cannot be resolved and for any other answer: a 404 of another message; a directory's listing, an entry of
        another type (a symbolic link, a submodule) or a file of another path; a file with no base64 content (GitHub
        sends none over 1 MB) or whose bytes do not hash to its blob id (a followed symbolic link); and a file the
        release's tree does not hold as that blob with a regular file's mode.  One contents request for each, whatever
        rows read it, and the trees on the way read once for each release."""
        if (tag, unit) not in self._holds:
            sha, path = self.commit(tag), "projects/%s/harness.yaml" % unit
            where = "%s at %s (%s, commit %s)" % (path, tag, self.repo, sha[:12])
            status, data = self._get("/repos/%s/contents/%s?ref=%s" % (self.repo, urllib.parse.quote(path), sha))
            message = data.get("message") if isinstance(data, dict) else None
            if status == 404 and message == "Not Found":
                self._holds[(tag, unit)] = None
                return None
            if status == 404:
                raise Unchecked("GitHub answered 404 to %s with %r, not \"Not Found\", so whether that tree holds it "
                                "is not known" % (where, message))
            if not (isinstance(data, dict) and data.get("type") == "file" and data.get("path") == path):
                raise Unchecked("%s is no regular file: GitHub's answer is %s" % (
                    where, "a directory's listing" if isinstance(data, list) else
                    "the file %s" % data.get("path") if isinstance(data, dict) and data.get("type") == "file" else
                    "an entry of type %r" % data.get("type") if isinstance(data, dict) else "no JSON object"))
            try:
                if data.get("encoding") != "base64" or not isinstance(data.get("content"), str):
                    raise ValueError("GitHub sent no base64 content for it")
                content = base64.b64decode(data["content"], validate=False)
            except ValueError as e:   # binascii.Error is a ValueError
                raise Unchecked("%s cannot be read: %s" % (where, e))
            blob = hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()
            if blob != data.get("sha"):
                raise Unchecked("%s is no regular file: its content hashes to the blob %s, not to %s, the blob GitHub "
                                "names (a symbolic link GitHub followed answers so)" % (where, blob, data.get("sha")))
            entry = self._mode(tag, path)
            if entry is None or entry[1] != "blob" or entry[2] != blob:
                raise Unchecked("%s is no regular file: the release's tree holds %s there, not the blob %s" % (
                    where, "nothing" if entry is None else "%s %s (mode %s)" % (entry[1], entry[2], entry[0]), blob))
            if entry[0] not in ("100644", "100755"):
                raise Unchecked("%s is no regular file: the release's tree gives it mode %s" % (where, entry[0]))
            self._holds[(tag, unit)] = content
        return self._holds[(tag, unit)]

    def holds(self, tag, unit):
        """Whether the tree of release tag holds the regular file projects/<unit>/harness.yaml (_entry)."""
        return self._entry(tag, unit) is not None

    def lists(self, tag, unit, statement):
        """Whether the harness.yaml of unit in the tree of release tag (_entry) lists statement in its `statements`:
        False when that tree holds no such file; Unchecked when the file is no YAML mapping with a `statements`
        mapping."""
        content = self._entry(tag, unit)
        if content is None:
            return False
        where = "projects/%s/harness.yaml at %s (%s)" % (unit, tag, self.repo)
        try:
            doc = yamlio.load(content.decode("utf-8"), where=where)
        except (ValueError, yamlio.YamlError) as e:   # a UnicodeDecodeError is a ValueError
            raise Unchecked("%s cannot be read: %s" % (where, e))
        if not (isinstance(doc, dict) and isinstance(doc.get("statements"), dict)):
            raise Unchecked("%s is no mapping with a `statements` mapping" % where)
        return statement in doc["statements"]


class History:
    """HEAD's first-parent line of the git repository at root, this clone's main when HEAD is on it.  change is the
    number of the pull request whose run this is when HEAD is GitHub's merge commit for it (module docstring)."""

    def __init__(self, root=REPO, change=None):
        self.root, self.change = root, change

    def _git(self, *args, check=True):
        try:
            done = subprocess.run(["git", "-C", self.root, *args], capture_output=True, text=True)
        except OSError as e:
            raise Unchecked("git cannot run: %s" % e)
        if check and done.returncode:
            raise Unchecked("git %s: %s" % (" ".join(args), done.stderr.strip() or "exit %d" % done.returncode))
        return done

    def merge(self, number):
        """(commit, committer time) of the one commit of HEAD's first-parent line that names pull request number
        (module docstring); Unchecked when none does, or more than one."""
        lines = self._git("log", "--first-parent", "--format=%H%x00%cI%x00%s", "HEAD").stdout.splitlines()
        rows = [line.split("\0", 2) for line in lines]
        named = re.compile(r"(?:.*\(#%d\)|Merge pull request #%d .*)" % (number, number))
        hits = [(c, _when(t)) for c, t, s in rows if named.fullmatch(s)]
        if len(hits) == 1:
            return hits[0]
        if not hits and number == self.change:
            # this run's own pull request, merged at HEAD: its time is when GitHub built the merge
            head = self._git("log", "-1", "--format=%H%x00%cI", "HEAD").stdout.strip().split("\0")
            return head[0], _when(head[1])
        if hits:
            raise Unchecked("%d commits of HEAD's first-parent line name pull request #%d: %s"
                            % (len(hits), number, ", ".join(c[:12] for c, _ in hits)))
        # a shallow clone's boundary commit has no parents here, so the line ends at it when it reaches it
        grafts = self._git("rev-parse", "--git-path", "shallow").stdout.strip()
        try:
            with open(os.path.join(self.root, grafts), encoding="utf-8") as f:
                cut = rows and rows[-1][0] in f.read().split()
        except FileNotFoundError:
            cut = False
        except (OSError, ValueError) as e:
            raise Unchecked("this clone's list of shallow commits cannot be read: %s" % e)
        raise Unchecked("no commit of HEAD's first-parent line names pull request #%d: %s" % (number, (
            "this clone's history stops at %s, a shallow clone's boundary, so it may stop before the merge"
            % rows[-1][0][:12] if cut else "it is not merged into the main this clone holds")))

    def private(self, rev, project):
        """Whether projects/<project>/project.yaml at rev says `release: private`; None when rev holds no such file;
        Unchecked when the file is no YAML mapping."""
        spec = "%s:projects/%s/project.yaml" % (rev, project)
        if self._git("cat-file", "-e", spec, check=False).returncode:
            return None
        try:
            data = yamlio.load(self._git("cat-file", "-p", spec).stdout, where=spec)
        except yamlio.YamlError as e:
            raise Unchecked(str(e))
        if not isinstance(data, dict):
            raise Unchecked("%s is no mapping" % spec)
        return data.get("release") == "private"


def check_row(unit, release, number, public, history, statement=None):
    """[problem]: each part of the row (unit, release, the hold's pull request number; with statement, the statement
    row of that statement of unit) that is false, or that cannot be checked here and why, as `<row>: <why>` (module
    docstring); [] when the row holds.  public is a GitHub, history a History, or stand-ins with their methods."""
    project, problems, published = unit.split("/")[0], [], None
    name = unit if statement is None else "%s/%s" % (unit, statement)
    what = "holds no projects/%s/harness.yaml%s" % (
        unit, "" if statement is None else " whose `statements` lists %s" % statement)

    def carries(tag):
        return public.holds(tag, unit) if statement is None else public.lists(tag, unit, statement)
    try:
        published = public.published()
        if release not in published:
            problems.append("%s is no published release of %s" % (release, PUBLIC))
        else:
            if not carries(release):
                problems.append("the tree of %s %s" % (release, what))
            for tag in sorted((t for t in published if published[t] < published[release]), key=published.get):
                if carries(tag):
                    problems.append("%s, published before %s, holds it already: %s is not the first" % (
                        tag, release, release))
                    break
    except Unchecked as e:
        problems.append("the public release cannot be checked here: %s" % e)
    try:
        commit, merged = history.merge(number)
        if history.private(commit, project) is not True:
            problems.append("projects/%s/project.yaml does not say `release: private` at #%d's merge %s"
                            % (project, number, commit[:12]))
        before = history.private(commit + "^1", project)
        if before is not False:
            problems.append("#%d did not begin the hold: projects/%s/project.yaml before its merge %s is %s" % (
                number, project, commit[:12], "not there" if before is None else "`release: private` already"))
        if published and release in published and not published[release] < merged:
            problems.append("%s was published at %s, not before #%d's merge at %s" % (
                release, published[release].isoformat(), number, merged.isoformat()))
    except Unchecked as e:
        problems.append("the hold's merge cannot be checked here: %s" % e)
    return ["%s\t%s\t#%d: %s" % (name, release, number, p) for p in problems]


class Rows(unittest.TestCase):
    """The record of this checkout, row by row, against GitHub and this clone's main."""

    def test_the_record_is_read_whole(self):
        record = disclosure.public_before_hold(os.path.join(REPO, disclosure.PUBLIC_BEFORE_HOLD))
        self.assertTrue(record and record.units, "%s is not there, cannot be read, holds a line that is no row or a "
                        "row that does not fit the others, or has no unit row" % disclosure.PUBLIC_BEFORE_HOLD)

    def test_each_row_holds(self):
        record = disclosure.public_before_hold(os.path.join(REPO, disclosure.PUBLIC_BEFORE_HOLD))
        change = os.environ.get("OFT_CHANGE_PULL_REQUEST", "")
        public, history = GitHub(), History(change=int(change) if change.isdigit() else None)
        rows = [((p, h, None), row) for (p, h), row in (record.units if record else {}).items()]
        rows += [((p, h, st), row) for (p, h, st), row in (record.statements if record else {}).items()]
        for (project, harness, statement), (release, number) in sorted(rows, key=lambda r: (r[0][:2], r[0][2] or "")):
            unit = "%s/%s" % (project, harness)
            with self.subTest(row=unit if statement is None else "%s/%s" % (unit, statement)):
                self.assertEqual(check_row(unit, release, number, public, history, statement), [])


if __name__ == "__main__":
    unittest.main()
