"""The process model the checker image is built from, and the public repositories a release pins commits of: what
`oft lint --release` reads with git (rules `model` and `pins`).

model.yaml says which hash over the model's files the checker image must pin for a model commit (required_tree), and
cut_sha256 computes that hash as toolchain/checker.Dockerfile does.  fetch_history fetches a public repository's
branches and tags anonymously; Public does it once per repository, into a scratch directory.
"""
import hashlib
import io
import os
import re
import subprocess
import tarfile
import tempfile

from . import yamlio

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "model.yaml")
PACKAGE = "package/"
COMMIT = re.compile(r"[0-9a-f]{40}")
# how long one git command may take: a fetch of a public repository takes seconds
TIMEOUT = 600


class ModelError(Exception):
    """A git read that failed, or a commit or a file name these functions cannot judge."""


def load():
    """model.yaml: `lines`, each a cut, a commit, its git tree and the sha256 its cut must hash to, and `other`, the
    cut and sha256 of a commit on no line."""
    return yamlio.load_file(DATA)


def _git(git_dir, *args, data=False):
    try:
        r = subprocess.run(["git", "-C", git_dir] + list(args), capture_output=True, timeout=TIMEOUT,
                           env=dict(os.environ, GIT_TERMINAL_PROMPT="0"))
    except subprocess.TimeoutExpired:
        raise ModelError("git %s: no answer in %d s" % (args[0], TIMEOUT)) from None
    if r.returncode:
        raise ModelError("git %s: %s" % (args[0], r.stderr.decode("utf-8", "replace").strip()))
    return r.stdout if data else r.stdout.decode()


def _commit(commit):
    if not isinstance(commit, str) or not COMMIT.fullmatch(commit):
        raise ModelError("%r is not a full commit id" % (commit,))
    return commit


def fetch_history(url, git_dir):
    """Every branch and tag of the repository at url, with all they hold, under refs/pub/heads/ and refs/pub/tags/ of
    git_dir, a bare repository made here (in an empty or missing directory) when it is not one.  A whole fetch, not a
    partial one: a partial repository fetches a missing object from its remote when asked for it, and a public
    repository is small."""
    os.makedirs(git_dir, exist_ok=True)
    _git(git_dir, "init", "-q", "--bare")
    _git(git_dir, "fetch", "-q", "--no-tags", "--prune", url, "+refs/heads/*:refs/pub/heads/*",
         "+refs/tags/*:refs/pub/tags/*")


def containing(git_dir, commit):
    """The branches and tags fetch_history fetched that hold commit, as heads/<name> and tags/<name>: [] when none
    does, or the repository does not have the commit."""
    try:
        _git(git_dir, "cat-file", "-e", _commit(commit) + "^{commit}")
    except ModelError:
        return []
    return _git(git_dir, "for-each-ref", "--contains", commit, "--format=%(refname:lstrip=2)", "refs/pub/").split()


def required_tree(git_dir, commit, data=None):
    """(sha256, cut) that model.yaml (or data) requires of the model's files at commit: those of the first line whose
    commit, or a commit with whose git tree, is commit or one of its ancestors, else those of `other`.  git_dir holds
    the commit and its ancestors (fetch_history); their commits are all it reads."""
    data = data or load()
    seen = set(_git(git_dir, "rev-list", "--format=%T", _commit(commit)).split())
    for line in data["lines"]:
        if line["commit"] in seen or line["tree"] in seen:
            return line["sha256"], line["cut"]
    return data["other"]["sha256"], data["other"]["cut"]


def cut_sha256(git_dir, commit, pathspecs=None):
    """The hash toolchain/checker.Dockerfile pins over the model's cut at commit: the regular files `git archive`
    gives for pathspecs (toolchain/lps-core.paths), or without them those of package/, named from inside package/;
    `sha256sum` of each in C order of its name, then the sha256 of those lines.  A name sha256sum would escape (a
    backslash or a line break in it) is refused."""
    spec = list(pathspecs) if pathspecs else [PACKAGE.rstrip("/")]
    data = _git(git_dir, "archive", "--format=tar", _commit(commit), "--", *spec, data=True)
    files = []
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:", encoding="utf-8", errors="surrogateescape") as tar:
        for m in tar:
            name = m.name
            if not m.isreg() or (not pathspecs and not name.startswith(PACKAGE)):
                continue
            name = name if pathspecs else name[len(PACKAGE):]
            if any(c in name for c in "\\\n\r"):
                raise ModelError("%r: a file name sha256sum escapes" % name)
            files.append((name.encode("utf-8", "surrogateescape"), hashlib.sha256(tar.extractfile(m).read())))
    return hashlib.sha256(b"".join(b"%s  %s\n" % (h.hexdigest().encode(), n) for n, h in sorted(files))).hexdigest()


class Public:
    """The public repositories `oft lint --release` reads, each fetched once, anonymously, into a scratch directory
    that close() removes.  A fetch that fails fails every read of its repository."""

    def __init__(self):
        self._tmp = None
        self._dirs = {}   # url -> its git directory, or the ModelError its fetch raised

    def _repository(self, url):
        if url not in self._dirs:
            if self._tmp is None:
                self._tmp = tempfile.TemporaryDirectory(prefix="oft-public-")
            d = os.path.join(self._tmp.name, str(len(self._dirs)))
            try:
                fetch_history(url, d)
                self._dirs[url] = d
            except ModelError as e:
                self._dirs[url] = ModelError("%s: %s" % (url, e))
        if isinstance(self._dirs[url], ModelError):
            raise self._dirs[url]
        return self._dirs[url]

    def containing(self, url, commit):
        return containing(self._repository(url), commit)

    def cut_sha256(self, url, commit, pathspecs):
        return cut_sha256(self._repository(url), commit, pathspecs)

    def required_tree(self, url, commit):
        return required_tree(self._repository(url), commit)

    def close(self):
        if self._tmp is not None:
            self._tmp.cleanup()
            self._tmp = None
