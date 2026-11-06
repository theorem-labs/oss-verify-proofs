"""Shared pieces of the tests: a fresh copy of the fixture tree, rendered, the edits several modules make to it, the
forms a held finding's text takes, test git repositories, and the environment of a script a test runs."""
import contextlib
import glob
import html
import io
import os
import re
import shutil
import subprocess
import tempfile
import urllib.parse

from oft import facts, generate, layout, lint, rules, yamlio

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE = os.path.join(HERE, "fixtures", "tree")
FINDINGS = os.path.join(HERE, "fixtures", "findings")
RECORD = os.path.join(HERE, "fixtures", "record")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))   # tools/oft/tests -> the repository
KEY = "zlib/checksum_fuzzer/stand-in-abort"
FINDING = "findings/" + KEY      # the fixture finding add_findings lays down

# Git's automatic maintenance (gc --auto, maintenance run --auto) starts detached after a commit and can still be
# writing into a test repository's .git/objects while the test deletes that repository (seen in CI:
# "Directory not empty: .../tree/.git/objects").  Every git a test starts inherits this process's environment, and
# every test module imports this one, so it is turned off here, after any GIT_CONFIG_* pairs already set.
NO_BACKGROUND_GIT = (("maintenance.auto", "false"), ("gc.auto", "0"))


def add_git_config(env, *pairs):
    """Add (key, value) pairs of git configuration to env, after any GIT_CONFIG_* pairs it holds already."""
    n = int(env.get("GIT_CONFIG_COUNT") or 0)
    for key, value in pairs:
        env["GIT_CONFIG_KEY_%d" % n], env["GIT_CONFIG_VALUE_%d" % n] = key, value
        n += 1
    env["GIT_CONFIG_COUNT"] = str(n)


add_git_config(os.environ, *NO_BACKGROUND_GIT)

# The variables of this process's environment that a test hands on to a script it runs, by name: where the commands
# are, the locale, where temporary files go and the time zone.  Nothing else: a child started from os.environ gets the
# home, the agent settings, the credentials and the review session of whoever runs the tests (XDG_CONFIG_HOME, the
# agent's configuration directory, ANTHROPIC_*, REVIEW_SESSION and the rest), so it reads, and can write, that person's
# files, and passes or fails by what is in them.
CHILD_VARIABLES = ("PATH", "LANG", "LANGUAGE", "LC_ALL", "LC_COLLATE", "LC_CTYPE", "LC_MESSAGES", "LC_NUMERIC",
                   "LC_TIME", "TMPDIR", "TZ")
# A home that is not there, for a child that reads none.
NO_HOME = "/nonexistent/oft-test-home"


def child_environment(home, **variables):
    """The environment of a script a test runs: CHILD_VARIABLES of this process's environment, HOME at home (a
    directory the test owns, or NO_HOME), the review agent's managed settings in a folder under <home> (the folder
    facts-review-served reads in place of the machine's managed settings), git's background maintenance off, as for
    every git a test starts, and `variables` over these."""
    env = {name: os.environ[name] for name in CHILD_VARIABLES if name in os.environ}
    env.update(HOME=home, REVIEW_MANAGED_SETTINGS=os.path.join(home, "etc-claude-code"))
    add_git_config(env, *NO_BACKGROUND_GIT)
    env.update(variables)
    return env


class Tree:
    """A rendered copy of the fixture in a temporary directory."""

    def __init__(self, render=True):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-test-")
        self.root = os.path.join(self._tmp.name, "tree")
        shutil.copytree(FIXTURE, self.root)
        if render:
            assert self.generate() == 0, "the fixture does not render"

    def close(self):
        self._tmp.cleanup()

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()

    def path(self, *p):
        return os.path.join(self.root, *p)

    def write(self, rel, text, mode="w"):
        p = self.path(rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, mode) as f:
            f.write(text)

    def read(self, rel):
        with open(self.path(rel), encoding="utf-8") as f:
            return f.read()

    def files(self):
        """The repository-relative path of every file under the tree, sorted; _build/ and .git/ left out."""
        found = []
        for dp, dns, fns in os.walk(self.root):
            dns[:] = [d for d in dns if d not in ("_build", ".git")]
            rel_dir = os.path.relpath(dp, self.root).replace(os.sep, "/")
            found += [f if rel_dir == "." else "%s/%s" % (rel_dir, f) for f in fns]
        return sorted(found)

    def yaml(self, rel):
        return yamlio.load_file(self.path(rel))

    def put_yaml(self, rel, data):
        self.write(rel, yamlio.dump(data))

    def generate(self, check=False):
        buf = io.StringIO()
        rc = generate.run(self.root, check=check, out=buf)
        self.last_output = buf.getvalue()
        return rc

    def lint(self, **kw):
        """lint.run over this tree; with release=True, the public repositories it reads are those of Public unless
        the caller gives its own, so no test reads the network."""
        if kw.get("release"):
            kw.setdefault("public", Public())
        return lint.run(self.root, **kw)


# what the fixture's toolchain/checker.Dockerfile pins as the model's files (LPS_TREE_SHA256)
FIXTURE_LPS_TREE = "7a" * 32


class Public:
    """Stands in for the public repositories `oft lint --release` reads (model.Public): every commit is on the
    branches and tags of refs, the model's cut hashes to cut at any commit, and model.yaml requires the hash required
    of the cut line."""

    def __init__(self, refs=("heads/main",), cut=FIXTURE_LPS_TREE, required=FIXTURE_LPS_TREE,
                 line="toolchain/lps-core.paths"):
        self.refs, self.cut, self.required, self.line = list(refs), cut, required, line
        self.read = []   # (method, url, commit, pathspecs or None) of every read, in order

    def containing(self, url, commit):
        self.read.append(("containing", url, commit, None))
        return list(self.refs)

    def cut_sha256(self, url, commit, pathspecs):
        self.read.append(("cut_sha256", url, commit, tuple(pathspecs) if pathspecs else None))
        return self.cut

    def required_tree(self, url, commit):
        self.read.append(("required_tree", url, commit, None))
        return self.required, self.line

    def close(self):
        pass


def rules_of(findings):
    return sorted({f.rule for f in findings})


def recipe_file(n):
    """The file name of recipe number n.  The fixtures build every numbered recipe's file name with this at run time:
    the tests ship in the public cut, whose disclosure search refuses a kept file that names a held project's own
    recipe, so no shipped file may name a recipe file that a real private project could pin (test_release_tree's
    test_no_shipped_file_names_a_recipe_file_a_private_project_could_pin).  release.yaml's first recipe,
    recipe.tar.zst, is the one name written out: no private project may take it while release.yaml lists it."""
    return "recipe-%d.tar.zst" % n


# the fixture's one recipe (release.yaml recipes), and the recipe of a later release
FIXTURE_RECIPE = {"release": "v2026.11.0", "file": "recipe.tar.zst", "bytes": 2000000, "sha256": "5d" * 32}
NEXT_RECIPE = {"release": "v2026.12.0-src", "file": recipe_file(2), "bytes": 3000000, "sha256": "6e" * 32}
# two recipes of their own that `release: private` projects pin (draft assets that release.yaml does not list), in a
# tag no other fact names
OWN_RECIPE = {"release": "v2026.11.7-src", "file": recipe_file(90), "bytes": 4000000, "sha256": "7a" * 32}
OTHER_OWN_RECIPE = {"release": "v2026.11.7-src", "file": recipe_file(91), "bytes": 4100000, "sha256": "7c" * 32}


def build_record(recipe=FIXTURE_RECIPE, proofs=None):
    """The text of a build record (PROVENANCE.yaml) that cites `recipe` and, with proofs, says where the proofs came
    from (proofs.origin and proofs.written_here): the only parts of it oft reads."""
    doc = {"schema": "oss-verify-proofs build record v1", "recipe": {"asset": dict(recipe)}}
    if proofs is not None:
        doc["proofs"] = dict(proofs)
    return yamlio.dump(doc)


def own_recipe(t, project, recipe, record=None):
    """Make project `release: private`, its binary archive built with `recipe`, a recipe of its own; with record, the
    path of a build record of the project, write that record citing it."""
    rel = "projects/%s/project.yaml" % project
    p = t.yaml(rel)
    p["release"] = "private"
    p["assets"]["bin"]["recipe"] = dict(recipe)
    t.put_yaml(rel, p)
    if record is not None:
        t.write(record, build_record(recipe))


def _next_release(t):
    r = t.yaml("release.yaml")
    r["release"] = "2026.12.0"
    r["recipes"].append(dict(NEXT_RECIPE))
    t.put_yaml("release.yaml", r)


def _rebuilt(t, project, src=False):
    """Give a project a binary archive in v2026.12.0 built with NEXT_RECIPE, and with src new source assets in
    v2026.12.0-src."""
    p = t.yaml("projects/%s/project.yaml" % project)
    p["assets"]["bin"] = dict(p["assets"]["bin"], release="v2026.12.0", sha256="9c" * 32, recipe=dict(NEXT_RECIPE))
    if src:
        p["assets"]["src"] = {"release": "v2026.12.0-src", "file": project + "-src.tar.zst", "bytes": 5000,
                              "sha256": "7f" * 32}
        p["assets"]["src_manifest"] = {"release": "v2026.12.0-src", "file": project + "-src.MANIFEST.tsv",
                                       "bytes": 300, "sha256": "8a" * 32}
    t.put_yaml("projects/%s/project.yaml" % project, p)


def later_release(t):
    """The fixture one release on, without copying: json is rebuilt with v2026.12.0-src's recipe and gains source
    assets there, while zlib's archive, source assets and recipe stay in v2026.11.0; each harness with a build record
    cites its project's archive recipe."""
    _next_release(t)
    _rebuilt(t, "json", src=True)
    t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", build_record())
    t.write("proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml", build_record(NEXT_RECIPE))
    assert t.generate() == 0, t.last_output


def recipe_only_rebuild(t, record=True):
    """The fixture one release on, after zlib is rebuilt with a new recipe and no new source: its archive (and its
    build record, with record) cites the recipe of v2026.12.0-src, and its source asset and MANIFEST stay in
    v2026.11.0."""
    _next_release(t)
    _rebuilt(t, "zlib")
    if record:
        t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", build_record(NEXT_RECIPE))
    assert t.generate() == 0, t.last_output


def older_shape(t):
    """The fixture in the shape before recipes, as a published tree still has it: release.yaml's one `recipe`, and
    no recipe on any binary archive."""
    r = t.yaml("release.yaml")
    r["recipe"] = r.pop("recipes")[0]
    t.put_yaml("release.yaml", r)
    for name in ("zlib", "json"):
        p = t.yaml("projects/%s/project.yaml" % name)
        del p["assets"]["bin"]["recipe"]
        t.put_yaml("projects/%s/project.yaml" % name, p)


# The names a renamed release gives its theories and its opam packages (OSSV-162)
NEW_NAMESPACE, NEW_OPAM_STEM = "OSSVerify", "oss-verify"


def rename_namespace(t, namespace=NEW_NAMESPACE, opam_stem=NEW_OPAM_STEM):
    """The fixture's facts under other names, as `oft rename-namespace` leaves them before it renders: release.yaml
    names them (`namespace`, `opam_stem`), each harness.yaml states its theory in the new namespace, and the opam files
    of the old stem are gone."""
    release = t.yaml("release.yaml")
    old, old_stem = release.get("namespace", "OssFuzzTheorems"), release.get("opam_stem", "oss-fuzz-theorems")
    edit(t, "release.yaml", lambda r: r.update(namespace=namespace, opam_stem=opam_stem))
    for rel in sorted(glob.glob(t.path("projects", "*", "*", "harness.yaml"))):
        edit(t, os.path.relpath(rel, t.root), lambda y: y.update(rocq=namespace + y["rocq"][len(old):]))
    for path in glob.glob(t.path("projects", "*", "rocq-%s-*.opam" % old_stem)) if opam_stem != old_stem else ():
        os.remove(path)


def add_findings(t):
    """Lay fixtures/findings over a fixture copy as its findings/: one patched finding of zlib/checksum_fuzzer,
    findings/zlib/checksum_fuzzer/stand-in-abort, whose input makes both ASan builds abort, so it shows asan_agrees and
    asan_ubsan_agrees false, and the unpatched binaries it runs on."""
    shutil.copytree(FINDINGS, t.path("findings"))


def recount(t):
    """Write release.yaml's counts and oss_fuzz.projects as t now has them (rules.counts)."""
    loaded = facts.load(t.root)
    r = t.yaml("release.yaml")
    r["counts"] = rules.counts(loaded)
    r["oss_fuzz"]["projects"] = loaded.oss_fuzz_project_count()
    t.put_yaml("release.yaml", r)


@contextlib.contextmanager
def tree(render=True):
    t = Tree(render)
    try:
        yield t
    finally:
        t.close()


def edit(t, rel, change):
    """Apply change to the YAML at rel in t."""
    y = t.yaml(rel)
    change(y)
    t.put_yaml(rel, y)


def errors(t, record=False):
    """Every tree error: the loader's and the rules'."""
    loaded = facts.load(t.root, record=record)
    rules.check(loaded)
    return loaded.errors


def entry_patch(t, project, entry_id, name, text, summary="A stand-in patch for these tests.", upstream="not-a-defect",
                url=None):
    """Give project a patches entry, the last of its entries, named entry_id, whose file <name> in the project's
    patches folder (patches/<project>/, or projects/<project>/patches/ in a tree in the per-project layout) holds
    text."""
    rel = "%s/%s" % (layout.patches_dir(project, layout.of_tree(t.root)), name)
    t.write(rel, text, "wb")
    entry = {"id": entry_id, "summary": summary, "file": name, "upstream": upstream}
    if url is not None:
        entry["url"] = url
    edit(t, "projects/%s/project.yaml" % project, lambda y: y.setdefault("patches", []).append(entry))


def public_patch(t):
    """Make the fixture finding public, reported at a stand-in URL, and give zlib the patches entry that ships its
    patch, as a release does."""
    finding = t.yaml(FINDING + "/finding.yaml")
    finding.update(state="public", upstream="https://bugs.example.org/stand-in-abort")
    t.put_yaml(FINDING + "/finding.yaml", finding)
    with open(t.path(FINDING, finding["patch"]), "rb") as f:
        entry_patch(t, "zlib", "stand-in-abort", finding["patch"], f.read(), summary=finding["summary"],
                    upstream="reported", url=finding["upstream"])


def port_built(t, project):
    """Say in project's project.yaml that the OSS Verify port built it, with the source assets (its own, when it has
    them) and the port archive a port build attaches."""
    def change(y):
        y["build"]["oss_verify"] = {"repository": "theorem-labs/oss-verify", "commit": "d" * 40,
                                    "path": "projects/" + project}
        assets = y["assets"]
        assets["bin"].pop("recipe", None)   # the port built the archive, and no recipe did
        assets.setdefault("src", {"release": "v2026.11.0", "file": project + "-src.tar.zst", "bytes": 1000,
                                  "sha256": "3" * 64})
        assets.setdefault("src_manifest", {"release": "v2026.11.0", "file": project + "-src.MANIFEST.tsv",
                                           "bytes": 1000, "sha256": "4" * 64})
        assets["port"] = {"release": "v2026.11.0", "file": project + "-port.tar.zst", "bytes": 1000,
                          "sha256": "9" * 64}
    edit(t, "projects/%s/project.yaml" % project, change)


def alias_patch(t, text, project="json"):
    """Give project a patches entry, the last of its entries, under an id no finding has, whose file holds text: a
    release that ships a patch under another name."""
    entry_patch(t, project, "alias", "alias.patch", text, summary="A patch with an unrelated public identifier.")


# who commits in a test repository, set in the repository's own configuration so that the tools' own git commands, in
# it and in every worktree of it, commit the same way; no commit is signed
TEST_GIT_CONFIG = (("user.name", "oft-tests"), ("user.email", "oft-tests" + "@" + "example.invalid"),
                   ("commit.gpgsign", "false"))


def git(root, *args, input=None):
    """`git -C root ARGS` with no global or system configuration; its output, stripped.  A failure fails the test."""
    r = subprocess.run(["git", "-C", root, *args], input=input, capture_output=True, text=True,
                       env=dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1"))
    if r.returncode != 0:
        raise AssertionError("git %s: %s" % (" ".join(args), r.stderr))
    return r.stdout.strip()


def git_commit(root, message="x"):
    """Commit every change under root; the new commit."""
    git(root, "add", "-A")
    git(root, "commit", "-q", "--allow-empty", "-m", message)
    return git(root, "rev-parse", "HEAD")


def git_repo(root):
    """Make root a git repository on branch main with its files in one commit (TEST_GIT_CONFIG in its configuration);
    that commit."""
    git(root, "init", "-q", "-b", "main")
    for key, value in TEST_GIT_CONFIG:
        git(root, "config", key, value)
    return git_commit(root, "the first commit")

# A holding finding's fix, shaped like the patches of a real one: a `git format-patch` file with its envelope, C code
# with `->`, `&`, `<`, `"` and `'`, and no `index` line (as `git diff` writes some).  It is a stand-in: it describes no
# bug in zlib.
HELD_PATCH = "\n".join([
    "From 3f1c0a9d8e7b6a5c4d3e2f1a0b9c8d7e6f5a4b3c Mon Sep 17 00:00:00 2001",
    "From: A Tester",
    "Date: Sun, 25 Oct 2026 12:00:00 +0000",
    "Subject: [PATCH 1/2] crc32: read the byte the loop stops at, not the one past it",
    "",
    "A stand-in commit message for these tests; it describes no bug in zlib.",
    "---",
    " crc32.c | 4 ++--",
    " 1 file changed, 2 insertions(+), 2 deletions(-)",
    "",
    "diff --git a/crc32.c b/crc32.c",
    "--- a/crc32.c",
    "+++ b/crc32.c",
    "@@ -101,7 +101,7 @@ local z_crc_t crc32_little(z_crc_t crc, const unsigned char *buf, z_size_t len)",
    "     register z_crc_t c;",
    "     register const z_crc_t *buf4;",
    " ",
    "-    while (len && ((ptrdiff_t)buf & 3) && buf[1] != '\\0')"
    " { /* read the byte after this crc32 input buffer ends */",
    "+    while (len && ((ptrdiff_t)buf & 3) && *buf != '\\0') { /* read the byte this crc32 input buffer ends at */",
    "         c = crc_table[0][(c ^ *buf++) & 0xff] ^ (c >> 8);",
    "         len--;",
    "     }",
    "@@ -140,6 +140,6 @@ local z_crc_t crc32_little(z_crc_t crc, const unsigned char *buf, z_size_t len)",
    " ",
    "     buf4 = (const z_crc_t *)(const void *)buf;",
    "-    if (state->next -> avail < 4 && \"stand-in\" != 0) /* reject only the unavailable stand-in checksum bytes */",
    "+    if (state->next -> avail <= 4 && \"stand-in\" != 0) /* reject each unavailable stand-in checksum byte */",
    "         return 0;",
    "     while (len >= 32) {",
    "         DOLIT32;",
    "-- ",
    "2.43.0",
    ""])
# the payload of a holding finding's input, after the driver's 6-byte header, with `<`, `&` and quotes.  A stand-in: it
# is no input of any finding
HELD_PAYLOAD = ("Q := $(join stand-in,in-stand) <&>\n"
                "all: ; @echo 'stand-in payload preserves the unpublished driver bytes before this release'"
                " && exit \"0\"\n")


def _diff(patch):
    """patch from its `diff --git` line on, without the envelope and the signature: as `git diff` prints it."""
    body = patch[patch.index("diff --git"):]
    return body[:body.index("-- \n")]


def patch_copies(patch):
    """{how: bytes}: the forms a copy of patch takes as people and tools write it.  Each holds every hunk of patch."""
    diff = _diff(patch)
    stamped = diff.replace("--- a/crc32.c\n", "--- a/crc32.c\t2026-10-25 12:00:00.000000000 +0000\n").replace(
        "+++ b/crc32.c\n", "+++ b/crc32.c\t2026-10-26 09:30:00.000000000 +0000\n")
    prefixed = diff.replace("a/crc32.c", "a/zlib-1.3.1/crc32.c").replace("b/crc32.c", "b/zlib-1.3.1/crc32.c")
    return {
        "exact": patch.encode(),
        "another envelope": patch.replace("3f1c0a9d", "0badc0de").replace("Sun, 25 Oct", "Mon, 26 Oct").replace(
            "[PATCH 1/2]", "[PATCH]").replace("2.43.0", "2.39.5").encode(),
        "no envelope (git diff)": diff.encode(),
        "git show": ("commit 0badc0de0badc0de0badc0de0badc0de0badc0de\nAuthor: A Tester\n"
                     "Date:   Sun Oct 25 12:00:00 2026 +0000\n\n    crc32: a stand-in\n\n" + diff).encode(),
        "an index line": diff.replace("--- a/", "index 0123456..89abcde 100644\n--- a/", 1).encode(),
        "header timestamps": stamped.encode(),
        "another path prefix": prefixed.encode(),
        "header case": diff.replace("crc32.c", "CRC32.c").encode(),
        "only the hunks": diff[diff.index("@@"):].encode(),
        "tabs for spaces": diff.replace("        ", "\t").encode(),
        "CR CR LF": diff.replace("\n", "\r\r\n").encode(),
        "HTML <pre>": ("<pre>%s</pre>\n" % html.escape(patch)).encode(),
        "HTML, only > escaped": patch.replace(">", "&gt;").encode(),
        "HTML escaped twice": html.escape(html.escape(diff)).encode(),
        "percent escapes": ("https://bugs.example.org/new?details=%s\n" % urllib.parse.quote(diff)).encode(),
        "UTF-16-LE": diff.encode("utf-16-le"),
        "UTF-32-LE": stamped.encode("utf-32-le"),
        "UTF-32-BE": prefixed.encode("utf-32-be"),
        "UTF-32 with a byte order mark": diff.encode("utf-32"),
        "a Markdown code block": ("The fix:\n\n" + "".join("    " + line for line in stamped.splitlines(True))
                                  ).encode(),
        "a YAML block scalar": ("fix:\n  text: |\n" + "".join("      " + line for line in prefixed.splitlines(True))
                                ).encode(),
    }


def folded(text, width, indent=""):
    """text broken at spaces into lines of at most width characters, each after indent."""
    lines, line = [], ""
    for word in text.split(" "):
        if line and len(line) + 1 + len(word) > width:
            lines.append(line)
            line = word
        else:
            line = word if not line else line + " " + word
    return "".join("%s%s\n" % (indent, w) for w in lines + [line])


def add_build_record(t, unit="zlib/checksum_fuzzer"):
    """Give a fuzz target the complete build record of fixtures/record (its PROVENANCE.yaml and the licence texts
    it names), with the binaries, the archives and the recipe the tree's facts pin for it.  The record goes in the
    fuzz target's proofs folder, in the layout its facts are in (layout.py)."""
    p, h = unit.split("/")
    rel = layout.record_path(p, h, facts.load(t.root).unit_layout(unit))
    shutil.copytree(RECORD, t.path(os.path.dirname(rel)), dirs_exist_ok=True)
    r = t.yaml(rel)
    builds = t.yaml("projects/%s/harness.yaml" % unit)["builds"]
    r["entry_point"].update(project=p, harness=h)
    r["binaries"] = [{"build": b, "file": v["file"], "bytes": v["bytes"], "sha256": v["sha256"]}
                     for b, v in builds.items() if not v.get("withheld")]
    assets = t.yaml("projects/%s/project.yaml" % p).get("assets") or {}
    # each archive by file, bytes and SHA-256, and no release: project.yaml names it (Contract C1)
    r["binary_asset"] = {k: assets["bin"][k] for k in ("file", "bytes", "sha256")}
    r["source_asset"] = {k: {f: assets[k][f] for f in ("file", "bytes", "sha256")}
                         for k in ("src", "src_manifest") if k in assets}
    if "recipe" in assets["bin"]:
        r["recipe"]["asset"] = dict(assets["bin"]["recipe"])
    t.put_yaml(rel, r)
    return rel


# GitHub's expressions, for every test here that reads a workflow key's value: the subset the workflows use
# ('...' strings with '' for a quote, numbers, null, true, false, context paths, format(), the status functions a
# caller passes in, parentheses, !, ==, !=, && and ||).  `a && b` gives b when a is true and a otherwise, `a || b`
# gives a when a is true and b otherwise, and a comparison of two unlike types casts both to a number (null and ''
# are 0, any other string is NaN, so null equals no action name); strings compare without regard to case, and an
# object or an array equals only itself.  One reading of these rules for the whole package, so a correction to them
# lands once.  https://docs.github.com/en/actions/reference/workflows-and-actions/expressions
_TOKEN = re.compile(r"\s*(\|\||&&|==|!=|!|\(|\)|,|'(?:[^']|'')*'|[A-Za-z_][A-Za-z0-9_.-]*|-?\d+(?:\.\d+)?)")
_WORDS = {"null": None, "true": True, "false": False}


def _tokens(text):
    out, at = [], 0
    while at < len(text):
        m = _TOKEN.match(text, at)
        if m is None:
            if not text[at:].strip():
                break
            raise ValueError("cannot read %r from %r" % (text[at:], text))
        out.append(m.group(1))
        at = m.end()
    return out


def gh_truthy(value):
    return not (value is None or value is False or value == "" or value == 0)


def _number(value):
    if value is None or value is False:
        return 0.0
    if value is True:
        return 1.0
    if isinstance(value, (int, float)):
        return float(value)
    try:
        return float(value.strip() or 0)
    except ValueError:
        return float("nan")


def _equal(a, b):
    if isinstance(a, str) and isinstance(b, str):
        return a.lower() == b.lower()
    if a is None and b is None:
        return True
    if isinstance(a, bool) and isinstance(b, bool):
        return a is b
    if isinstance(a, (dict, list)) or isinstance(b, (dict, list)):
        return a is b                      # an object or an array equals only itself, so one is never null
    return _number(a) == _number(b)        # NaN == NaN is false here as it is for GitHub


def gh_text(value):
    """The value as GitHub writes it into a key's text."""
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, float) and value.is_integer():
        return str(int(value))
    return str(value)


def _format(args):
    out, fmt, at = "", gh_text(args[0]), 0
    while at < len(fmt):
        m = re.compile(r"\{\{|\}\}|\{(\d+)\}").match(fmt, at)
        if m is None:
            out, at = out + fmt[at], at + 1
            continue
        out += fmt[at] if m.group(1) is None else gh_text(args[int(m.group(1)) + 1])
        at = m.end()
    return out


class _Expression:
    """One ${{ }} expression over a scope of contexts ({"github": …, "needs": …}); a name the scope does not hold
    is null, as GitHub's is.  `functions` gives the value of each function the expression calls, beside format()."""

    def __init__(self, text, scope, functions):
        self.tokens, self.scope, self.functions, self.at = _tokens(text), scope, functions, 0

    def value(self):
        got = self._or()
        if self.at != len(self.tokens):
            raise ValueError("left over: %s" % " ".join(self.tokens[self.at:]))
        return got

    def _take(self, token):
        if self.at < len(self.tokens) and self.tokens[self.at] == token:
            self.at += 1
            return True
        return False

    def _or(self):
        got = self._and()
        while self._take("||"):
            other = self._and()
            got = got if gh_truthy(got) else other
        return got

    def _and(self):
        got = self._comparison()
        while self._take("&&"):
            other = self._comparison()
            got = other if gh_truthy(got) else got
        return got

    def _comparison(self):
        got = self._unary()
        while self.at < len(self.tokens) and self.tokens[self.at] in ("==", "!="):
            op, self.at = self.tokens[self.at], self.at + 1
            other = self._unary()
            got = _equal(got, other) if op == "==" else not _equal(got, other)
        return got

    def _unary(self):
        if self._take("!"):
            return not gh_truthy(self._unary())
        return self._primary()

    def _primary(self):
        token, self.at = self.tokens[self.at], self.at + 1
        if token == "(":
            got = self._or()
            if not self._take(")"):
                raise ValueError("no ) in %s" % " ".join(self.tokens))
            return got
        if token.startswith("'"):
            return token[1:-1].replace("''", "'")
        if token in _WORDS:
            return _WORDS[token]
        if re.fullmatch(r"-?\d+(?:\.\d+)?", token):
            return float(token)
        if self._take("("):
            args = []
            if not self._take(")"):
                args.append(self._or())
                while self._take(","):
                    args.append(self._or())
                if not self._take(")"):
                    raise ValueError("no ) after %s(" % token)
            if token == "format":
                return _format(args)
            if token not in self.functions:
                raise ValueError("no stand-in for %s()" % token)
            return self.functions[token](*args)
        got = self.scope
        for part in token.split("."):
            got = got.get(part) if isinstance(got, dict) else None
        return got


def gh_value(text, scope, functions=None):
    """The value of a workflow key over a scope of contexts: the expression's own value when the key is one ${{ }}
    and nothing else (so a key that reads as a boolean stays one), else the key's text with each expression's value
    written into it, which is what a concurrency group's name is.  A key that holds no expression, a YAML boolean
    among them, is its own value."""
    if isinstance(text, bool) or text is None:
        return text
    text = " ".join(str(text).split())
    functions = functions or {}
    whole = re.fullmatch(r"\$\{\{(.*)\}\}", text, re.S)
    if whole:
        return _Expression(whole.group(1), scope, functions).value()
    return re.sub(r"\$\{\{(.*?)\}\}",
                  lambda m: gh_text(_Expression(m.group(1), scope, functions).value()), text)


class Concurrency:
    """GitHub's rule over the runs of one workflow, from its own concurrency block: at most one run of a group is in
    progress and at most one waits; a run queued while another of its group is in progress is `pending` and cancels
    the one that was waiting; a run whose cancel-in-progress is true cancels the run in progress of its group and
    starts instead of waiting.  A group's name is read without regard to case.
    https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#concurrency"""

    def __init__(self, workflow):
        self.block = workflow["concurrency"]
        self.running, self.pending, self.cancelled = {}, {}, []

    def group(self, scope):
        return gh_value(self.block["group"], scope).lower()

    def cancels(self, scope):
        return gh_truthy(gh_value(self.block["cancel-in-progress"], scope))

    def start(self, name, scope):
        """The event of `scope` starts the run `name`: it runs, or waits, or is cancelled at once."""
        group = self.group(scope)
        if group in self.pending:
            self.cancelled.append(self.pending.pop(group))
        if group in self.running and not self.cancels(scope):
            self.pending[group] = name
            return
        if group in self.running:
            self.cancelled.append(self.running.pop(group))
        self.running[group] = name

    def finish(self, name):
        """The run `name` ends; the run that waits in its group, if there is one, starts."""
        group = next(g for g, run in self.running.items() if run == name)
        del self.running[group]
        if group in self.pending:
            self.running[group] = self.pending.pop(group)

    def state(self, name):
        if name in self.cancelled:
            return "cancelled"
        if name in self.running.values():
            return "running"
        return "pending" if name in self.pending.values() else "ended"
