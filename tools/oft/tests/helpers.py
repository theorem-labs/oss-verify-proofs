"""Shared pieces of the tests: a fresh copy of the fixture tree, rendered, and the forms a held finding's text takes."""
import contextlib
import html
import io
import os
import shutil
import tempfile
import urllib.parse

from oft import facts, generate, lint, rules, yamlio

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE = os.path.join(HERE, "fixtures", "tree")
FINDINGS = os.path.join(HERE, "fixtures", "findings")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))   # tools/oft/tests -> the repository

# Git's automatic maintenance (gc --auto, maintenance run --auto) starts detached after a commit and can still be
# writing into a test repository's .git/objects while the test deletes that repository (CI run 40332897507:
# "Directory not empty: .../tree/.git/objects").  Every git a test starts inherits this process's environment, and
# every test module imports this one, so it is turned off here, after any GIT_CONFIG_* pairs already set.
NO_BACKGROUND_GIT = (("maintenance.auto", "false"), ("gc.auto", "0"))


def _no_background_git(env):
    n = int(env.get("GIT_CONFIG_COUNT") or 0)
    for key, value in NO_BACKGROUND_GIT:
        env["GIT_CONFIG_KEY_%d" % n], env["GIT_CONFIG_VALUE_%d" % n] = key, value
        n += 1
    env["GIT_CONFIG_COUNT"] = str(n)


_no_background_git(os.environ)


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
        return lint.run(self.root, **kw)


def rules_of(findings):
    return sorted({f.rule for f in findings})


# the fixture's one recipe (release.yaml recipes), and the recipe of a later release
FIXTURE_RECIPE = {"release": "v2026.11.0", "file": "recipe.tar.zst", "bytes": 2000000, "sha256": "5d" * 32}
NEXT_RECIPE = {"release": "v2026.12.0-src", "file": "recipe-2.tar.zst", "bytes": 3000000, "sha256": "6e" * 32}


def build_record(recipe=FIXTURE_RECIPE, proofs=None):
    """The text of a build record (PROVENANCE.yaml) that cites `recipe` and, with proofs, says where the proofs came
    from (proofs.origin and proofs.written_here): the only parts of it oft reads."""
    doc = {"schema": "oss-verify-proofs build record v1", "recipe": {"asset": dict(recipe)}}
    if proofs is not None:
        doc["proofs"] = dict(proofs)
    return yamlio.dump(doc)


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
