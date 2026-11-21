"""The deviation record of a fuzz target (harness.yaml `deviation`, docs/facts.md), read again from what made its
binaries: the TLS library each build links, from a scan of the build's unstripped twin, and the rest from the build
record the fuzz target has, its release recipe or the copy of its OSS Verify port.

The scan of a build is projects/<project>/<harness>/proofs/provenance/evidence/deviation/<build>.tls.tsv:

    # oss-fuzz-theorems/tls-scan/1 sha256=<the stripped binary's sha256, builds.<build>.sha256> unstripped=<the twin's>
    <library> TAB <count> TAB <up to five of the names, sorted, joined by ",", or - when there is none>

with one row for each library of LIBRARIES, in that order.  The stripped binary has no symbol table (it is linked with
--strip-all), so the scan is of its unstripped twin, and its header binds it to the binary harness.yaml pins.

from_recipe reads only what it knows how to read, and refuses the rest, naming the file and the line: it never guesses.
Of a port function (a function a port's build.sh defines outside its blocks) it reads only where the flags of a compile
come from and skips the rest (_Port). tools/enroll/facts.py's deviation_record holds what it reads to the compiles whose
objects each build's link took (RESULT/links.<build>.json, by the objects' bytes), among them the compile of one entry
source of the harness (Reading.entries: a library block may compile those of several fuzz targets).

Not the checker (keys.NOT_THE_CHECKER): `oft lint` and the enrolment writer (tools/enroll/facts.py) run it, and
rules.check does not import it, so `oft check` never opens it."""
import collections
import fnmatch
import os
import posixpath
import re
import shlex

from . import elf, facts, layout, schema, yamlio

# The projects whose facts the enrolment writer gives `deviation` and the default statement `instance`.  The projects
# that must carry both are shapes.REQUIRED, in the checker, since oft check reads them and never opens this module.
WRITTEN = ("curl",)

# The names of each TLS library cURL can link, by prefix (R2(a)).  Each prefix is the library's own, read from the
# names it defines (2026-11-11):
#   OpenSSL 3 (libssl.so.3 and libcrypto.so.3, `nm -D --defined-only`): of libssl's 609 names 558 are SSL_, 7
#     OPENSSL_ and 5 OSSL_; of libcrypto's 5868, 910 are EVP_, 695 OSSL_, 101 OPENSSL_ and 100 CRYPTO_ (CRYPTO_malloc
#     and CRYPTO_free, which both libraries allocate through).
#   GnuTLS 3.8 (libgnutls.so.30): 1294 of its 1382 names are gnutls_; the others are _gnutls_ and nettle names.
#   mbedTLS 3.6.2 (library/*.c compiled): of its 1258 global names 1109 are mbedtls_ and 149 psa_ (cURL's md5.c and
#     sha256.c hash with psa_hash_* when they use mbedTLS).
#   wolfSSL 5.7.4 (src/*.c and wolfcrypt/src/*.c compiled with OPENSSL_EXTRA and OPENSSL_ALL): of its 2900 global
#     names 1776 are wolfSSL_ and 491 wc_ (wolfCrypt, which cURL's md4.c, md5.c, sha256.c and curl_ntlm_core.c call).
#     wolfSSL also defines four SSL_ names: SSL_ResourceFree, SSL_CtxResourceFree, SSL_COMP_get_compression_methods
#     and SSL_CTX_set_tmp_dh_callback.  A wolfSSL build that holds one of them has names of openssl and of wolfssl,
#     and backend refuses it, naming both: change this rule before a wolfSSL build is enrolled.
# No other prefix matches a name of another of these libraries.  None matches a name of cURL's own: Curl_* and curl_*
# begin with other letters, libcurl exports curl_* names only, and of these prefixes the cURL tree at f190aa8e defines
# only static functions: wc_statemach and wc_data_dtor (lib/ftp.c, in every build with FTP), and gnutls_*, mbedtls_*
# and SSL_ERROR_to_str in lib/vtls/, each built only with its own library.  So only global and weak names count: a
# static function is a local symbol (elf.BINDINGS), and every entry point cURL calls in a TLS library is global.
PREFIXES = (
    ("openssl", ("SSL_", "OPENSSL_", "EVP_", "CRYPTO_", "OSSL_")),
    ("gnutls", ("gnutls_",)),
    ("mbedtls", ("mbedtls_", "psa_")),
    ("wolfssl", ("wolfSSL_", "wc_")),
)
LIBRARIES = tuple(library for library, _prefixes in PREFIXES)
COUNTED = ("global", "weak")
KEPT = 5
HEADER = "# oss-fuzz-theorems/tls-scan/1 sha256=%s unstripped=%s"
_HEADER = re.compile(r"# oss-fuzz-theorems/tls-scan/1 sha256=([0-9a-f]{64}) unstripped=([0-9a-f]{64})")
_SHA = re.compile(r"[0-9a-f]{64}")
_NAME = re.compile(r"[^\s,]+")
CAP = 64 << 10
# One build's scan: the sha256 of its stripped binary and of the unstripped twin scanned, and for each library of
# LIBRARIES (count, names): how many names of it the twin defines, and the first KEPT of them, sorted.
Scan = collections.namedtuple("Scan", "sha256 unstripped counts")

# The flavour of each build in the release recipe's build body (recipe/tools/build-env.tsv names the flavours; the
# same map is tools/enroll/toolchain_info.py's FLAV).
FLAVOUR = {"plain": "plain", "ubsan": "ubsan", "asan": "asan", "asan-ubsan": "asanubsan"}
# The SANITIZER each build of an OSS Verify port is compiled with: tools/enroll/toolchain_info.py's SANITIZER, written
# out again here because no module of tools/oft imports tools/enroll (keys.NOT_THE_CHECKER); test_deviation pins the
# two.  The port's toolchain (oss-verify's infra/base-builder/toolchain.sh) sets SAN from it.
PORT_SANITIZER = {"plain": "none", "ubsan": "undefined", "asan": "address", "asan-ubsan": "address-undefined"}
# deviation.sanitizer's spelling of each SANITIZER value: the toolchain writes the pair address-undefined.
SPELLING = {"none": "none", "address": "address", "undefined": "undefined", "address-undefined": "address+undefined"}

# What one build of a block reads (from_recipe): the functions of the recipe's tools/ossfuzz/recipes.sh a build_lib
# may call, the commands it may run itself, and the variables a block may set.
KNOWN_CALLS = ("oft_require_target_cxx", "oft_build_cmake", "oft_build_harness", "oft_seal_getenv", "oft_seal_mkstemp",
               "oft_seal_getpid")
COMPILERS = ("$CC", "${CC}", "$CXX", "${CXX}")
ARCHIVERS = ("$CHOST-ar", "${CHOST}-ar", "$AR", "${AR}")
KNOWN_VARIABLES = ("URL", "COMMIT", "BUILD_IMAGE", "LIB_ARCHIVE", "LIB_CFLAGS", "OFT_HARNESS_CFLAGS", "CFLAGS",
                   "CXXFLAGS")
FLAG_VARIABLES = ("CFLAGS", "CXXFLAGS", "OFT_HARNESS_CFLAGS", "LIB_CFLAGS")
RECIPES = "/work/tools/ossfuzz/recipes.sh"
SOURCE_SUFFIXES = (".c", ".cc", ".cpp", ".cxx", ".C", ".c++")
# CMake's spellings of true and false (the -D values a recipe gives); any other value is refused
CMAKE_TRUE = ("ON", "YES", "TRUE", "Y", "1")
CMAKE_FALSE = ("OFF", "NO", "FALSE", "N", "0")
_ASSIGNMENT = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)=(.*)", re.DOTALL)
_CMAKE_D = re.compile(r"-D([A-Za-z_][A-Za-z0-9_]*)(?::[A-Za-z]+)?=(.*)", re.DOTALL)
_COMMIT = re.compile(r"[0-9a-f]{40}")
_FLAV_IF = re.compile(r"(if|elif) \[ \"\$FLAV\" = ([A-Za-z0-9_]+) \]; then")
_SAN = re.compile(r"(?<![A-Za-z0-9_])SAN=")
_HEREDOC = re.compile(r"<<-?\s*['\"]?([A-Za-z_][A-Za-z0-9_]*)['\"]?")

# What from_recipe reads: values, the record's fields (sanitizer a map from build name); sources, where each comes
# from, a file and line of the tree, by field path (sanitizer.<build> for each build); target, the target whose block
# built the fuzz target (a port's ov_target_begin, a release recipe's recipe.target); library, a port's library block
# whose build that block takes ($LIBROOT/<library>), or None; entries, a port's: each Entry, the entry sources of the
# harness whose origin harness_origin is, or None (a release recipe's).
Reading = collections.namedtuple("Reading", "values sources target library entries", defaults=(None, None, None))
# An entry source of a port's harness (Reading.entries): its path, /work/<the path _entry gives>, the file that
# oft_build_harness compiles and that the patch rows of the port's sources apply to; the target whose block compiles
# it (the Reading's target, or its library block's); and the file and line of that oft_build_harness.
Entry = collections.namedtuple("Entry", "path target source")


# ---------------------------------------------------------------- the TLS scan

def tls_scan(unstripped, stripped_sha256):
    """The Scan of the unstripped twin at path unstripped, of the stripped binary whose sha256 is stripped_sha256:
    the global and weak functions and data objects of its .symtab (elf.Elf.symbols) of each library of PREFIXES."""
    if not _SHA.fullmatch(stripped_sha256 or ""):
        raise ValueError("%r is not a sha256" % (stripped_sha256,))
    twin = elf.Elf(unstripped)
    found = {library: set() for library in LIBRARIES}
    for s in twin.symbols():
        if s.binding in COUNTED:
            for library, prefixes in PREFIXES:
                if s.name.startswith(prefixes):
                    found[library].add(s.name)
    return Scan(stripped_sha256, twin.sha256,
                {library: (len(names), tuple(sorted(names)[:KEPT])) for library, names in found.items()})


def render_scan(scan):
    """The text of the scan file of scan."""
    rows = [HEADER % (scan.sha256, scan.unstripped)]
    rows += ["%s\t%d\t%s" % (library, scan.counts[library][0], ",".join(scan.counts[library][1]) or "-")
             for library in LIBRARIES]
    text = "\n".join(rows) + "\n"
    parse_scan(text)
    return text


def write_scan(path, scan):
    """Write the scan file of scan at path."""
    text = render_scan(scan)
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def parse_scan(text):
    """The Scan of the text of a scan file; ValueError, naming the line, for one it cannot read."""
    if not text.endswith("\n"):
        raise ValueError("it does not end with a newline")
    lines = text[:-1].split("\n")
    m = _HEADER.fullmatch(lines[0])
    if not m:
        raise ValueError("line 1: not %r" % (HEADER % ("<sha256>", "<sha256>")))
    if len(lines) - 1 != len(LIBRARIES):
        raise ValueError("%d rows, but a scan has one for each of %s" % (len(lines) - 1, ", ".join(LIBRARIES)))
    counts = {}
    for no, (line, library) in enumerate(zip(lines[1:], LIBRARIES), 2):
        fields = line.split("\t")
        if len(fields) != 3 or fields[0] != library or not fields[1].isdigit() or fields[1] != str(int(fields[1])):
            raise ValueError("line %d: not %s TAB <count> TAB <names>" % (no, library))
        count = int(fields[1])
        names = () if fields[2] == "-" else tuple(fields[2].split(","))
        if (len(names) != min(count, KEPT) or not all(_NAME.fullmatch(n) for n in names)
                or list(names) != sorted(set(names))):
            raise ValueError("line %d: the names are not the first %d of %d names, sorted, joined by , (- for none)"
                             % (no, min(count, KEPT), count))
        counts[library] = (count, names)
    return Scan(m.group(1), m.group(2), counts)


def load_scan(path):
    """The Scan of the scan file at path, read as lint reads a file (facts.read_bounded): never through a symbolic
    link, and only a regular file of at most CAP bytes."""
    return parse_scan(facts.read_bounded(path, CAP).decode("utf-8"))


def scan_path(tree, harness):
    """{build: the path of its scan file} for each build of harness.yaml."""
    p, h = harness.project.name, harness.name
    where = layout.provenance_dir(p, h, tree.unit_layout("%s/%s" % (p, h)))
    return {b: "%s/evidence/deviation/%s.tls.tsv" % (where, b) for b in harness.data.get("builds") or {}}


def load_scans(tree, harness):
    """{build: its Scan, or the text of why its scan file cannot be read} of each build of harness.yaml whose scan
    file is there (a symbolic link counts, which load_scan refuses)."""
    out = {}
    for b, rel in scan_path(tree, harness).items():
        if not os.path.lexists(tree.path(rel)):
            continue
        try:
            out[b] = load_scan(tree.path(rel))
        except (ValueError, facts.BoundedFileError) as e:
            out[b] = "%s: %s" % (rel, e)
    return out


def _held(scans, library):
    return "; ".join("%s: %s" % (b, ", ".join(s.counts[library][1])) for b, s in sorted(scans.items())
                     if s.counts[library][0])


def backend(scans):
    """deviation.tls_backend of {build: Scan}: none when no scan holds a name of a TLS library, the library when
    exactly one library's names are held; ValueError, naming each library and its names, when two or more are."""
    held = [library for library in LIBRARIES if any(s.counts[library][0] for s in scans.values())]
    if not held:
        return "none"
    if len(held) == 1:
        return held[0]
    raise ValueError("the scans hold names of %s, and a binary links one TLS library at most"
                     % " and of ".join("%s (%s)" % (library, _held(scans, library)) for library in held))


# ---------------------------------------------------------------- the recipe

def _text(path_of, rel):
    try:
        return facts.read_bounded(path_of(rel), facts.file_cap(rel)).decode("utf-8")
    except facts.BoundedFileError as e:
        raise ValueError("%s: cannot be read: %s" % (rel, e)) from None
    except UnicodeDecodeError:
        raise ValueError("%s: not UTF-8 text" % rel) from None


def _yaml(path_of, rel):
    data = yamlio.load(_text(path_of, rel), rel)
    if not isinstance(data, dict):
        raise ValueError("%s: not a mapping" % rel)
    return data


def _logical(text, first=1, last=None):
    """[(line, text)] of the logical lines of lines first..last of text (1-based), a line that ends in a backslash
    joined to the next."""
    lines = text.split("\n")
    last = len(lines) if last is None else last
    out, held, start = [], "", None
    for no in range(first, last + 1):
        line = lines[no - 1]
        if start is None:
            start = no
        if line.endswith("\\"):
            held += line[:-1]
            continue
        out.append((start, held + line))
        held, start = "", None
    if start is not None:
        out.append((start, held))
    return out


def _words(rel, no, line):
    """The simple commands of one logical line, each a list of words, split at ; and &&; ValueError for anything
    else the shell would read as an operator (a pipe, a redirection, a subshell, a here-document)."""
    lexer = shlex.shlex(line, posix=True, punctuation_chars=";&|()<>")
    lexer.whitespace_split = True
    lexer.commenters = "#"
    try:
        tokens = list(lexer)
    except ValueError as e:
        raise ValueError("%s:%d: %s" % (rel, no, e)) from None
    if len(tokens) == 3 and tokens[1] == "()" and tokens[2] == "{":
        return [["%s()" % tokens[0], "{"]]
    commands, now = [], []
    for t in tokens:
        if t in (";", "&&"):
            commands.append(now)
            now = []
        elif t and set(t) <= set(";&|()<>"):
            raise ValueError("%s:%d: %r, a shell operator this reader does not read" % (rel, no, t))
        else:
            if "$(" in t or "`" in t:
                raise ValueError("%s:%d: %r runs a command this reader does not read" % (rel, no, t))
            now.append(t)
    commands.append(now)
    return [c for c in commands if c]


def _ref(word, name):
    return word in ("$%s" % name, "${%s}" % name, "${%s:-}" % name)


def _bare(value):
    """The variable a value is, when it is `$name` or `${name}` alone, else None."""
    m = re.fullmatch(r"\$(?:([A-Za-z_][A-Za-z0-9_]*)|\{([A-Za-z_][A-Za-z0-9_]*)\})", value)
    return m and (m.group(1) or m.group(2))


class _Flags:
    """What one block's build compiles with, read in the order the build runs its commands (_Block.read, and
    _Port.run for a port function): each flag variable of FLAG_VARIABLES as [(word, its line)], the macros its
    compiles define, the last -DENABLE_DEBUG= of oft_build_cmake, each oft_build_harness, each $LIBROOT/<target> the
    build names, and the variables its commands set.  The compiles are oft_build_cmake's (CFLAGS; recipes.sh's
    oft_cmake_toolchain gives CMake CFLAGS for both languages, oft_cxxflags), oft_build_harness's (CFLAGS and
    OFT_HARNESS_CFLAGS), each $CC or $CXX the build runs, and the driver's (LIB_CFLAGS, build-body.sh), each with the
    flags in force when it runs.  In a port's block (others: the targets of build.sh's other blocks), a path into the
    tree of another block that is not $LIBROOT/<target> is refused (refer)."""

    def __init__(self, rel, first, others=None):
        self.rel, self.first = rel, first         # first: the block's first line; a port function is defined before it
        self.others = others
        self.env = {name: [] for name in FLAG_VARIABLES}
        self.defined = {}                         # macro: the line of the flag that defines it
        self.debug, self.debug_at = None, None
        self.harnesses = []                       # [(line, the source as written, its _Scope, or None in a block)]
        self.cmake_at = []                        # the line of each oft_build_cmake
        self.refs = []                            # [(line, target, or None for one it cannot name)] of each $LIBROOT
        self.assigned = set()                     # each variable a command sets (an assignment, export, read...)
        self.loops = {}                           # variable: [(function, first line, last line)] of its for loops
        self.writes = collections.Counter()       # variable: how many commands set it, a for loop counted once

    def set(self, name):
        self.assigned.add(name)
        self.writes[name] += 1

    def assign(self, no, word, saved=None):
        """An assignment NAME=value (its word, quotes taken out): CFLAGS="$CFLAGS ..." adds to a flag variable, any
        other value replaces it.  CFLAGS set without $CFLAGS is refused, but for a value a port function saved itself
        and restores (saved, _Port.command's: pf_cflags=$CFLAGS, then CFLAGS=$pf_cflags)."""
        name, value = _ASSIGNMENT.fullmatch(word).groups()
        self.set(name)
        if name not in FLAG_VARIABLES:
            return
        parts = value.split()
        restore = (saved or {}).get(_bare(value))
        if parts and _ref(parts[0], name):
            self.env[name] = self.env[name] + [(w, no) for w in parts[1:]]
        elif restore and restore[0] == name and self.writes[_bare(value)] == restore[2]:
            self.env[name] = list(restore[1])
        elif name == "CFLAGS":
            raise ValueError("%s:%d: sets CFLAGS without $CFLAGS, which drops the flavour's sanitizer flags; "
                             "this reader cannot tell what the build compiles with" % (self.rel, no))
        else:
            self.env[name] = [(w, no) for w in parts]

    def expand(self, no, words):
        out = []
        for w in words:
            name = next((n for n in FLAG_VARIABLES if _ref(w, n)), None)
            out += self.env[name] if name else [(w, no)]
        return out

    def compile_(self, flags):
        now = {}
        i = 0
        while i < len(flags):
            w, no = flags[i]
            if w in ("-D", "-U") and i + 1 < len(flags):
                i += 1
                w = w + flags[i][0]
            if w.startswith(("-D", "-U")):
                macro = w[2:].split("=", 1)[0]
                if "$" in macro:
                    raise ValueError("%s:%d: %s, a macro this reader cannot name" % (self.rel, no, w))
                if w.startswith("-D"):
                    now.setdefault(macro, no)
                else:
                    now.pop(macro, None)
            i += 1
        for macro, no in now.items():
            self.defined.setdefault(macro, no)

    def cmake(self, no, args, where=()):
        """oft_build_cmake with args: its -DENABLE_DEBUG= (refused inside a construct, where, that the reader cannot
        follow: the last one wins), and its compiles."""
        i = 0
        while i < len(args):
            w = args[i]
            if w == "-D" and i + 1 < len(args):     # cmake takes -D NAME=VALUE as two words too
                i += 1
                w += args[i]
            i += 1
            m = _CMAKE_D.fullmatch(w)
            if m and m.group(1) == "ENABLE_DEBUG":
                value = m.group(2).upper()
                if value not in CMAKE_TRUE + CMAKE_FALSE:
                    raise ValueError("%s:%d: -DENABLE_DEBUG=%s, a value this reader does not know"
                                     % (self.rel, no, m.group(2)))
                if where:
                    raise ValueError("%s:%d: -DENABLE_DEBUG= inside %s (line %d), which this reader cannot follow"
                                     % ((self.rel, no) + tuple(where[0])))
                self.debug, self.debug_at = value in CMAKE_TRUE, no
            elif m and m.group(1) in ("CMAKE_C_FLAGS", "CMAKE_CXX_FLAGS"):
                raise ValueError("%s:%d: -D%s=, which the toolchain file's %s (CACHE FORCE, recipes.sh "
                                 "oft_cmake_toolchain) replaces: this reader cannot tell what CMake compiles "
                                 "with" % (self.rel, no, m.group(1), m.group(1)))
        self.cmake_at.append(no)
        self.compile_(list(self.env["CFLAGS"]))

    def harness(self, no, word, rest, scope=None):
        self.harnesses.append((no, word, scope))
        self.compile_(self.env["CFLAGS"] + self.env["OFT_HARNESS_CFLAGS"] + [(w, no) for w in rest])

    def refer(self, no, word):
        """Each $LIBROOT/<target> of the word (line no), which names the build of the block of that target; in a port's
        block, ValueError for any other path the word names into another block's tree: a `..` (as in $BUILDDIR/.. or
        ../<target>), which leaves the block's own directory, or a name of another block's target between its slashes
        (/work/build/lib/<flavour>/<target>, /work/targets/<target>, <target>/lib)."""
        text = _unquote(word)
        for m in _LIBROOT.finditer(text):
            self.refs.append((no, m.group(1)))
        if self.others is None:
            return
        rest = _LIBROOT.sub("", text)
        if _CLIMB.search(rest):
            raise ValueError("%s:%d: %s names .., a path out of the block's directory: this reader reads another "
                             "block's build only as $LIBROOT/<target>" % (self.rel, no, text))
        other = next((s for s in _SEGMENTS.split(rest) if s in self.others), None)
        if other is not None:
            raise ValueError("%s:%d: %s names the directory of %s, another block's target (ov_target_begin %s): this "
                             "reader reads another block's build only as $LIBROOT/<target>"
                             % (self.rel, no, text, other, other))

    def result(self, where):
        """(enable_debug, its source, unittests, its source): the last -DENABLE_DEBUG= of oft_build_cmake, or
        DEBUGBUILD defined in a compile; UNITTESTS defined in a compile.  where: the source of a value nothing gives."""
        if self.debug:
            enable_debug, debug_source = True, "%s:%d" % (self.rel, self.debug_at)
        elif "DEBUGBUILD" in self.defined:
            enable_debug, debug_source = True, "%s:%d" % (self.rel, self.defined["DEBUGBUILD"])
        else:
            enable_debug, debug_source = False, "%s:%d" % (self.rel, self.debug_at) if self.debug_at else where
        if "UNITTESTS" in self.defined:
            unittests, unit_source = True, "%s:%d" % (self.rel, self.defined["UNITTESTS"])
        else:
            unittests, unit_source = False, where
        return enable_debug, debug_source, unittests, unit_source


# What _Block.read gives: _Flags.result's four values, the _Flags, and the lines of what it read (the last build_lib,
# or a library block's own lines)
_Built = collections.namedtuple("_Built", "enable_debug debug_source unittests unit_source flags first last")


class _Block:
    """The commands of one target's block of a build record (lines first..last of rel), read as the build runs
    them: the block's own assignments, then the last build_lib it defines.  A port's library block (library: a block
    with no ov_target_build, port_blocks) runs no build_lib: its own commands, in order, are its build, which the blocks
    of other targets take.  A port's build_lib, and a library block, may call a port function, one that the port's
    build.sh (port, its _Port) defines outside every block before this block: _Port.run reads it.  Each word of a
    port's block (target, the target it begins), its own assignments too, is read for $LIBROOT/<target> and for a
    path into the tree of another block (_Flags.refer)."""

    def __init__(self, rel, text, first, last, sources_line=False, port=None, library=False, target=None):
        self.rel, self.first, self.last, self.port, self.library = rel, first, last, port, library
        self.target = target
        self.top = []            # [(line, words)] outside every function
        self.functions = []      # [(first line, last line, [(line, words)])] of each build_lib
        body = None
        for no, line in _logical(text, first, last):
            if _HEREDOC.search(line):
                raise ValueError("%s:%d: a here-document, which this reader does not read" % (rel, no))
            for words in _words(rel, no, line):
                if words[-1] == "{" and words[0].endswith("()"):
                    if words[0] != "build_lib()":
                        raise ValueError("%s:%d: defines %s, a function this reader does not know"
                                         % (rel, no, words[0][:-2]))
                    if body is not None:
                        raise ValueError("%s:%d: a function inside build_lib" % (rel, no))
                    body = (no, [])
                elif words == ["}"]:
                    if body is None:
                        raise ValueError("%s:%d: a } outside build_lib" % (rel, no))
                    self.functions.append((body[0], no, body[1]))
                    body = None
                elif body is not None:
                    self._check(no, words, inside=True)
                    body[1].append((no, words))
                else:
                    self._check(no, words, inside=library, sources_line=sources_line)
                    self.top.append((no, words))
        if body is not None:
            raise ValueError("%s:%d: build_lib is not closed" % (rel, body[0]))
        if not self.functions and not library:
            raise ValueError("%s:%d-%d: no build_lib" % (rel, first, last))

    def _check(self, no, words, inside, sources_line=False):
        if all(_ASSIGNMENT.fullmatch(w) for w in words):
            for w in words:
                name = _ASSIGNMENT.fullmatch(w).group(1)
                if name not in KNOWN_VARIABLES:
                    raise ValueError("%s:%d: sets %s, a variable this reader does not know" % (self.rel, no, name))
            return
        if _ASSIGNMENT.fullmatch(words[0]):
            raise ValueError("%s:%d: runs %s with %s set, which this reader does not read"
                             % (self.rel, no, words[1], words[0].split("=")[0]))
        if not inside:
            if sources_line and words == [".", RECIPES]:
                return
            raise ValueError("%s:%d: runs %s outside build_lib, which this reader does not read"
                             % (self.rel, no, words[0]))
        if words[0] in KNOWN_CALLS or words[0] in COMPILERS or words[0] in ARCHIVERS:
            return
        if self.port is not None and self.port.function(words[0], self.first) is not None:
            return
        raise ValueError("%s:%d: calls %s, which this reader does not know" % (self.rel, no, words[0]))

    def read(self):
        """The _Built of the block: what the commands of its last build_lib (or a library block's own) compile with,
        each with the flags in force when it runs (_Flags), and each port function they call, read where it is
        called (_Port.run)."""
        others = None if self.port is None else frozenset(t.name for t in self.port.targets()) - {self.target}
        flags = _Flags(self.rel, self.first, others)
        if self.library:
            first, last, run = self.first, self.last, self.top
        else:
            for no, words in self.top:
                for w in words:
                    flags.refer(no, w)
                    if _ASSIGNMENT.fullmatch(w):
                        flags.assign(no, w)
            first, last, run = self.functions[-1]
        for no, words in run:
            for w in words:
                flags.refer(no, w)
            if _ASSIGNMENT.fullmatch(words[0]):
                for w in words:
                    flags.assign(no, w)
            elif words[0] == "oft_build_cmake":
                flags.cmake(no, words[1:])
            elif words[0] == "oft_build_harness":
                if len(words) < 2:
                    raise ValueError("%s:%d: oft_build_harness names no source" % (self.rel, no))
                flags.harness(no, words[1], words[2:])
            elif words[0] in COMPILERS:
                flags.compile_(flags.expand(no, words[1:]))
            elif self.port is not None and self.port.function(words[0], self.first) is not None:
                # the block's words, their quotes taken out: an argument is written again as one word
                args = tuple(w if "$" in w else shlex.quote(w) for w in words[1:])
                self.port.run(flags, words[0], _Call(words[0], args, _Scope(None, (), True), no, ()), ())
        if not self.library:
            flags.compile_(list(flags.env["LIB_CFLAGS"]))
        return _Built(*flags.result("%s:%d-%d" % (self.rel, first, last)), flags, first, last)

    def one(self, built, target=None):
        """(the harness's entry source as build_lib names it, its line): its one oft_build_harness, whose source, in a
        port function, _Port.names names ($T: target, the block's)."""
        if len(built.flags.harnesses) != 1:
            raise ValueError("%s:%d-%d: build_lib calls oft_build_harness %d times, and this reader reads one"
                             % (self.rel, built.first, built.last, len(built.flags.harnesses)))
        no, word, scope = built.flags.harnesses[0]
        if scope is not None:
            names = self.port.names(built.flags, no, word, scope, target)
            if len(names) != 1:
                raise ValueError("%s:%d: oft_build_harness names %d sources (%s), and this reader reads one"
                                 % (self.rel, no, len(names), ", ".join(names)))
            word = names[0]
        return word, no


def _entry(rel, no, target, name):
    """The path, under the build's /work, of the harness's entry source that oft_build_harness names: in the target's
    directory of the recipe, targets/<target>/.  recipes.sh's oft_build_harness looks in the copy of the library's
    tree first; this reader has no copy of that tree, so it takes the file the recipe lays out for the target, which
    tools/enroll/facts.py's deviation_record finds again among the compiles the link took (Reading.entries).  A
    name with a character of pathname expansion (_GLOB) is refused: build_lib's words keep no quotes, so this reader
    cannot tell whether the shell expands it."""
    if "$" in name or ".." in name.split("/") or any(c in name for c in _GLOB):
        raise ValueError("%s:%d: oft_build_harness %s, a path this reader cannot name" % (rel, no, name))
    if name.startswith("/work/"):
        return name[len("/work/"):]
    if name.startswith("/"):
        raise ValueError("%s:%d: oft_build_harness %s, outside /work" % (rel, no, name))
    return "targets/%s/%s" % (target, name)


def _sanitizers_release(path_of, rel, builds):
    """{build: (sanitizer, source)}: the SAN= line of each build's flavour in the release build body at rel, through
    its `if [ "$FLAV" = <flavour> ]` branches (lines 550-591 at the release), each if, elif, else and fi placed by its
    indent; a SAN= line that a build's flavour may reach under any other condition, or of words it does not know, is
    refused."""
    text = _text(path_of, rel)
    want = {}
    for b in builds:
        if b not in FLAVOUR:
            raise ValueError("builds.%s: a build this reader knows no flavour of" % b)
        want[b] = FLAVOUR[b]
    found = {b: None for b in builds}
    # the open ifs: [indent, the flavours of its branches so far (None for an if on anything else), the branch now
    # (an index into them, or "else")]
    frames = []
    lines = text.split("\n")
    no = 0
    while no < len(lines):
        line = lines[no]
        no += 1
        stripped = line.strip()
        indent = len(line) - len(line.lstrip())
        if stripped.startswith("#") or not stripped:
            continue
        m = _FLAV_IF.fullmatch(stripped)
        top = frames[-1] if frames else None
        if m and m.group(1) == "if":
            frames.append([indent, [m.group(2)], 0])
        elif m and top and top[0] == indent and top[1] is not None:
            top[1].append(m.group(2))
            top[2] = len(top[1]) - 1
        elif stripped == "else" and top and top[0] == indent:
            top[2] = "else"
        elif re.match(r"fi\b", stripped) and top and top[0] == indent:
            frames.pop()
        elif re.match(r"(?:el)?if\b", stripped) and stripped.endswith("then"):
            if stripped.startswith("elif"):
                if not (top and top[0] == indent):
                    raise ValueError("%s:%d: an elif this reader cannot place" % (rel, no))
                top[1] = None
            else:
                frames.append([indent, None, None])
        for s in _SAN.finditer(line):
            if not (s.start() == indent and _ASSIGNMENT.fullmatch(stripped)):
                raise ValueError("%s:%d: a SAN= this reader does not read" % (rel, no))
            for b, flavour in want.items():
                runs = all(flavour not in named if branch == "else"
                           else named[branch] == flavour and flavour not in named[:branch]
                           for _indent, named, branch in frames if named is not None)
                if runs and any(named is None for _indent, named, _branch in frames):
                    raise ValueError("%s:%d: SAN= under a condition this reader does not read" % (rel, no))
                if runs:
                    found[b] = (_san(rel, no, stripped), "%s:%d" % (rel, no))
        heredoc = _HEREDOC.search(line)
        if heredoc:
            while no < len(lines) and lines[no].strip() != heredoc.group(1):
                no += 1
            no += 1
    if frames:
        raise ValueError("%s:%d: an if with no fi this reader can place" % (rel, len(lines)))
    for b in builds:
        if found[b] is None:
            raise ValueError("%s: no SAN= line for the %s flavour, which builds.%s is built in" % (rel, want[b], b))
    return found


def _san(rel, no, assignment):
    """The sanitizer of a SAN= line: address, undefined, both, or none; a flag it does not know is refused."""
    try:
        words = shlex.split(_ASSIGNMENT.fullmatch(assignment).group(2), comments=True)
    except ValueError as e:
        raise ValueError("%s:%d: %s" % (rel, no, e)) from None
    on = set()
    for value in " ".join(words).split():
        if value.startswith("-fsanitize="):
            kinds = value[len("-fsanitize="):].split(",")
            if not set(kinds) <= {"address", "undefined"}:
                raise ValueError("%s:%d: %s, a sanitizer this reader does not know" % (rel, no, value))
            on |= set(kinds)
        elif value.startswith("-fno-sanitize="):
            if set(value[len("-fno-sanitize="):].split(",")) & {"address", "undefined"}:
                raise ValueError("%s:%d: %s, which this reader does not read" % (rel, no, value))
        elif not value.startswith(("-fsanitize-", "-fno-sanitize-")):
            raise ValueError("%s:%d: %s, a SAN= word this reader does not know" % (rel, no, value))
    return {frozenset(): "none", frozenset({"address"}): "address", frozenset({"undefined"}): "undefined",
            frozenset({"address", "undefined"}): "address+undefined"}[frozenset(on)]


def _origin(patched, kept, upstream_beside):
    if patched:
        return "patched"
    if kept:
        return "extended" if upstream_beside else "vendored"
    return "upstream"


def _release(path_of, prov, record, builds):
    recipe = record.get("recipe")
    target = recipe.get("target") if isinstance(recipe, dict) else None
    if not isinstance(target, str) or not re.fullmatch(r"[A-Za-z0-9._+-]+", target):
        raise ValueError("%s/PROVENANCE.yaml: recipe.target names no target of the recipe" % prov)
    pin = "%s/recipe/targets/%s/pin" % (prov, target)
    text = _text(path_of, pin)
    block = _Block(pin, text, 1, len(text.split("\n")), sources_line=True)
    built = block.read()
    name, name_at = block.one(built)
    debug, debug_src, unit, unit_src = built.enable_debug, built.debug_source, built.unittests, built.unit_source
    commits = [(no, _ASSIGNMENT.fullmatch(w).group(2)) for no, words in block.top for w in words
               if _ASSIGNMENT.fullmatch(w) and w.startswith("COMMIT=")]
    if not commits:
        raise ValueError("%s: no COMMIT=" % pin)
    commit_at, commit = commits[-1]
    if not _COMMIT.fullmatch(commit):
        raise ValueError("%s:%d: COMMIT=%s, not a full commit id" % (pin, commit_at, commit))
    entry = _entry(pin, name_at, target, name)
    # patched: a patch of PROVENANCE.yaml's recipe.patches applies to the entry source (its applies_to begins with
    # the path, under the recipe)
    patches = recipe.get("patches") or []
    if not isinstance(patches, list) or not all(isinstance(p, dict) for p in patches):
        raise ValueError("%s/PROVENANCE.yaml: recipe.patches is not a list of patches" % prov)
    patched = [p for p in patches if str(p.get("applies_to") or "").split(" ")[0] == entry]
    # kept: recipe/MANIFEST.tsv keeps the entry source as a file of kind ours; beside it, an upstream source of the
    # same target's directory
    manifest = "%s/recipe/MANIFEST.tsv" % prov
    rows = {}
    for no, line in enumerate(_text(path_of, manifest).split("\n"), 1):
        fields = line.split("\t")
        if no == 1 or not line:
            continue
        if len(fields) < 5:
            raise ValueError("%s:%d: not a row of path, sha256, bytes, mode, kind and why" % (manifest, no))
        rows[fields[0]] = (fields[4], no)
    # the build body sources an override of the pin after it when the recipe has one (build-body.sh, after
    # `. /work/targets/$T/pin`): this reader does not read one
    for override in ("targets/%s/override.sh" % target, "harness/native/overrides/%s.sh" % target):
        if override in rows or os.path.lexists(path_of("%s/recipe/%s" % (prov, override))):
            raise ValueError("%s: the recipe has %s, an override of the pin, which this reader does not read"
                             % (manifest, override))
    kind, kind_at = rows.get(entry, (None, None))
    if kind not in (None, "ours", "upstream"):
        raise ValueError("%s:%d: %s is of kind %s, which this reader cannot place" % (manifest, kind_at, entry, kind))
    beside = sorted(path for path, (k, _no) in rows.items() if k == "upstream" and path != entry
                    and path.startswith("targets/%s/" % target) and path.endswith(SOURCE_SUFFIXES))
    origin = _origin(patched, kind == "ours", beside)
    origin_src = ("%s/PROVENANCE.yaml recipe.patches (%s)" % (prov, patched[0].get("file")) if patched
                  else "%s:%d" % (manifest, kind_at) if kind == "ours" else "%s:%d" % (pin, name_at))
    sanitizers = _sanitizers_release(path_of, "%s/recipe/tools/build-body.sh" % prov, builds)
    return _reading(commit, "%s:%d" % (pin, commit_at), debug, debug_src, unit, unit_src, sanitizers, origin,
                    origin_src, target)


# ---------------------------------------------------------------- the target blocks of a port's build.sh

# The target blocks of an OSS Verify port's build.sh, as oss-verify's infra/base-builder/release-target.sh lays them
# out: one reader for this module and the enrolment writer's tools/enroll/facts.py (target_blocks, which
# configured_seals and rust_config read), so that both take the same lines for a block.  It lives here, in a module
# keys.NOT_THE_CHECKER names, so that a change to it re-checks no fuzz target.
#
# A block is a subshell: a line `(` to the next line `)`, each alone on its line but for white space.  Its lines whose
# first word is `ov_target_begin` begin a target (the word after it is the target's name, $T); a block that holds
# `ov_target_build <fuzz target>` builds that fuzz target: ov_target_build runs the block's build_lib and links the
# fuzz target.  A block with no ov_target_build builds no fuzz target: a library block, whose commands run in the
# block itself and leave their build in its directory, $LIBROOT/<its target>, which the blocks of other targets can
# take (curl's curl-fuzz_proto_lib, whose build its structured fuzz targets link).  A `(` line inside a block, or one
# that is never closed, begins no block.  The reader reads lines and words only: it runs no shell, and refuses
# nothing; _Port refuses what it cannot read of a block (port_stray, ov_target_begin with dependencies,
# ov_target_dependency, two targets in one block).
#
# One block: the indexes (0-based) of its `(` and `)` lines and of the lines between them, and [(index, words)] of
# each of those lines whose first word is ov_target_begin, or ov_target_build (str.split's words, any number of them).
PortBlock = collections.namedtuple("PortBlock", "first last lines begins builds")
PORT_BEGIN, PORT_BUILD = "ov_target_begin", "ov_target_build"


def port_blocks(lines):
    """[PortBlock] of each block of a port's build.sh (its lines), in the order of the file."""
    out, start, held = [], None, []
    for i, line in enumerate(lines):
        if start is None and line.strip() == "(":
            start, held = i, []
        elif start is not None and line.strip() == ")":
            words = [(j, lines[j].split()) for j in held]
            out.append(PortBlock(start, i, held, [(j, w) for j, w in words if w[:1] == [PORT_BEGIN]],
                                 [(j, w) for j, w in words if w[:1] == [PORT_BUILD]]))
            start = None
        elif start is not None:
            held.append(i)
    return out


def port_stray(lines, found):
    """[(index, words)] of each ov_target_begin or ov_target_build line of lines outside every block of found."""
    inside = {i for b in found for i in range(b.first, b.last + 1)}
    return [(i, line.split()) for i, line in enumerate(lines)
            if i not in inside and line.split()[:1] in ([PORT_BEGIN], [PORT_BUILD])]


# ---------------------------------------------------------------- a port's blocks and functions

# What _Port reads in the words of a port function: $LIBROOT/<target>, the build directory of a block of build.sh
# (ov_target_begin sets LIBROOT; None for a $LIBROOT with no plain target name after it); "$@", the words of a
# function's arguments, which it runs as a command (curl's pf_bg); an expansion that sets a flag variable; and an
# expansion whose value _Port.names can tell: $N, $name, ${N}, ${name} and ${name<op><pattern>} with op one of
# %% % ## #.
_LIBROOT = re.compile(r"\$(?:LIBROOT(?![A-Za-z0-9_])|\{LIBROOT\})(?:/([A-Za-z0-9._+-]+)(?=$|[/\s\"'}]))?")
# A `..` of a path, and what separates the names of a path in a word: / and the = , : of an option (_Flags.refer)
_CLIMB = re.compile(r"(?<!\.)\.\.(?=$|[/\s\"'])")
_SEGMENTS = re.compile(r"[/=:,\s\"']+")
_RUNNER = ('"$@"', "$@", '"${@}"', "${@}")
_FLAG_DEFAULT = re.compile(r"\$\{(?:%s):?=" % "|".join(FLAG_VARIABLES))
_EXPANSION = re.compile(r"\$(?:([0-9])|([A-Za-z_][A-Za-z0-9_]*)|\{([0-9]|[A-Za-z_][A-Za-z0-9_]*)"
                        r"(?:(%%|%|##|#)([^}'\"$`\\]*))?\})")
_VARIABLE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
# The characters at which field splitting splits the value of an expansion outside double quotes (the shell's IFS,
# unset: space, tab and newline), and the characters that make a word, outside quotes, a pattern of pathname expansion
_IFS = " \t\n"
_GLOB = "*?["
_IFS_NAMED = re.compile(r"(?<![A-Za-z0-9_])IFS(?![A-Za-z0-9_])")
_OPERATORS = ("&&", "||", ";;", ";", "&", "|", "(", ")")
_SETTERS = ("export", "readonly", "local", "unset", "read", "typeset", "declare")
_RESERVED = ("for", "while", "until", "do", "done", "if", "then", "elif", "else", "fi", "case", "esac", "{", "}", "!")


def _unquote(word):
    """A word as the shell passes it on: its quotes and backslashes taken out (shlex's POSIX rules), its expansions as
    written; a word that holds a command substitution, as written."""
    if "$(" in word or "`" in word:
        return word
    try:
        parts = shlex.split(word)
    except ValueError:
        return word
    return parts[0] if len(parts) == 1 else word


def _splits(word):
    """Whether the shell may pass the word `word`, as written, as more or fewer words than one: it holds an expansion
    ($ or `) or a character of _GLOB outside quotes, which field splitting or pathname expansion may make words of."""
    i, quoted = 0, False
    while i < len(word):
        c = word[i]
        if c == "'" and not quoted:
            j = word.find("'", i + 1)
            if j < 0:
                return True
            i = j + 1
        elif c == '"':
            quoted, i = not quoted, i + 1
        elif c == "\\":
            i += 2
        elif not quoted and (c in "$`" or c in _GLOB):
            return True
        else:
            i += 1
    return False


def _skip(rel, no, text, i):
    """The index just past the quote or expansion that begins at text[i] ('...', "...", `...`, $(...) or ${...}),
    each holding the others as the shell reads them; ValueError, naming the line no, for one that does not end."""
    if text[i] == "'":
        j = text.find("'", i + 1)
        if j < 0:
            raise ValueError("%s:%d: a ' that does not end" % (rel, no))
        return j + 1
    opener = text[i] if text[i] in "\"`" else text[i:i + 2]
    closer = {'"': '"', "`": "`", "$(": ")", "${": "}"}[opener]
    j, depth = i + len(opener), 0
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
        elif c == closer and not depth:
            return j + 1
        elif closer != "`" and (c in "`\"" or text.startswith(("$(", "${"), j) or (c == "'" and closer != '"')):
            j = _skip(rel, no + text.count("\n", i, j), text, j)
        elif closer == ")" and c in "()":
            depth += 1 if c == "(" else -1
            j += 1
        else:
            j += 1
    raise ValueError("%s:%d: %s that does not end" % (rel, no, opener))


def _tokens(rel, text, no):
    """(line, kind, text) of each token of shell text whose first line is line no of rel, then (line, "end", None):
    "word", as written (its quotes and expansions kept, a backslash-newline taken out), "op" (one of _OPERATORS, or a
    newline) and "redirect" (< or > and what follows it of <>&|).  A comment is dropped.  ValueError for a
    here-document."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t":
            i += 1
        elif c == "\n":
            yield no, "op", "\n"
            no, i = no + 1, i + 1
        elif text.startswith("\\\n", i):
            no, i = no + 1, i + 2
        elif c == "#":
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("<<", i):
            raise ValueError("%s:%d: a here-document, which this reader does not read" % (rel, no))
        elif c in "<>":
            j = i + 1
            while j < n and text[j] in "<>&|":
                j += 1
            yield no, "redirect", text[i:j]
            i = j
        elif c in ";&|()":
            op = next(o for o in _OPERATORS if text.startswith(o, i))
            yield no, "op", op
            i += len(op)
        else:
            start, at = i, no
            while i < n and text[i] not in " \t\n;&|()<>":
                if text[i] == "\\":
                    no += text.startswith("\\\n", i)
                    i += 2
                elif text[i] in "'\"`" or text.startswith(("$(", "${"), i):
                    j = _skip(rel, no, text, i)
                    no += text.count("\n", i, j)
                    i = j
                else:
                    i += 1
            yield at, "word", text[start:i].replace("\\\n", "")
    yield no, "end", None


# One simple command of shell text: its line, its words as written, [(the construct it runs inside, that construct's
# line)], innermost first (none: its function runs it once, in its own shell), and the for loops around it, outermost
# first: [(variable, the words of its list, its line)].
_Cmd = collections.namedtuple("_Cmd", "line words where loops")
# A function build.sh defines: its name, the lines of its `name() {` and its }, its _Cmds, and [(variable, first line,
# last line)] of each for loop of its body.
_Def = collections.namedtuple("_Def", "name line end commands loops")


class _Shell:
    """The simple commands of shell text (rel, from its line no), in the order of the text, each with the constructs
    around it, as sh reads them: for, while and until loops, if, case, a subshell ( ... ), a { ... } group, && and ||
    lists, pipelines, a command run in the background (&), and a command substitution, whose commands come before the
    command that holds it.  A redirection is dropped with its file.  ValueError, naming the line, for what it cannot
    place."""

    def __init__(self, rel, text, no):
        self.rel, self.tokens, self.defs = rel, _tokens(rel, text, no), []

    def take(self):
        return next(self.tokens)

    def want(self, word):
        no, kind, text = self.take()
        while kind == "op" and text == "\n":
            no, kind, text = self.take()
        if kind != "word" or text != word:
            raise ValueError("%s:%d: %s where this reader reads %s" % (self.rel, no, text or "the end", word))

    def commands(self, closing=None, where=(), loops=(), top=False):
        """([_Cmd], the line they end at, [(variable, first line, last line)] of their for loops): the commands of a
        function's body, to the } that closes it (closing: the line of its `name() {`), or of the whole text.  where
        and loops: what is around the text (a command substitution's).  With top, the text is build.sh outside its
        blocks: a function it defines goes into defs, its body read there, and is none of the text's commands."""
        rel, out, frames, ranges = self.rel, [], [], []
        words, at = [], None
        elem = chain = 0          # where in out the element being read, and its && or || list, begin
        mark = None               # what the operator before that element makes of it: (construct, line)
        simple = join = False     # whether the element just read is a simple command; whether a newline continues

        def around():
            return [(f["kind"], f["line"]) for f in reversed(frames) if f["kind"]] + list(where)

        def looping():
            return list(loops) + [(f["var"], f["list"], f["line"]) for f in frames if f["kind"] == "a for loop"]

        def end_simple():
            nonlocal words, simple
            if words:
                out.extend(self.substituted(words, at, around(), looping()))
                out.append(_Cmd(at, words, around(), looping()))
                words, simple = [], True

        def settle(op, no):
            """The element just read ends at the operator op (of line no)."""
            nonlocal elem, chain, mark, simple, join
            span = out[elem:]
            for c in span if mark else ():
                c.where.append(mark)
            if op in ("&&", "||", "|"):
                kind = "a pipeline" if op == "|" else "an && or || list"
                for c in span if simple or op == "|" else ():
                    c.where.append((kind, no))
                mark, elem, join = (kind, no), len(out), True
            else:
                for c in out[chain:] if op == "&" else ():
                    c.where.append(("a command run in the background (&)", no))
                mark, elem, chain = None, len(out), len(out)
            simple = False

        def open_(kind, no, **more):
            nonlocal elem, chain, mark
            frames.append(dict(kind=kind, line=no, start=len(out), mark=mark, chain=chain, **more))
            elem = chain = len(out)
            mark = None

        def close(no, *kinds):
            nonlocal elem, chain, mark, simple
            if not frames or frames[-1]["kind"] not in kinds:
                raise ValueError("%s:%d: a %s this reader cannot place" % (rel, no, text))
            end_simple()
            settle("\n", no)
            f = frames.pop()
            if f["kind"] == "a for loop":
                ranges.append((f["var"], f["line"], no))
            elem, chain, mark, simple = f["start"], f["chain"], f["mark"], False

        while True:
            no, kind, text = self.take()
            if join and kind == "op" and text == "\n":
                continue
            join = False
            if frames and frames[-1].get("pattern") and not words and kind != "end":
                # a case's pattern, up to its )
                if kind == "word" and text == "esac":
                    close(no, "a case")
                    continue
                while not (kind == "op" and text in ("\n", ")")):
                    no, kind, text = self.take()
                    if kind == "end":
                        raise ValueError("%s:%d: a case pattern that does not end" % (rel, no))
                frames[-1]["pattern"] = text == "\n"
                continue
            if kind == "end":
                end_simple()
                settle("\n", no)
                if frames:
                    raise ValueError("%s:%d: %s that does not end" % (rel, frames[-1]["line"],
                                                                       frames[-1]["kind"] or "a { group"))
                if closing is not None:
                    raise ValueError("%s:%d: a function that is not closed" % (rel, closing))
                return out, no, ranges
            if kind == "redirect":
                if self.take()[1] != "word":
                    raise ValueError("%s:%d: %s with no file, which this reader does not read" % (rel, no, text))
            elif kind == "op" and text == "(" and not words:
                open_("a subshell", no)
            elif kind == "op" and text == ")" and frames and frames[-1]["kind"] == "a subshell":
                close(no, "a subshell")
            elif kind == "op" and text == "(" and len(words) == 1 and _VARIABLE.fullmatch(words[0]):
                # name() {: a function's definition
                if self.take()[2] != ")":
                    raise ValueError("%s:%d: %s(, which this reader cannot read" % (rel, no, words[0]))
                self.want("{")
                name, words = words[0], []
                if not top or frames:
                    raise ValueError("%s:%d: defines %s inside %s, which this reader does not read"
                                     % (rel, no, name, (around() or [("a function",)])[0][0]))
                body, end, body_loops = self.commands(closing=no)
                self.defs.append(_Def(name, no, end, body, body_loops))
            elif kind == "op" and text in ("(", ")"):
                raise ValueError("%s:%d: %r, a shell operator this reader does not read here" % (rel, no, text))
            elif kind == "op":
                end_simple()
                settle(text, no)
                if text == ";;":
                    if not frames or frames[-1]["kind"] != "a case":
                        raise ValueError("%s:%d: ;; outside a case" % (rel, no))
                    frames[-1]["pattern"] = True
            elif words or text not in _RESERVED:
                if not words:
                    at = no
                words.append(text)
            elif text == "for":
                var = self.take()
                if var[1] != "word" or not _VARIABLE.fullmatch(var[2]):
                    raise ValueError("%s:%d: a for loop this reader cannot read" % (rel, no))
                items, t = ['"$@"'], self.take()
                while t[1] == "op" and t[2] == "\n":
                    t = self.take()
                if t[1:] == ("word", "in"):
                    items, t = [], self.take()
                    while t[1] == "word":
                        items.append(t[2])
                        t = self.take()
                    if t[1:] not in (("op", ";"), ("op", "\n")):
                        raise ValueError("%s:%d: a for loop this reader cannot read" % (rel, no))
                    self.want("do")
                elif t[1:] == ("op", ";"):
                    self.want("do")
                elif t[1:] != ("word", "do"):
                    raise ValueError("%s:%d: a for loop this reader cannot read" % (rel, no))
                out.extend(self.substituted(items, no, around(), looping()))
                open_("a for loop", no, var=var[2], list=items)
            elif text in ("while", "until"):
                open_("a %s loop" % text if text == "while" else "an until loop", no)
            elif text == "do":
                if not frames or frames[-1]["kind"] not in ("a while loop", "an until loop"):
                    raise ValueError("%s:%d: a do this reader cannot place" % (rel, no))
            elif text == "done":
                close(no, "a for loop", "a while loop", "an until loop")
            elif text == "if":
                open_("an if", no)
            elif text in ("then", "elif", "else"):
                if not frames or frames[-1]["kind"] != "an if":
                    raise ValueError("%s:%d: a %s this reader cannot place" % (rel, no, text))
            elif text == "fi":
                close(no, "an if")
            elif text == "case":
                subject = self.take()
                if subject[1] != "word":
                    raise ValueError("%s:%d: a case this reader cannot read" % (rel, no))
                out.extend(self.substituted([subject[2]], no, around(), looping()))
                self.want("in")
                open_("a case", no, pattern=True)
            elif text == "esac":
                close(no, "a case")
            elif text == "{":
                open_(None, no, group=True)
            elif text == "}" and not frames and closing is not None:
                settle("\n", no)
                return out, no, ranges
            elif text == "}":
                close(no, None)

    def substituted(self, words, no, where, loops):
        """The commands of each command substitution of words ($(...) or `...`, read from line no), which the shell
        runs before the command that holds it, in a subshell; an arithmetic $((...)) runs none."""
        out = []
        for w in words:
            i, quoted = 0, False
            while i < len(w):
                if w[i] == "\\":
                    i += 2
                elif w[i] == "'" and not quoted:
                    i = w.index("'", i + 1) + 1
                elif w[i] == '"':
                    quoted, i = not quoted, i + 1
                elif w.startswith("$((", i):
                    i = _skip(self.rel, no, w, i)
                elif w.startswith("$(", i) or w[i] == "`":
                    j = _skip(self.rel, no, w, i)
                    line = no + w.count("\n", 0, i)
                    inner = w[i + 2:j - 1] if w[i] == "$" else w[i + 1:j - 1]
                    out += _Shell(self.rel, inner, line).commands(
                        where=[("a command substitution", line)] + list(where), loops=loops)[0]
                    i = j
                else:
                    i += 1
        return out


# A block of build.sh that begins a target: its name and line (ov_target_begin), the fuzz target it builds and the
# line of that ov_target_build (both None for a library block), and the lines of its ( and ).
_Target = collections.namedtuple("_Target", "name begin fuzz build first last")
# A call of a port function: its name, its arguments as written, the _Scope they are written in, its line, and the
# constructs around the call there.
_Call = collections.namedtuple("_Call", "name args scope line where")
# Where a command of a port function runs: the _Call of the function (None for a block's own command), the for loops
# around the command, as _Cmd gives them, and whether the function's positional parameters are still its call's
# there (no set -- or shift before it).
_Scope = collections.namedtuple("_Scope", "call loops positional")


class _Unnamed(Exception):
    """Why _Port.names cannot tell the value of a word."""


class _Port:
    """A port's build.sh (rel, its text): its blocks (port_blocks), and the functions it defines outside every block,
    at the start of a line (`name() {` to its }), which a block's build may call: port functions.

    A port function is read where a block's build_lib, or a library block, calls it (run), with the flags in force
    there, and more weakly than build_lib.  _Block reads every command of build_lib and refuses one it does not know;
    of a port function, this reader reads only where the flags of a compile come from: each assignment of a flag
    variable (FLAG_VARIABLES), oft_build_cmake, oft_build_harness and each $CC or $CXX, with the flags in force when
    each runs, and each call of another port function, read the same way where it is called (a recursion is refused);
    a function whose body runs "$@" (curl's pf_bg) runs its arguments there as a command.  Every other command of a
    port function is skipped: the recipes' other helpers (oft_define_fuzzing_build_mode, say), make, configure and what
    they compile, and a flag a compile takes from another variable.  What this reading gives of a port is so checked
    again, from what the build ran: tools/enroll/facts.py's deviation_record holds enable_debug, unittests and the
    sanitizer to the compiles whose objects each build's link of the fuzz target took (RESULT/links.<build>.json: each
    object and archive member of the link's map, matched by its bytes to every compile that wrote them, wherever it
    ran), finds there the compile of one entry source whose origin harness_origin is (Reading.entries), and stops
    the facts where they differ or where the link took code no recorded compile wrote, so a flag that this reader
    skips, or an object that a path this reader does not follow brings in, fails the facts job rather than passing
    unread.

    A port function is read once where it is called, whatever is around the call (a loop, a condition): what it sets
    stays set after it.  In its own text, a flag variable set inside a construct this reader cannot follow (a for,
    while or until loop, a case, an if, a subshell, an && or || list, a pipeline, a command run in the background, a
    command substitution: _Shell) is refused, naming the line, as is CFLAGS set without $CFLAGS, but for a restore of
    the value the same function saved before (pf_cflags=$CFLAGS, then CFLAGS=$pf_cflags); so are -DENABLE_DEBUG=
    inside such a construct, a flag variable set by export, read, local or unset or in an expansion (${CFLAGS:=...}),
    eval, . and source, and an assignment of T or LIBROOT, which ov_target_begin sets.

    The source that oft_build_harness names in a port function is read as the shell makes words of it and of the
    arguments of each call that leads there (names, _fields): the words of a for loop's list are split as field
    splitting splits them, but this reader does not split an argument: one that the shell may pass as more or fewer
    words than one is refused, naming the line (an expansion outside double quotes whose value holds white space,
    _IFS, or none; any word with a character of _GLOB outside quotes; any expansion outside double quotes where
    build.sh names IFS).  A word with none of these is the one word the shell passes."""

    def __init__(self, rel, text):
        self.rel, self.text = rel, text
        self.lines = text.split("\n")
        self.blocks = port_blocks(self.lines)
        self._top = None
        # the first line of build.sh that names IFS, which may change how the shell splits words
        self.ifs = next((no for no, line in enumerate(self.lines, 1) if _IFS_NAMED.search(line)), None)

    def targets(self):
        """[_Target] of each block that begins a target; ValueError for a block, or a line outside the blocks, that
        this reader cannot place."""
        rel, lines = self.rel, self.lines
        for i, words in port_stray(lines, self.blocks):
            if words[0] == PORT_BEGIN:
                raise ValueError("%s:%d: ov_target_begin outside a block, a subshell ( ... ), which this reader does "
                                 "not read" % (rel, i + 1))
            raise ValueError("%s:%d: an ov_target_build this reader cannot place" % (rel, i + 1))
        out = []
        for b in self.blocks:
            if not b.begins:
                if b.builds:
                    raise ValueError("%s:%d: an ov_target_build this reader cannot place" % (rel, b.builds[0][0] + 1))
                continue
            (i, words), more = b.begins[0], b.begins[1:]
            if len(words) != 2:
                raise ValueError("%s:%d: ov_target_begin with dependencies, which this reader does not read"
                                 % (rel, i + 1))
            if more:
                raise ValueError("%s:%d: ov_target_begin in the block that line %d's began, which this reader does "
                                 "not read" % (rel, more[0][0] + 1, i + 1))
            for j in b.lines:
                if j > i and "ov_target_dependency" in lines[j].split():
                    raise ValueError("%s:%d: ov_target_dependency, which this reader does not read" % (rel, j + 1))
            bad = [j for j, w in b.builds if j < i or len(w) != 2] + [j for j, _w in b.builds[1:]]
            if bad:
                raise ValueError("%s:%d: an ov_target_build this reader cannot place" % (rel, min(bad) + 1))
            build = b.builds[0] if b.builds else (None, [None, None])
            out.append(_Target(words[1], i + 1, build[1][1], build[0] + 1 if b.builds else None, b.first + 1,
                               b.last + 1))
        return out

    def top(self):
        """(the _Defs of the functions build.sh defines outside its blocks, its other commands there, their for
        loops), read once, when a block calls a command that may be a port function."""
        if self._top is None:
            inside = {i for b in self.blocks for i in range(b.first, b.last + 1)}
            shell = _Shell(self.rel, "\n".join("" if i in inside else x for i, x in enumerate(self.lines)), 1)
            commands, _end, loops = shell.commands(top=True)
            for d in shell.defs:
                b = next((b for b in self.blocks if d.line < b.first + 1 < d.end), None)
                if b is not None:
                    raise ValueError("%s:%d: a line ( inside the function %s (lines %d-%d), which this reader cannot "
                                     "place" % (self.rel, b.first + 1, d.name, d.line, d.end))
            self._top = (shell.defs, commands, loops)
        return self._top

    def function(self, name, before):
        """The _Def of the port function `name` that a block whose first line is `before` calls: its last definition
        before that line, or None when build.sh defines none there."""
        if not _VARIABLE.fullmatch(name):
            return None
        found = [d for d in self.top()[0] if d.name == name and d.end < before]
        return found[-1] if found else None

    def library(self, built):
        """(the _Target of the library block whose build a block's build takes, the line that names it), or None:
        the target T of each $LIBROOT/T its build names (built: its _Built), which must be one, the target of one
        block of build.sh, and a library block's, one that builds no fuzz target; ValueError, naming the line, else."""
        rel, named = self.rel, []
        for no, name in built.flags.refs:
            if name is None:
                raise ValueError("%s:%d: names $LIBROOT with no target after it ($LIBROOT/<target>), which this reader "
                                 "cannot read" % (rel, no))
            if named and name != named[0][1]:
                raise ValueError("%s:%d: refers to $LIBROOT/%s, and line %d to $LIBROOT/%s: this reader reads a block "
                                 "that takes the build of one library block" % (rel, no, name, named[0][0],
                                                                                named[0][1]))
            named.append((no, name))
        if not named:
            return None
        no, name = named[0]
        begun = [t for t in self.targets() if t.name == name]
        if len(begun) != 1:
            raise ValueError("%s:%d: refers to $LIBROOT/%s, the build of %s, but %d blocks begin %s (ov_target_begin "
                             "%s), and this reader reads one" % (rel, no, name, name, len(begun), name, name))
        if begun[0].fuzz is not None:
            raise ValueError("%s:%d: refers to $LIBROOT/%s, whose block (line %d) builds the fuzz target %s "
                             "(ov_target_build, line %d): this reader takes the build of a library block only, one "
                             "with no ov_target_build" % (rel, no, name, begun[0].begin, begun[0].fuzz,
                                                          begun[0].build))
        return begun[0], no

    def run(self, flags, name, call, stack):
        """Read the port function `name`, which call (_Call) calls, into flags (_Flags): each of its commands, where
        it runs.  stack: the port functions whose calls lead here."""
        if name in stack:
            raise ValueError("%s:%d: calls %s, which calls itself (%s): a recursion this reader does not read"
                             % (self.rel, call.line, name, " -> ".join(stack + (name,))))
        d = self.function(name, flags.first)
        stack += (name,)
        for var, first, last in d.loops:
            flags.loops.setdefault(var, []).append((name, first, last))
            flags.writes[var] += 1
        saved = {}       # variable: (the flag variable whose value it holds, that value, the variable's writes then)
        for k, c in enumerate(d.commands):
            self.command(flags, c, _Scope(call, tuple(c.loops), self._positional(d, k)), stack, saved)

    def command(self, flags, c, scope, stack, saved):
        """Read the command c (_Cmd) of a port function, run where scope says: an assignment of a flag variable, or a
        value of one that the function saves (saved), or a command (call)."""
        lead = next((i for i, w in enumerate(c.words) if not _ASSIGNMENT.fullmatch(w)), len(c.words))
        for w in c.words:
            flags.refer(c.line, w)
            if _FLAG_DEFAULT.search(w):
                raise ValueError("%s:%d: %s sets a flag variable in an expansion, which this reader does not read"
                                 % (self.rel, c.line, w))
        if lead < len(c.words):
            return self.call(flags, c.words[lead:], c.words[:lead], c.line, c.where, scope, stack)
        for w in c.words:
            word = _unquote(w)
            name = _ASSIGNMENT.fullmatch(word).group(1)
            if name in ("T", "LIBROOT"):
                raise ValueError("%s:%d: sets %s, which ov_target_begin sets for the block" % (self.rel, c.line, name))
            if name in FLAG_VARIABLES and c.where:
                raise ValueError("%s:%d: sets %s inside %s (line %d), which this reader cannot follow"
                                 % ((self.rel, c.line, name) + tuple(c.where[0])))
            flags.assign(c.line, word, saved)
            ref = _bare(word.split("=", 1)[1])
            if ref in FLAG_VARIABLES and name not in FLAG_VARIABLES and not c.where:
                saved[name] = (ref, list(flags.env[ref]), flags.writes[name])
            else:
                saved.pop(name, None)

    def call(self, flags, head, prefix, line, where, scope, stack):
        """Read a command of a port function (line): head, its words as written, after prefix, the assignments the
        shell makes for it alone; where, the constructs around it."""
        cmd = _unquote(head[0])
        port = self.function(cmd, flags.first)
        reads = head[0] in _RUNNER or cmd in COMPILERS or cmd in ("oft_build_cmake", "oft_build_harness") or port
        for w in prefix:
            name = _ASSIGNMENT.fullmatch(w).group(1)
            flags.set(name)
            if name in FLAG_VARIABLES and reads:
                raise ValueError("%s:%d: runs %s with %s set, which this reader does not read"
                                 % (self.rel, line, cmd, name))
        if head[0] in _RUNNER:
            # "$@": the words of the function's arguments, as its call wrote them
            if scope.call is None or not scope.positional:
                raise ValueError("%s:%d: runs \"$@\", whose words this reader cannot tell" % (self.rel, line))
            if scope.call.args:
                self.call(flags, list(scope.call.args), [], scope.call.line, list(where) + list(scope.call.where),
                          scope.call.scope, stack)
        elif cmd in _SETTERS:
            for w in head[1:]:
                name = _unquote(w).split("=", 1)[0]
                if _VARIABLE.fullmatch(name):
                    flags.set(name)
                    if name in FLAG_VARIABLES + ("T", "LIBROOT"):
                        raise ValueError("%s:%d: %s %s, which this reader does not read" % (self.rel, line, cmd, name))
        elif cmd in ("eval", ".", "source"):
            raise ValueError("%s:%d: runs %s, which this reader does not read" % (self.rel, line, cmd))
        elif cmd == "oft_build_cmake":
            flags.cmake(line, [_unquote(w) for w in head[1:]], where)
        elif cmd == "oft_build_harness":
            if len(head) < 2:
                raise ValueError("%s:%d: oft_build_harness names no source" % (self.rel, line))
            flags.harness(line, head[1], [_unquote(w) for w in head[2:]], scope)
        elif cmd in COMPILERS:
            flags.compile_(flags.expand(line, [_unquote(w) for w in head[1:]]))
        elif port is not None:
            self.run(flags, cmd, _Call(cmd, tuple(head[1:]), scope, line, tuple(where)), stack)

    @staticmethod
    def _positional(d, k):
        """Whether the positional parameters of d (a _Def) are still its call's at its command k: no shift, nor a set
        that sets them, before it or in a loop around it."""
        around = {line for _v, _w, line in d.commands[k].loops}
        for j, c in enumerate(d.commands):
            head = [_unquote(w) for w in c.words if not _ASSIGNMENT.fullmatch(w)]
            if head[:1] == ["shift"] or head[:1] == ["set"] and any(w == "--" or not w.startswith(("-", "+"))
                                                                    for w in head[1:]):
                if j < k or around & {line for _v, _w, line in c.loops}:
                    return False
        return True

    def names(self, flags, no, word, scope, target):
        """Each value, sorted, of the word `word` (line no) where scope reads it: with each positional parameter and
        for loop variable bound to each value it takes there (_envs: a for loop's list split into words as the shell
        splits it), $T the block's target (target), and any other variable one build.sh sets once, outside its blocks
        and functions, to a text with no expansion (literal); ValueError, naming the line, for a word whose values this
        reader cannot tell, or that the shell may pass as more or fewer words than one (_one)."""
        try:
            return sorted({self._one(flags, word, env, target, no) for env in self._envs(flags, scope, target)})
        except _Unnamed as e:
            raise ValueError("%s:%d: oft_build_harness %s, a path this reader cannot name: %s"
                             % (self.rel, no, word, e)) from None

    def entries(self, built, lib):
        """[(path under /work, line)] of each entry source the library block lib (_Target) compiles (built, its
        _Built): each value (names) of the source of each of its oft_build_harness, in lib's directory (_entry)."""
        out = set()
        for no, word, scope in built.flags.harnesses:
            for name in self.names(built.flags, no, word, scope, lib.name) if scope is not None else [word]:
                out.add((_entry(self.rel, no, lib.name, name), no))
        return sorted(out)

    def _envs(self, flags, scope, target):
        """Each binding, {name: its value, or the _Unnamed of why it has none}, of the positional parameters and the
        for loop variables where scope runs.  An argument of the call binds its parameter when the shell passes it as
        one word (_one); after one that the shell may pass as more or fewer (_splits), every later parameter has none
        too, since the shell numbers them by the words it made."""
        outer = [{}]
        if scope.call is not None:
            outer, call = [], scope.call
            for env in self._envs(flags, call.scope, target):
                bound, cut = {}, None
                for i, w in enumerate(call.args if scope.positional else (), 1):
                    if cut is not None:
                        bound[str(i)] = _Unnamed("$%d, a parameter after %s, which the call of line %d may pass as "
                                                 "more or fewer words than one" % (i, cut, call.line))
                        continue
                    try:
                        bound[str(i)] = self._one(flags, w, env, target, call.line)
                    except _Unnamed as e:
                        bound[str(i)] = e
                        cut = w if _splits(w) else None
                outer.append(bound)
        out = []
        for env in outer:
            out += self._bind(flags, scope, list(scope.loops), env, target)
        return out

    def _bind(self, flags, scope, loops, env, target):
        if not loops:
            return [env]
        (var, items, line), loops = loops[0], loops[1:]
        try:
            self._certain(flags, scope, var, line)
            values = []
            for w in items:
                values += self._fields(flags, w, env, target, line, split=True)
        except _Unnamed as e:
            return self._bind(flags, scope, loops, dict(env, **{var: e}), target)
        return [e for v in values for e in self._bind(flags, scope, loops, dict(env, **{var: v}), target)]

    @staticmethod
    def _certain(flags, scope, var, line):
        """_Unnamed unless the for loop of line, in the function scope runs in, is all that sets var there: no command
        of the block's build sets var, and no for loop of var but those of that function outside this loop."""
        if var in flags.assigned:
            raise _Unnamed("%s, which a command of the build sets" % var)
        name = scope.call.name
        end = next((last for fn, first, last in flags.loops.get(var, ()) if fn == name and first == line), line)
        for fn, first, _last in flags.loops.get(var, ()):
            if fn != name or (first != line and line < first <= end):
                raise _Unnamed("%s, which another for loop sets (%s)" % (var, fn))

    def _one(self, flags, word, env, target, no):
        """The value of the word `word`, as written, under env (_envs), that the shell passes as one word, as an
        argument of line no: its one field (_fields, not split); _Unnamed for one the shell may make more or fewer
        words of."""
        fields = self._fields(flags, word, env, target, no)
        if len(fields) != 1:
            raise _Unnamed("%s (line %d), an expansion outside double quotes of an empty value, of which the shell "
                           "makes no word" % (word, no))
        return fields[0]

    def _fields(self, flags, word, env, target, no, split=False):
        """The words (fields) the shell makes of the word `word`, as written, under env (_envs), at line no: its
        pieces (_pieces) joined, and, with split, the value of each expansion outside double quotes split at the
        characters of _IFS (field splitting), as the shell splits the words of a for loop's list.  _Unnamed for what
        this reader does not follow: a character of _GLOB outside quotes (pathname expansion), an expansion outside
        double quotes where build.sh names IFS, and, without split, such an expansion whose value holds a character
        of _IFS: this reader does not split an argument."""
        fields, now, begun = [], "", False       # the field being made, and whether it is begun
        for text, kind in self._pieces(flags, word, env, target):
            glob = next((c for c in _GLOB if c in text), None) if kind != "quoted" else None
            if glob:
                raise _Unnamed("%s (line %d) holds %s outside quotes, which pathname expansion reads as a pattern, and "
                               "this reader expands none" % (word, no, glob))
            if kind == "expanded" and self.ifs is not None:
                raise _Unnamed("%s (line %d), an expansion outside double quotes, which build.sh may split otherwise: "
                               "its line %d names IFS" % (word, no, self.ifs))
            if kind != "expanded" or not any(c in _IFS for c in text):
                now, begun = now + text, begun or kind == "quoted" or text != ""
                continue
            if not split:
                raise _Unnamed("%s (line %d), an expansion outside double quotes whose value %r holds white space: the "
                               "shell splits it into words (field splitting), and this reader does not split an "
                               "argument" % (word, no, text))
            parts = re.split("[%s]+" % _IFS, text)
            now, begun = now + parts[0], begun or parts[0] != ""
            for part in parts[1:]:
                if begun:
                    fields.append(now)
                now, begun = part, part != ""
        return fields + [now] if begun else fields

    def _pieces(self, flags, word, env, target):
        """[(text, kind)] of the word `word`, as written, under env (_envs), in order: its quotes and backslashes taken
        out and each expansion's value put in; kind is "quoted" (inside quotes, or after a backslash), "literal" (a
        character written outside quotes) or "expanded" (the value of an expansion outside double quotes).  Inside
        double quotes a backslash quotes only $ ` " \\ and a newline, and is kept before any other character."""
        out, i, quoted = [], 0, False
        while i < len(word):
            c = word[i]
            if c == "'" and not quoted:
                j = word.index("'", i + 1)
                out.append((word[i + 1:j], "quoted"))
                i = j + 1
            elif c == '"':
                out.append(("", "quoted"))
                quoted, i = not quoted, i + 1
            elif c == "\\" and quoted and word[i + 1:i + 2] not in tuple('$`"\\\n'):
                out.append(("\\", "quoted"))
                i += 1
            elif c == "\\":
                out.append((word[i + 1:i + 2], "quoted"))
                i += 2
            elif c == "$":
                m = _EXPANSION.match(word, i)
                if not m:
                    raise _Unnamed("%s, an expansion this reader does not read" % word[i:])
                value = self._lookup(flags, next(g for g in m.group(1, 2, 3) if g), env, target)
                out.append((_trim(value, m.group(4), m.group(5)) if m.group(4) else value,
                            "quoted" if quoted else "expanded"))
                i = m.end()
            elif c == "`":
                raise _Unnamed("%s, a command substitution" % word[i:])
            else:
                out.append((c, "quoted" if quoted else "literal"))
                i += 1
        return out

    def _lookup(self, flags, name, env, target):
        if name in env:
            if isinstance(env[name], _Unnamed):
                raise env[name]
            return env[name]
        if name.isdigit():
            raise _Unnamed("$%s, a parameter this reader cannot tell there" % name)
        if name == "T" and target is not None:
            return target
        return self.literal(name, flags)

    def literal(self, name, flags):
        """The value of the variable `name` that build.sh sets once, outside its blocks, functions and every
        construct, before the block (flags.first), to a text with no expansion, where no command of the block's build
        sets it, nor a command of build.sh before the block in another way; _Unnamed else."""
        if name in flags.assigned or name in flags.loops:
            raise _Unnamed("%s, which the block's build sets" % name)
        _defs, commands, loops = self.top()
        if any(var == name for var, _first, _last in loops):
            raise _Unnamed("%s, which a for loop of build.sh sets" % name)
        found = []
        for c in commands:
            lead = next((i for i, w in enumerate(c.words) if not _ASSIGNMENT.fullmatch(w)), len(c.words))
            found += [(c, w, lead == len(c.words)) for w in c.words[:lead] if _ASSIGNMENT.fullmatch(w).group(1) == name]
            head = [_unquote(w) for w in c.words[lead:]]
            if head and c.line < flags.first and (self.function(head[0], flags.first) or head[0] in _SETTERS
                                                  and any(w.split("=", 1)[0] == name for w in head[1:])):
                raise _Unnamed("%s, which line %d of build.sh may set (%s)" % (name, c.line, head[0]))
        if len(found) != 1:
            raise _Unnamed("%s, which build.sh sets %d times outside its blocks and functions" % (name, len(found)))
        c, w, alone = found[0]
        value = _unquote(w).split("=", 1)[1]
        if not alone or c.where or c.line >= flags.first or "$" in value or "`" in value:
            raise _Unnamed("%s, which line %d of build.sh sets as this reader cannot read" % (name, c.line))
        return value


def _trim(value, op, pattern):
    """${name<op><pattern>} of value: % and %% take out the shortest and the longest end that matches pattern, # and
    ## the shortest and the longest start."""
    cuts = range(len(value) + 1)
    if op in ("%", "%%"):
        k = next((k for k in (reversed(cuts) if op == "%" else cuts) if fnmatch.fnmatchcase(value[k:], pattern)), None)
        return value if k is None else value[:k]
    k = next((k for k in (cuts if op == "#" else reversed(cuts)) if fnmatch.fnmatchcase(value[:k], pattern)), None)
    return value if k is None else value[k:]


def _sources(path_of, rel):
    """[(line, kind, fields)] of the port's sources file (oss-verify's infra/base-builder/lay-out-sources)."""
    out = []
    for no, line in enumerate(_text(path_of, rel).split("\n"), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t")
        out.append((no, fields[0], fields[1:]))
    return out


def _under(path, top):
    return path == top or path.startswith(top.rstrip("/") + "/")


def _in_port(path):
    """True when path, relative to a port's folder, names a place inside it: not absolute, and no `..` segment."""
    return not path.startswith("/") and ".." not in path.split("/")


def _patched_paths(path_of, rel, under):
    """The paths, under /work, that the patch at rel changes when applied at under (git apply, -p1)."""
    paths = set()
    for line in _text(path_of, rel).split("\n"):
        if line.startswith(("--- ", "+++ ")):
            name = line[4:].split("\t")[0].strip()
            if name == "/dev/null":
                continue
            parts = name.split("/", 1)
            if len(parts) != 2:
                raise ValueError("%s: %r, a path git apply -p1 cannot strip" % (rel, name))
            paths.add(posixpath.join(under, parts[1]))
    return paths


def _tree_commit(path_of, top, rows, target):
    """(library_commit, its source) of the target's tree, for a port at top (rows: its sources file's): the row that
    lays out /work/ext/<target>/src (ov_target_begin's SRCDIR), through its links: a git row's commit, or a tree row of
    the checkout that the Dockerfile's fetch-commit makes at the port's COMMIT, which is project.yaml's repo#<commit>
    (oss-verify's tools/check passes it)."""
    sources = top + "/sources"
    where, seen = "ext/%s/src" % target, set()
    while True:
        row = [r for r in rows if len(r[2]) >= 2 and r[2][0] == where and r[1] in ("link", "git", "tree")]
        if where in seen:
            raise ValueError("%s: the links that lay out the tree of %s come back to %s" % (sources, target, where))
        if len(row) != 1:
            raise ValueError("%s: %d rows lay out %s, the tree of %s, and this reader reads one"
                             % (sources, len(row), where, target))
        seen.add(where)
        no, kind, fields = row[0]
        if kind == "link":
            where = fields[1]
            continue
        break
    if kind == "git":
        if len(fields) < 3 or not _COMMIT.fullmatch(fields[2]):
            raise ValueError("%s:%d: a git row with no full commit id" % (sources, no))
        return fields[2], "%s:%d" % (sources, no)
    docker = top + "/Dockerfile"
    fetch = ["RUN fetch-commit $SRC/%s" % fields[1], "RUN fetch-commit --submodules $SRC/%s" % fields[1]]
    if not any(line.strip() in fetch for line in _text(path_of, docker).split("\n")):
        raise ValueError("%s:%d: the tree of %s is a copy of %s, which %s does not fetch with fetch-commit"
                         % (sources, no, target, fields[1], docker))
    project = top + "/project.yaml"
    repo = _yaml(path_of, project).get("repo")
    ref = repo.partition("#")[2] if isinstance(repo, str) else ""
    if not _COMMIT.fullmatch(ref):
        raise ValueError("%s: repo is %r, which names no full commit id" % (project, repo))
    line = next((n for n, t in enumerate(_text(path_of, project).split("\n"), 1) if t.startswith("repo:")), None)
    return ref, "%s:%d" % (project, line) if line else project


def _entry_origin(path_of, top, rows, entry, target, script, name_at):
    """(harness_origin, its source) of the entry source at entry (a path under /work) that oft_build_harness of line
    name_at of script compiles in the directory of target: a patch row whose patch changes it; else the row that lays
    it out, through the links that lay out a directory above it: a file of the project's (copy, or a tree of the
    Dockerfile's copy of the project) is a kept copy, a download or a checkout is upstream; beside it, an upstream
    source file of the same target's directory, targets/<target>/."""
    sources = top + "/sources"
    for no, kind, fields in rows:
        if kind == "patch":
            if len(fields) < 2:
                raise ValueError("%s:%d: a patch row names no patch" % (sources, no))
            if not _in_port(fields[1]):
                raise ValueError("%s:%d: the patch row names no file of the port" % (sources, no))
    names, seen = [entry], set()        # entry, and its path under each link's target
    while True:
        path = names[-1]
        laid = [(no, kind, fields) for no, kind, fields in rows if len(fields) >= 2 and kind != "patch"
                and (fields[0] == path if kind in ("file", "copy") else
                     _under(path, fields[0]) if kind in ("tree", "git", "archive", "link") else False)]
        if len(laid) != 1:
            raise ValueError("%s: %d rows lay out %s, the harness's entry source (%s:%d), and this reader reads one"
                             % (sources, len(laid), path, script, name_at))
        laid_at, laid_kind, laid_fields = laid[0]
        if laid_kind != "link":
            break
        if laid_at in seen or not _in_port(laid_fields[1]):
            raise ValueError("%s:%d: a link this reader cannot follow to %s, the harness's entry source"
                             % (sources, laid_at, entry))
        seen.add(laid_at)
        names.append(laid_fields[1] + path[len(laid_fields[0]):])
    patched = [no for no, kind, fields in rows if kind == "patch"
               and set(names) & _patched_paths(path_of, "%s/%s" % (top, fields[1]), fields[0])]
    kept = laid_kind == "copy" or (laid_kind == "tree" and _under(laid_fields[1], "project"))
    beside = [no for no, kind, fields in rows if kind == "file" and len(fields) >= 2 and fields[0] not in names
              and _under(fields[0], "targets/%s" % target) and fields[0].endswith(SOURCE_SUFFIXES)]
    return _origin(patched, kept, beside), "%s:%d" % (sources, patched[0] if patched else laid_at)


def _joined(own, own_src, lib, lib_src):
    """(value, source) of a flag of a block's own build (own) and of the library block's whose build it takes (lib):
    true where either is."""
    if lib:
        return True, lib_src
    if own:
        return True, own_src
    return False, "%s and %s" % (own_src, lib_src)


def _port(path_of, prov, record, builds, harness_name):
    port = record.get("port")
    path = port.get("path") if isinstance(port, dict) else None
    if not isinstance(path, str) or not _in_port(path):
        raise ValueError("%s/PROVENANCE.yaml: port.path names no directory of the port" % prov)
    top = "%s/port/%s" % (prov, path)
    script = top + "/build.sh"
    shell = _Port(script, _text(path_of, script))
    mine = [t for t in shell.targets() if t.fuzz == harness_name]
    if len(mine) != 1:
        raise ValueError("%s: %d blocks build %s (ov_target_build %s), and this reader reads one"
                         % (script, len(mine), harness_name, harness_name))
    t = mine[0]
    block = _Block(script, shell.text, t.begin + 1, t.build - 1, port=shell, target=t.name)
    built = block.read()
    rows = _sources(path_of, top + "/sources")
    commit, commit_src = _tree_commit(path_of, top, rows, t.name)
    debug, debug_src, unit, unit_src = built.enable_debug, built.debug_source, built.unittests, built.unit_source
    # the library block whose build this block takes ($LIBROOT/<it>): its enable_debug, unittests and library_commit,
    # since the binary holds that build's code; its entry sources, when build_lib compiles none
    took, lib = shell.library(built), None
    if took is not None:
        lib, at = took
        if built.flags.cmake_at:
            raise ValueError("%s:%d: build_lib runs oft_build_cmake, and takes the build of %s ($LIBROOT/%s, line %d): "
                             "this reader cannot tell which library the binary holds"
                             % (script, built.flags.cmake_at[0], lib.name, lib.name, at))
        lib_built = _Block(script, shell.text, lib.begin + 1, lib.last - 1, port=shell, library=True,
                           target=lib.name).read()
        if lib_built.flags.refs:
            raise ValueError("%s:%d: the library block %s names $LIBROOT too: this reader does not read a library "
                             "block that takes the build of another" % (script, lib_built.flags.refs[0][0], lib.name))
        lib_commit, lib_commit_src = _tree_commit(path_of, top, rows, lib.name)
        if lib_commit != commit:
            raise ValueError("%s: the tree of %s (%s) is at %s, and the tree of %s, whose build it takes (line %d), at "
                             "%s: this reader cannot tell which the binary holds"
                             % (script, t.name, commit_src, commit, lib.name, at, lib_commit))
        commit_src = lib_commit_src
        debug, debug_src = _joined(debug, debug_src, lib_built.enable_debug, lib_built.debug_source)
        unit, unit_src = _joined(unit, unit_src, lib_built.unittests, lib_built.unit_source)
    if built.flags.harnesses or lib is None:
        name, name_at = block.one(built, t.name)
        entries = [(_entry(script, name_at, t.name, name), name_at, t.name)]
    else:
        entries = [(entry, no, lib.name) for entry, no in shell.entries(lib_built, lib)]
        if not entries:
            raise ValueError("%s:%d-%d: neither build_lib nor the library block %s (lines %d-%d), whose build it "
                             "takes, calls oft_build_harness, and this reader reads one"
                             % (script, built.first, built.last, lib.name, lib.first, lib.last))
    # one origin, whichever of the library block's entry sources the binary holds
    origins = sorted({_entry_origin(path_of, top, rows, entry, owner, script, no) for entry, no, owner in entries})
    if len(origins) != 1:
        raise ValueError("%s:%d: the %d entry sources that the library block %s compiles have %d origins (%s), and "
                         "this reader cannot tell which of them the binary of %s holds"
                         % (script, entries[0][1], len(entries), lib.name, len(origins),
                            "; ".join("%s, %s" % o for o in origins), harness_name))
    origin, origin_src = origins[0]
    sanitizers = {}
    for b in builds:
        if b not in PORT_SANITIZER:
            raise ValueError("builds.%s: a build this reader knows no sanitizer of" % b)
        sanitizers[b] = (spelled(PORT_SANITIZER[b]), "the port's %s build (SANITIZER=%s)" % (b, PORT_SANITIZER[b]))
    return _reading(commit, commit_src, debug, debug_src, unit, unit_src, sanitizers, origin, origin_src, t.name,
                    lib and lib.name, tuple(sorted({Entry("/work/" + entry, owner, "%s:%d" % (script, no))
                                                    for entry, no, owner in entries})))


def _reading(commit, commit_src, debug, debug_src, unit, unit_src, sanitizers, origin, origin_src, target,
             library=None, entries=None):
    values = {"library_commit": commit, "enable_debug": debug, "unittests": unit,
              "sanitizer": {b: s for b, (s, _src) in sanitizers.items()}, "harness_origin": origin}
    sources = {"library_commit": commit_src, "enable_debug": debug_src, "unittests": unit_src,
              "harness_origin": origin_src}
    sources.update({"sanitizer.%s" % b: src for b, (_s, src) in sanitizers.items()})
    return Reading(values, sources, target, library, entries)


def spelled(sanitizer):
    """deviation.sanitizer's spelling of a SANITIZER value of the toolchain (tools/enroll/toolchain_info.py)."""
    if sanitizer not in SPELLING:
        raise ValueError("SANITIZER=%s, a sanitizer this reader does not know" % sanitizer)
    return SPELLING[sanitizer]


def read_record(path_of, prov, harness_name, builds):
    """The Reading of a fuzz target's deviation record from its build record at prov, a folder of the tree (R2(b),
    R2(c)): its PROVENANCE.yaml names a port (the copy of the port's projects/<project>/build.sh, its block, a
    subshell, from `ov_target_begin <target>` to `ov_target_build <harness_name>`, with the port functions it calls
    (_Port), and the library block whose build it takes, when it names $LIBROOT/<library>: its enable_debug, unittests
    and library_commit, and its entry sources when the block compiles none; Reading.entries, the entry sources whose
    origin is harness_origin), or else a release recipe (recipe/targets/<recipe.target>/pin).  path_of(rel) is the
    path of the tree's file rel; builds, the names of harness.yaml's builds.  The last build_lib of the block wins.
    ValueError, naming the file and the line, for what it cannot read."""
    record = _yaml(path_of, prov + "/PROVENANCE.yaml")
    builds = [b for b in schema.BUILDS if b in builds]
    if record.get("port") is not None:
        return _port(path_of, prov, record, builds, harness_name)
    return _release(path_of, prov, record, builds)


def from_recipe(tree, harness):
    """read_record of the fuzz target `harness` of tree, from the build record in its provenance folder."""
    p, h = harness.project.name, harness.name
    return read_record(tree.path, layout.provenance_dir(p, h, tree.unit_layout("%s/%s" % (p, h))), h,
                       harness.data.get("builds") or {})


# ---------------------------------------------------------------- the check

def _show(value):
    if value is True:
        return "true"
    if value is False:
        return "false"
    return "missing" if value is None else str(value)


def compare(record, derived, scans, builds):
    """The messages of each field of record (harness.yaml's deviation) that differs from derived (from_recipe's
    Reading) or the scans ({build: Scan, or why its scan cannot be read}), each `deviation.<field> is <x>, but <source>
    gives <y>`, and one for each build of builds (harness.yaml's) whose scan is missing or is of another binary than
    builds.<build>.sha256.  A withheld build (builds.<build>.withheld) has no sha256 to hold a scan to, so its scan is
    neither required nor compared: tls_backend is what the scans of the other builds give.  When every build is
    withheld, no scan gives tls_backend, so compare takes the record's value, and the harness README says that no
    published build has a scan, so no check reads that value (harness-README.md.tmpl's deviation_tls_unscanned)."""
    out = []
    for field in ("library_commit", "enable_debug", "unittests", "harness_origin"):
        if record.get(field) != derived.values[field]:
            out.append("deviation.%s is %s, but %s gives %s" % (field, _show(record.get(field)),
                                                                derived.sources[field], _show(derived.values[field])))
    named = record.get("sanitizer") if isinstance(record.get("sanitizer"), dict) else {}
    for b, value in derived.values["sanitizer"].items():
        if named.get(b) != value:
            out.append("deviation.sanitizer.%s is %s, but %s gives %s"
                       % (b, _show(named.get(b)), derived.sources["sanitizer." + b], value))
    # Not facts.Harness.builds(), which generate.py's deviation bullet reads: on a harness.yaml that rules.check
    # accepts, both give the builds that are not withheld.  compare takes harness.yaml's raw builds mapping
    # (lint.check_deviation passes h.data.get("builds"), test_deviation passes mappings), and lint runs check_deviation
    # even when rules.check refuses the file, so a build record can be no mapping: Harness.builds() calls .get on it
    # and raises, and here it is not withheld, so its scan is reported.  One reader for both would mean a change to
    # generate.py, which is part of the checker key (keys.NOT_THE_CHECKER leaves out deviation.py, not generate.py).
    good, published = {}, [b for b, rec in builds.items() if not (isinstance(rec, dict) and rec.get("withheld"))]
    for b in published:
        rec = builds[b]
        s = scans.get(b)
        pin = rec.get("sha256") if isinstance(rec, dict) else None
        if s is None:
            out.append("deviation.tls_backend: builds.%s has no scan (evidence/deviation/%s.tls.tsv)" % (b, b))
        elif isinstance(s, str):
            out.append("deviation.tls_backend: %s" % s)
        elif s.sha256 != pin:
            out.append("deviation.tls_backend: the scan of builds.%s is of the binary with sha256 %s, but "
                       "builds.%s.sha256 is %s: scan the twin of this build again" % (b, s.sha256, b, pin))
        else:
            good[b] = s
    if good:
        try:
            tls = backend(good)
        except ValueError as e:
            out.append("deviation.tls_backend: %s" % e)
        else:
            if record.get("tls_backend") != tls:
                held = _held(good, tls) if tls != "none" else ""
                out.append("deviation.tls_backend is %s, but the scans of builds %s give %s%s"
                           % (_show(record.get("tls_backend")), ", ".join(sorted(good)), tls,
                              " (%s)" % held if held else ""))
    return out
