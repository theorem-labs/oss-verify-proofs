"""deviation.py: the TLS scan of a build's unstripped twin and its file, the TLS library a fuzz target's scans give,
the deviation record read again from a release recipe or an OSS Verify port, and the check that compares the two
(OSSV-484, R2; C1's cases and its negative controls).  The ELF files are written here, at test time: no binary is
committed for them (lint.ELF_FIXTURES)."""
import os
import re
import struct
import tempfile
import unittest

from oft import deviation, facts, layout
from oft.tests.helpers import REPO, Tree

HARNESS = ("zlib", "checksum_fuzzer")
TARGET = "zlib-checksum_fuzzer"
COMMIT = "51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf"      # the fixture's library.commit
OTHER = "f" * 64
NO_TLS = {library: (0, ()) for library in deviation.LIBRARIES}
SANITIZER = {"plain": "none", "ubsan": "undefined", "asan": "address", "asan-ubsan": "address+undefined"}

# ---------------------------------------------------------------- an ELF file, written here

EM_RISCV = 243
_TYPE = {"func": 2, "object": 1}
_BIND = {"local": 0, "global": 1, "weak": 2}


def write_elf(path, symbols):
    """A riscv64 ELF64 executable at path with .text, .symtab and .strtab, whose symbol table holds symbols,
    [(name, kind, binding)] (kind func or object, binding local, global or weak), each 4 bytes of .text."""
    text = b"\x13\x00\x00\x00" * max(1, len(symbols))           # nop
    ordered = sorted(symbols, key=lambda s: s[2] != "local")    # the local symbols first, as ELF has them
    strtab, rows = b"\0", [b"\0" * 24]
    for i, (name, kind, binding) in enumerate(ordered):
        rows.append(struct.pack("<IBBHQQ", len(strtab), _BIND[binding] << 4 | _TYPE[kind], 0, 1, 0x10000 + 4 * i, 4))
        strtab += name.encode() + b"\0"
    symtab = b"".join(rows)
    shstrtab = b"\0.text\0.symtab\0.strtab\0.shstrtab\0"
    offsets, at = [], 64
    for blob in (text, symtab, strtab, shstrtab):
        offsets.append(at)
        at += len(blob)
    shoff = (at + 7) & ~7
    first_global = 1 + sum(1 for s in ordered if s[2] == "local")
    sections = [struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                struct.pack("<IIQQQQIIQQ", 1, 1, 0x6, 0x10000, offsets[0], len(text), 0, 0, 4, 0),
                struct.pack("<IIQQQQIIQQ", 7, 2, 0, 0, offsets[1], len(symtab), 3, first_global, 8, 24),
                struct.pack("<IIQQQQIIQQ", 15, 3, 0, 0, offsets[2], len(strtab), 0, 0, 1, 0),
                struct.pack("<IIQQQQIIQQ", 23, 3, 0, 0, offsets[3], len(shstrtab), 0, 0, 1, 0)]
    header = struct.pack("<16sHHIQQQIHHHHHH", b"\x7fELF\x02\x01\x01", 2, EM_RISCV, 1, 0x10000, 0, shoff, 0, 64, 0, 0,
                         64, len(sections), 4)
    with open(path, "wb") as f:
        f.write(header + text + symtab + strtab + shstrtab + b"\0" * (shoff - at) + b"".join(sections))


# cURL's own names, and one static function whose name begins with wolfCrypt's wc_ (lib/ftp.c), with a libc name
CURL_ONLY = [("Curl_ssl_init", "func", "global"), ("curl_easy_init", "func", "global"),
             ("wc_statemach", "func", "local"), ("memcpy", "func", "global"), ("Curl_ssl_backend", "object", "global")]
OPENSSL = CURL_ONLY + [("SSL_new", "func", "global")]


class Scans(unittest.TestCase):
    """tls_scan counts each library's global and weak names in the unstripped twin; its file reads back as written."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = self._tmp.name

    def tearDown(self):
        self._tmp.cleanup()

    def scan(self, symbols, sha256=OTHER):
        path = os.path.join(self.dir, "twin")
        write_elf(path, symbols)
        return deviation.tls_scan(path, sha256)

    def test_an_openssl_name_is_openssl(self):
        s = self.scan(OPENSSL)
        self.assertEqual(s.counts["openssl"], (1, ("SSL_new",)))
        self.assertEqual({k: v for k, v in s.counts.items() if k != "openssl"},
                         {k: v for k, v in NO_TLS.items() if k != "openssl"})
        self.assertEqual(deviation.backend({"plain": s}), "openssl")

    def test_curls_own_names_are_no_tls_library(self):
        """Curl_* and curl_* match no prefix, and a static function of cURL's (wc_statemach, lib/ftp.c) is local."""
        s = self.scan(CURL_ONLY)
        self.assertEqual(s.counts, NO_TLS)
        self.assertEqual(deviation.backend({"plain": s, "asan": s}), "none")
        for name in ("Curl_ssl_init", "curl_easy_init", "Curl_ossl_init", "curl_global_sslset"):
            self.assertFalse(any(name.startswith(p) for _l, ps in deviation.PREFIXES for p in ps), name)

    def test_each_prefix_counts_for_its_library(self):
        for library, prefixes in deviation.PREFIXES:
            for prefix in prefixes:
                with self.subTest(prefix=prefix):
                    s = self.scan(CURL_ONLY + [(prefix + "x", "func", "weak"), (prefix + "y", "object", "global")])
                    self.assertEqual(s.counts[library], (2, (prefix + "x", prefix + "y")))
                    self.assertEqual(deviation.backend({"plain": s}), library)

    def test_a_local_name_of_a_prefix_is_not_counted(self):
        self.assertEqual(self.scan(CURL_ONLY + [("SSL_ERROR_to_str", "func", "local")]).counts, NO_TLS)

    def test_the_file_keeps_five_names_and_the_count(self):
        names = ["gnutls_%d" % i for i in range(7)]
        s = self.scan(CURL_ONLY + [(n, "func", "global") for n in names], "a" * 64)
        text = deviation.render_scan(s)
        self.assertEqual(text.split("\n")[2], "gnutls\t7\t" + ",".join(sorted(names)[:5]))
        self.assertTrue(text.startswith("# oss-fuzz-theorems/tls-scan/1 sha256=%s unstripped=%s\nopenssl\t0\t-\n"
                                        % ("a" * 64, s.unstripped)))
        path = os.path.join(self.dir, "deviation", "plain.tls.tsv")
        deviation.write_scan(path, s)
        self.assertEqual(deviation.load_scan(path), s)

    def test_a_file_it_cannot_read_is_refused_naming_the_line(self):
        good = deviation.render_scan(self.scan(OPENSSL))
        for why, text, line in (("no header", good.replace("tls-scan/1", "tls-scan/2"), "line 1"),
                                ("rows out of order", good.replace("openssl", "wolfssl", 1), "line 2"),
                                ("a count that is not one", good.replace("openssl\t1", "openssl\tone"), "line 2"),
                                ("names the count does not give", good.replace("SSL_new", "SSL_new,SSL_free"),
                                 "line 2"),
                                ("no newline at the end", good[:-1], "newline")):
            with self.subTest(why=why):
                self.assertRaisesRegex(ValueError, line, deviation.parse_scan, text)

    def test_a_stripped_sha256_that_is_not_one_is_refused(self):
        self.assertRaisesRegex(ValueError, "not a sha256", self.scan, OPENSSL, "plain")

    def test_names_of_two_libraries_are_refused_naming_both(self):
        a, b = self.scan(OPENSSL), self.scan(CURL_ONLY + [("wolfSSL_new", "func", "global")])
        with self.assertRaises(ValueError) as e:
            deviation.backend({"plain": a, "asan": b})
        self.assertIn("openssl (plain: SSL_new)", str(e.exception))
        self.assertIn("wolfssl (asan: wolfSSL_new)", str(e.exception))


# ---------------------------------------------------------------- recipes, written into the fixture tree

PIN = """URL=https://github.com/madler/zlib.git
COMMIT=%s
BUILD_IMAGE=builder
. /work/tools/ossfuzz/recipes.sh
build_lib() {
  oft_require_target_cxx
  oft_build_cmake
  oft_build_harness "fuzz.cc"
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
""" % COMMIT

# the release build body's choice of SAN by flavour (projects/curl/*/proofs/provenance/recipe/tools/build-body.sh)
BODY = """#!/bin/sh
if [ "$FLAV" = gcc ]; then
  SAN=""
else
  if [ "${OFT_MUSL_PATCHED:-0}" = 1 ]; then
    echo patched
  fi
  cat > /tmp/x.h <<'POISON'
if [ "$FLAV" = asan ]; then
  SAN="-fsanitize=memory"
fi
POISON
  if [ "$FLAV" = asan ]; then
    CC=sealed
    SAN="-fsanitize=address"
  elif [ "$FLAV" = asanubsan ]; then
    SAN="-fsanitize=address -fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
  elif [ "$FLAV" = ubsan ]; then
    SAN="-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
  else
    SAN=""
  fi
fi
CFLAGS="$BASE_CFLAGS $SAN"
"""
MANIFEST = "path\tsha256\tbytes\tmode\tkind\twhy\n"
PORT_PROJECT = "repo: https://github.com/madler/zlib#%s\nprimary_contact: n/a\n" % COMMIT
DOCKERFILE = "FROM base\nARG REPO\nARG COMMIT\nRUN fetch-commit $SRC/upstream/zlib\nCOPY . $SRC/project/\n"
SOURCES = ("tree\text/%s/src\tupstream/zlib\n"
           "file\ttargets/%s/fuzz.cc\thttps://raw.githubusercontent.com/x/y/%s/fuzz.cc\t%s\n"
           % (TARGET, TARGET, "1" * 40, "2" * 64))
PATCH = """A change to the harness.

--- a/fuzz.cc\t2026-10-31 19:10:56.000000000 +0000
+++ b/fuzz.cc\t2026-10-31 19:11:39.000000000 +0000
@@ -1 +1 @@
-int a;
+int b;
"""


def port_script(block):
    return ("#!/bin/sh -e\n. /usr/local/lib/oss-verify/release-target.sh\n\n(\nov_target_begin %s\n%sov_target_build "
            "checksum_fuzzer\n)\n" % (TARGET, block))


BLOCK = 'LIB_ARCHIVE="lib/liboft.a"\nbuild_lib() {\n  oft_build_cmake\n  oft_build_harness "fuzz.cc"\n}\n'


def write_release(t, prov, pin=PIN, patches=(), manifest=MANIFEST, body=BODY):
    """A release recipe of the fixture fuzz target in its build record at prov: PROVENANCE.yaml naming the recipe's
    target and each of patches as a patch of that file of the target's directory, the pin, recipe/MANIFEST.tsv and
    the build body; the pin's path."""
    patched = "".join("  - file: recipe/targets/%s/%s\n    applies_to: targets/%s/%s (sha256 %s), with patch -p1\n"
                      % (TARGET, p, TARGET, p, "3" * 64) for p in patches)
    t.write(prov + "/PROVENANCE.yaml", "recipe:\n  target: %s\n  patches:%s\n%s"
            % (TARGET, "" if patches else " []", patched))
    t.write("%s/recipe/targets/%s/pin" % (prov, TARGET), pin)
    t.write(prov + "/recipe/MANIFEST.tsv", manifest)
    t.write(prov + "/recipe/tools/build-body.sh", body)
    return "%s/recipe/targets/%s/pin" % (prov, TARGET)


class Recipes(unittest.TestCase):
    """from_recipe reads enable_debug, unittests, library_commit, the sanitizer of each build and harness_origin from
    the fixture fuzz target's build record, and refuses what it cannot read, naming the file and the line."""

    def setUp(self):
        self.t = Tree(render=False)
        self.tree = facts.load(self.t.root)
        self.h = self.tree.projects[HARNESS[0]].harnesses[HARNESS[1]]
        self.prov = layout.provenance_dir(*HARNESS, self.tree.unit_layout("/".join(HARNESS)))

    def tearDown(self):
        self.t.close()

    def release(self, pin=PIN, patches=(), manifest=MANIFEST, body=BODY):
        self.pin = write_release(self.t, self.prov, pin, patches, manifest, body)

    def port(self, block=BLOCK, sources=SOURCES, files=(), script=None):
        """The fixture's port: its build.sh, port_script(block) unless script gives it whole, and its sources rows."""
        top = self.prov + "/port/projects/zlib"
        self.t.write(self.prov + "/PROVENANCE.yaml", "port:\n  repository: theorem-labs/oss-verify\n  commit: %s\n"
                     "  path: projects/zlib\n" % ("4" * 40))
        self.t.write(top + "/build.sh", port_script(block) if script is None else script)
        self.t.write(top + "/sources", "# kind\tpath\targuments\n" + sources)
        self.t.write(top + "/Dockerfile", DOCKERFILE)
        self.t.write(top + "/project.yaml", PORT_PROJECT)
        for name, text in files:
            self.t.write("%s/%s" % (top, name), text)
        self.script = top + "/build.sh"

    def read(self):
        return deviation.from_recipe(self.tree, self.h)

    def refused(self, text):
        with self.assertRaises(ValueError) as e:
            self.read()
        self.assertRegex(str(e.exception), text)

    def with_lib(self, *lines):
        """PIN with its build_lib's calls replaced by lines."""
        return re.sub(r"build_lib\(\) \{\n.*?\n\}", lambda _m: "build_lib() {\n%s\n}" % "\n".join(lines), PIN,
                      flags=re.DOTALL)

    def test_a_release_recipe_of_the_fuzzing_build_is_read(self):
        self.release()
        r = self.read()
        self.assertEqual(r.values, {"library_commit": COMMIT, "enable_debug": False, "unittests": False,
                                    "sanitizer": SANITIZER, "harness_origin": "upstream"})
        self.assertEqual(r.sources["library_commit"], self.pin + ":2")
        self.assertEqual({b: r.sources["sanitizer." + b] for b in SANITIZER},
                         {b: self.prov + "/recipe/tools/build-body.sh:%d" % n
                          for b, n in (("plain", 21), ("ubsan", 19), ("asan", 15), ("asan-ubsan", 17))})

    def test_enable_debug_on_is_enable_debug(self):
        self.release(self.with_lib("  oft_build_cmake -DCURL_USE_LIBPSL=OFF -DENABLE_DEBUG=ON",
                                   '  oft_build_harness "fuzz.cc"'))
        r = self.read()
        self.assertEqual((r.values["enable_debug"], r.values["unittests"]), (True, False))
        self.assertEqual(r.sources["enable_debug"], self.pin + ":6")

    def test_enable_debug_on_as_two_words_is_enable_debug(self):
        """cmake takes -D NAME=VALUE as two words, and oft_build_cmake passes its words to cmake ("$@", recipes.sh)."""
        self.release(self.with_lib("  oft_build_cmake -D CURL_USE_LIBPSL=OFF -D ENABLE_DEBUG=ON",
                                   '  oft_build_harness "fuzz.cc"'))
        r = self.read()
        self.assertEqual((r.values["enable_debug"], r.values["unittests"]), (True, False))
        self.assertEqual(r.sources["enable_debug"], self.pin + ":6")

    def test_the_last_enable_debug_wins(self):
        self.release(self.with_lib("  oft_build_cmake -DENABLE_DEBUG=ON -DENABLE_DEBUG:BOOL=off",
                                   '  oft_build_harness "fuzz.cc"'))
        self.assertIs(self.read().values["enable_debug"], False)

    def test_a_flag_that_defines_debugbuild_is_enable_debug(self):
        self.release(self.with_lib("  oft_build_cmake", '  OFT_HARNESS_CFLAGS="-DHAVE_CONFIG_H -DDEBUGBUILD"',
                                   '  oft_build_harness "fuzz.cc"'))
        r = self.read()
        self.assertIs(r.values["enable_debug"], True)
        self.assertEqual(r.sources["enable_debug"], self.pin + ":7")

    def test_cflags_with_unittests_is_unittests(self):
        self.release(self.with_lib('  CFLAGS="$CFLAGS -DUNITTESTS"; CXXFLAGS="${CXXFLAGS:-} -DUNITTESTS"',
                                   "  oft_build_cmake", '  oft_build_harness "fuzz.cc"'))
        r = self.read()
        self.assertEqual((r.values["enable_debug"], r.values["unittests"]), (False, True))
        self.assertEqual(r.sources["unittests"], self.pin + ":6")

    def test_a_flag_undefined_again_is_not_defined(self):
        self.release(self.with_lib('  CFLAGS="$CFLAGS -DUNITTESTS -UUNITTESTS"', "  oft_build_cmake",
                                   '  oft_build_harness "fuzz.cc"'))
        self.assertIs(self.read().values["unittests"], False)

    def test_the_last_build_lib_wins(self):
        """curl's pins define build_lib twice; the second definition is the one the build runs."""
        second = 'build_lib() {\n  oft_build_cmake%s\n  oft_build_harness "fuzz.cc"\n}\n'
        self.release(PIN.replace("  oft_build_cmake\n", "  oft_build_cmake -DENABLE_DEBUG=ON\n") + second % "")
        r = self.read()
        self.assertIs(r.values["enable_debug"], False)
        self.assertEqual(r.sources["enable_debug"], self.pin + ":12-15")
        self.release(PIN + second % " -DENABLE_DEBUG=ON")
        r = self.read()
        self.assertIs(r.values["enable_debug"], True)
        self.assertEqual(r.sources["enable_debug"], self.pin + ":13")

    def test_a_harness_patch_is_patched(self):
        self.release(patches=("fuzz.cc",))
        r = self.read()
        self.assertEqual(r.values["harness_origin"], "patched")
        self.assertIn("recipe.patches", r.sources["harness_origin"])

    def test_a_patch_of_another_file_leaves_the_harness_upstream(self):
        self.release(patches=("other.cc",))
        self.assertEqual(self.read().values["harness_origin"], "upstream")

    def test_a_kept_copy_beside_an_upstream_harness_is_extended(self):
        self.release(manifest=MANIFEST + "targets/%s/fuzz.cc\t%s\t1\t644\tours\tour entry point\n"
                     "targets/%s/upstream_fuzzer.c\t%s\t1\t644\tupstream\tthe target's own harness\n"
                     % (TARGET, "5" * 64, TARGET, "6" * 64))
        r = self.read()
        self.assertEqual(r.values["harness_origin"], "extended")
        self.assertEqual(r.sources["harness_origin"], self.prov + "/recipe/MANIFEST.tsv:2")

    def test_a_kept_copy_with_no_upstream_harness_is_vendored(self):
        self.release(manifest=MANIFEST + "targets/%s/fuzz.cc\t%s\t1\t644\tours\ta copy\n" % (TARGET, "5" * 64))
        self.assertEqual(self.read().values["harness_origin"], "vendored")

    def test_an_unknown_call_is_refused_naming_the_file_and_line(self):
        self.release(self.with_lib("  oft_build_cmake", "  oft_build_autotools --disable-x",
                                   '  oft_build_harness "fuzz.cc"'))
        self.refused(re.escape(self.pin + ":7: calls oft_build_autotools"))

    def test_what_it_cannot_read_is_refused_naming_the_file_and_line(self):
        for why, pin, at in (
                ("a variable it does not know", PIN.replace("LIB_CFLAGS=\"\"", "DEPENDS=\"openssl\""),
                 ":11: sets DEPENDS"),
                ("CFLAGS without the flavour's", self.with_lib('  CFLAGS="-DUNITTESTS"', "  oft_build_cmake",
                                                               '  oft_build_harness "fuzz.cc"'), ":6: sets CFLAGS"),
                ("CMake flags the toolchain file replaces",
                 self.with_lib("  oft_build_cmake -DCMAKE_C_FLAGS=-DUNITTESTS", '  oft_build_harness "fuzz.cc"'),
                 ":6: -DCMAKE_C_FLAGS="),
                ("an ENABLE_DEBUG value it does not know",
                 self.with_lib("  oft_build_cmake -DENABLE_DEBUG=$X", '  oft_build_harness "fuzz.cc"'),
                 ":6: -DENABLE_DEBUG="),
                ("CMake flags the toolchain file replaces, as two words",
                 self.with_lib("  oft_build_cmake -D CMAKE_C_FLAGS=-DUNITTESTS", '  oft_build_harness "fuzz.cc"'),
                 ":6: -DCMAKE_C_FLAGS="),
                ("an ENABLE_DEBUG value it does not know, as two words",
                 self.with_lib("  oft_build_cmake -D ENABLE_DEBUG=$X", '  oft_build_harness "fuzz.cc"'),
                 ":6: -DENABLE_DEBUG="),
                ("a command substitution", self.with_lib('  CFLAGS="$CFLAGS $(cat flags)"', "  oft_build_cmake",
                                                         '  oft_build_harness "fuzz.cc"'), ":6: .* runs a command"),
                ("a pipe", self.with_lib("  oft_build_cmake | tee log", '  oft_build_harness "fuzz.cc"'), ":6: '\\|'"),
                ("no build_lib", PIN.split("build_lib")[0], ":1-.*: no build_lib"),
                ("two harnesses", self.with_lib('  oft_build_harness "a.cc"', '  oft_build_harness "b.cc"'),
                 ":5-8: build_lib calls oft_build_harness 2 times"),
                ("a helper function", PIN + "helper() {\n  oft_build_cmake\n}\n", ":12: defines helper")):
            with self.subTest(why=why):
                self.release(pin)
                self.refused(re.escape(self.pin) + at)

    def test_an_override_of_the_pin_is_refused(self):
        self.release()
        self.t.write("%s/recipe/targets/%s/override.sh" % (self.prov, TARGET), "build_lib() { :; }\n")
        self.refused("override.sh, an override of the pin")

    def test_a_san_line_it_does_not_know_is_refused(self):
        body = self.prov + "/recipe/tools/build-body.sh"
        for why, text, at in (
                ("a sanitizer it does not know", BODY.replace('SAN="-fsanitize=address"', 'SAN="-fsanitize=memory"'),
                 ":15: -fsanitize=memory"),
                ("a word it does not know", BODY.replace('SAN="-fsanitize=address"', 'SAN="-fsanitize=address -O0"'),
                 ":15: -O0"),
                ("SAN= under another condition", BODY.replace("    CC=sealed\n",
                                                              '    if [ -n "$X" ]; then\n      SAN=""\n    fi\n'),
                 ":15: SAN= under a condition"),
                ("no line for a flavour", BODY.replace('    SAN=""\n  fi\nfi', "  fi\nfi"),
                 ": no SAN= line for the plain")):
            with self.subTest(why=why):
                self.release(body=text)
                self.refused(re.escape(body) + at)

    def test_a_port_block_is_read(self):
        self.port(BLOCK.replace("  oft_build_cmake\n", '  CFLAGS="$CFLAGS -DUNITTESTS"\n'
                                "  oft_build_cmake -DENABLE_DEBUG=ON -DCMAKE_BUILD_TYPE=Debug\n"))
        r = self.read()
        self.assertEqual(r.values, {"library_commit": COMMIT, "enable_debug": True, "unittests": True,
                                    "sanitizer": SANITIZER, "harness_origin": "upstream"})
        self.assertEqual(r.sources["library_commit"], self.prov + "/port/projects/zlib/project.yaml:1")
        self.assertEqual(r.sources["enable_debug"], self.script + ":9")
        self.assertEqual(r.sources["unittests"], self.script + ":8")

    def test_a_port_patch_of_the_harness_is_patched(self):
        self.port(sources=SOURCES + "patch\ttargets/%s\tfuzz.patch\n" % TARGET, files=(("fuzz.patch", PATCH),))
        r = self.read()
        self.assertEqual(r.values["harness_origin"], "patched")
        self.assertEqual(r.sources["harness_origin"], self.prov + "/port/projects/zlib/sources:4")

    def test_a_port_copy_beside_an_upstream_harness_is_extended_and_alone_vendored(self):
        copy = "tree\text/%s/src\tupstream/zlib\ncopy\ttargets/%s/fuzz.cc\tfuzz.cc\n" % (TARGET, TARGET)
        self.port(sources=copy)
        self.assertEqual(self.read().values["harness_origin"], "vendored")
        self.port(sources=copy + "file\ttargets/%s/upstream_fuzzer.c\thttps://example.invalid/u.c\t%s\n"
                  % (TARGET, "7" * 64))
        self.assertEqual(self.read().values["harness_origin"], "extended")

    def test_a_port_library_from_a_git_row_is_its_commit(self):
        self.port(sources="link\text/%s/src\text/lib\ngit\text/lib\thttps://github.com/madler/zlib.git\t%s\n"
                  "file\ttargets/%s/fuzz.cc\thttps://example.invalid/f.cc\t%s\n" % (TARGET, "8" * 40, TARGET, "2" * 64))
        r = self.read()
        self.assertEqual(r.values["library_commit"], "8" * 40)
        self.assertEqual(r.sources["library_commit"], self.prov + "/port/projects/zlib/sources:3")

    def test_what_it_cannot_read_of_a_port_is_refused_naming_the_file_and_line(self):
        for why, block, sources, text in (
                ("an unknown call", BLOCK.replace("  oft_build_cmake\n", "  oft_build_cmake\n  make -j4\n"), SOURCES,
                 re.escape(self.prov) + r"/port/projects/zlib/build.sh:9: calls make"),
                ("an entry source no row lays out", BLOCK, SOURCES.split("\n")[0] + "\n",
                 r"sources: 0 rows lay out targets/%s/fuzz.cc" % TARGET),
                ("a library tree no row lays out", BLOCK, SOURCES.split("\n")[1] + "\n",
                 r"sources: 0 rows lay out ext/%s/src" % TARGET),
                ("a patch above the port", BLOCK, SOURCES + "patch\ttargets/%s\t../../outside.patch\n" % TARGET,
                 r"/port/projects/zlib/sources:4: the patch row names no file of the port$"),
                ("a patch at an absolute path", BLOCK, SOURCES + "patch\ttargets/%s\t/etc/outside.patch\n" % TARGET,
                 r"/port/projects/zlib/sources:4: the patch row names no file of the port$")):
            with self.subTest(why=why):
                self.port(block, sources)
                self.refused(text)
        self.port()
        self.t.write(self.prov + "/port/projects/zlib/build.sh",
                     port_script(BLOCK).replace("ov_target_begin %s" % TARGET, "ov_target_begin %s openssl" % TARGET))
        self.refused(re.escape(self.script) + ":5: ov_target_begin with dependencies")

    def test_a_plain_port_block_reads_as_before_and_names_its_target(self):
        """A block that takes no library block's build reads as it did before library blocks: its own build_lib,
        harness and tree; its Reading names its target, whose trace facts.py's deviation_record reads, and no
        library."""
        self.port()
        r = self.read()
        self.assertEqual(r.values, {"library_commit": COMMIT, "enable_debug": False, "unittests": False,
                                    "sanitizer": SANITIZER, "harness_origin": "upstream"})
        self.assertEqual({k: v for k, v in r.sources.items() if not k.startswith("sanitizer.")},
                         {"library_commit": self.prov + "/port/projects/zlib/project.yaml:1",
                          "enable_debug": self.script + ":7-10", "unittests": self.script + ":7-10",
                          "harness_origin": self.prov + "/port/projects/zlib/sources:3"})
        self.assertEqual((r.target, r.library), (TARGET, None))

    def test_the_toolchain_spelling_is_the_records(self):
        self.assertEqual(deviation.spelled("address-undefined"), "address+undefined")
        self.assertEqual([deviation.spelled(deviation.PORT_SANITIZER[b]) for b in SANITIZER], list(SANITIZER.values()))
        self.assertRaises(ValueError, deviation.spelled, "memory")

    @unittest.skipUnless(os.path.exists(os.path.join(REPO, "tools", "enroll", "toolchain_info.py")),
                         "no tools/enroll: `oft release-tree` removes it")
    def test_the_port_sanitizers_are_toolchain_infos(self):
        """deviation.PORT_SANITIZER and FLAVOUR are tools/enroll/toolchain_info.py's SANITIZER and FLAV, read from
        its source: no module of tools/oft, nor these tests, imports tools/enroll (keys.NOT_THE_CHECKER)."""
        with open(os.path.join(REPO, "tools", "enroll", "toolchain_info.py"), encoding="utf-8") as f:
            source = f.read()
        for name, mine in (("SANITIZER", deviation.PORT_SANITIZER), ("FLAV", deviation.FLAVOUR)):
            line = re.search(r"^%s = (\{.*\})$" % name, source, re.MULTILINE)
            self.assertEqual(eval(line.group(1), {}), mine, name)


# curl's shape (oss-verify b22f13a0, projects/curl/build.sh): the library block zlib-lib builds what the fuzz targets
# share through port functions that build.sh defines outside its blocks (lib_build; entry, which run_bg runs in the
# background for each row of ROWS), with UNITTESTS in the library's own compiles only, and compiles the entry point of
# every fuzz target; the block of each fuzz target takes that build ($LIBROOT/zlib-lib, link_lib) and compiles none.
# @lib@, @ref@ and @more@ are what a test adds to lib_build, the target link_lib names, and blocks after the two.
SHARED = r'''#!/bin/sh -e
. /usr/local/lib/oss-verify/release-target.sh

ROWS="
  checksum_fuzzer:one
  other_fuzzer:two
"
# run_bg <command>: the command, in the background
run_bg() {
  "$@" &
}
# entry <fuzz target> <profile>: its entry point, in a directory of its own
entry() {
  BUILDDIR=$BUILDDIR/t/$1
  OFT_HARNESS_CFLAGS="-DCURL_DISABLE_DEPRECATION -I$BUILDDIR/$2"
  oft_build_harness "entrypoints/$1.cc"
}
lib_build() {
  saved=$CFLAGS
  CFLAGS="$CFLAGS -DUNITTESTS"
  oft_build_cmake -DENABLE_DEBUG=ON \
    -DCMAKE_BUILD_TYPE=Debug
  CFLAGS=$saved
@lib@  ( cd "$BUILDDIR" && CC="$CC" CFLAGS="$CFLAGS" ./configure --without-tls )
  for row in $ROWS; do
    run_bg entry "${row%%:*}" "${row#*:}"
  done
  for s in a b; do
    run_bg "$CXX" $CFLAGS -g -c "$s.cc"
  done
  case "$CC" in
    *clang*) cc=clang ;;
    *) ;;
  esac
}
link_lib() {
  lib=$LIBROOT/@ref@
  cp "$lib/lib/liboft.a" "$BUILDDIR/lib/liboft.a"
}

(
ov_target_begin zlib-lib
oft_require_target_cxx
lib_build
)

(
ov_target_begin zlib-checksum_fuzzer
LIB_ARCHIVE="lib/liboft.a"
build_lib() {
  oft_require_target_cxx
  link_lib
  oft_seal_getenv
}
ov_target_build checksum_fuzzer
)
@more@'''
# the tree of both blocks, and the entry points, a git tree that targets/zlib-lib links to
SHARED_SOURCES = ("tree\text/zlib-lib/src\tupstream/zlib\nlink\text/%s/src\text/zlib-lib/src\n"
                  "git\text/entries\thttps://github.com/x/entries.git\t%s\nlink\ttargets/zlib-lib\text/entries\n"
                  % (TARGET, "9" * 40))


def shared(lib="", ref="zlib-lib", more=""):
    return SHARED.replace("@lib@", lib).replace("@ref@", ref).replace("@more@", more)


def line_of(text, needle, after=0):
    """The number of the first line of text, after line `after`, that holds needle."""
    return next(no for no, line in enumerate(text.split("\n"), 1) if no > after and needle in line)


def split_args(args, call, harness="$1", top=""):
    """shared(), with the lines `top` and ARGS=<args> before ROWS, `call` in place of lib_build's call of entry for each
    row, and entry's oft_build_harness naming entrypoints/<harness>.cc."""
    return (shared().replace('ROWS="', '%sARGS=%s\nROWS="' % (top, args), 1)
            .replace('    run_bg entry "${row%%:*}" "${row#*:}"\n', "    %s\n" % call)
            .replace('oft_build_harness "entrypoints/$1.cc"', 'oft_build_harness "entrypoints/%s.cc"' % harness))


def own_harness(text):
    """shared()'s text with the block of checksum_fuzzer compiling its own entry source too, fuzz.cc (OWN_SOURCES)."""
    return text.replace("  link_lib\n  oft_seal_getenv\n",
                        '  link_lib\n  oft_build_harness "fuzz.cc"\n  oft_seal_getenv\n')


OWN_SOURCES = SHARED_SOURCES + "file\ttargets/%s/fuzz.cc\thttps://raw.githubusercontent.com/x/y/%s/fuzz.cc\t%s\n" % (
    TARGET, "1" * 40, "2" * 64)


class LibraryBlocks(unittest.TestCase):
    """A port's block that takes the build of a library block ($LIBROOT/<it>), as curl's structured fuzz targets take
    curl-fuzz_proto_lib's: it reads the library block's enable_debug, unittests and library_commit, and its entry
    sources, through the port functions both call; and the refusals of what this reader cannot read of such a port."""

    setUp, tearDown, port, read, refused = Recipes.setUp, Recipes.tearDown, Recipes.port, Recipes.read, Recipes.refused

    def test_a_block_takes_the_library_blocks_enable_debug_unittests_and_entry(self):
        text = shared()
        self.port(sources=SHARED_SOURCES, script=text)
        r = self.read()
        self.assertEqual(r.values, {"library_commit": COMMIT, "enable_debug": True, "unittests": True,
                                    "sanitizer": SANITIZER, "harness_origin": "upstream"})
        self.assertEqual((r.target, r.library), (TARGET, "zlib-lib"))
        self.assertEqual(r.sources["enable_debug"], "%s:%d" % (self.script, line_of(text, "oft_build_cmake")))
        self.assertEqual(r.sources["unittests"], "%s:%d" % (self.script, line_of(text, "-DUNITTESTS")))
        self.assertEqual(r.sources["library_commit"], self.prov + "/port/projects/zlib/project.yaml:1")
        # each entry point the library block compiles, targets/zlib-lib/entrypoints/<row>.cc, is a file of the git
        # tree that targets/zlib-lib links to
        self.assertEqual(r.sources["harness_origin"], self.prov + "/port/projects/zlib/sources:4")

    def test_the_three_refusals_of_a_library_blocks_build(self):
        two = "(\nov_target_begin zlib-two\noft_require_target_cxx\n)\n"
        other = ('(\nov_target_begin zlib-other\nLIB_ARCHIVE="lib/liboft.a"\nbuild_lib() {\n  oft_build_cmake\n'
                 '  oft_build_harness "other.cc"\n}\nov_target_build other_fuzzer\n)\n')
        text = shared(ref="zlib-lib\n  two=${LIBROOT}/zlib-two/lib", more=two)
        cases = [(text, "%d: refers to $LIBROOT/zlib-two, and line %d to $LIBROOT/zlib-lib: this reader reads a block "
                  "that takes the build of one library block" % (line_of(text, "two=${LIBROOT}"),
                                                                 line_of(text, "lib=$LIBROOT")))]
        text = shared(ref="zlib-none")
        cases.append((text, "%d: refers to $LIBROOT/zlib-none, the build of zlib-none, but 0 blocks begin zlib-none "
                      "(ov_target_begin zlib-none), and this reader reads one" % line_of(text, "lib=$LIBROOT")))
        text = shared(ref="zlib-other", more=other)
        cases.append((text, "%d: refers to $LIBROOT/zlib-other, whose block (line %d) builds the fuzz target "
                      "other_fuzzer (ov_target_build, line %d): this reader takes the build of a library block only, "
                      "one with no ov_target_build" % (line_of(text, "lib=$LIBROOT"),
                                                       line_of(text, "ov_target_begin zlib-other"),
                                                       line_of(text, "ov_target_build other_fuzzer"))))
        for text, message in cases:
            with self.subTest(message=message):
                self.port(sources=SHARED_SOURCES, script=text)
                self.refused("^%s$" % re.escape("%s:%s" % (self.script, message)))

    def test_a_flag_variable_set_in_a_loop_of_a_port_function_is_refused(self):
        text = shared(lib='  for s in a; do\n    CFLAGS="$CFLAGS -DUNITTESTS"\n  done\n')
        self.port(sources=SHARED_SOURCES, script=text)
        loop = line_of(text, "for s in a; do")
        self.refused("^%s:%d: sets CFLAGS inside a for loop \\(line %d\\), which this reader cannot follow$"
                     % (re.escape(self.script), loop + 1, loop))

    def test_what_it_cannot_follow_in_a_port_function_is_refused_naming_the_line(self):
        # each: what lib_build gains, the text of the line refused, and the start of the refusal after the line
        for lib, at, needle in (
                ('  case x in\n    x) CXXFLAGS="$CXXFLAGS -DX" ;;\n  esac\n', "x) CXXFLAGS",
                 "sets CXXFLAGS inside a case"),
                ('  if [ -n "$X" ]; then\n    LIB_CFLAGS=-DX\n  fi\n', "LIB_CFLAGS=-DX",
                 "sets LIB_CFLAGS inside an if"),
                ("  ( OFT_HARNESS_CFLAGS=-DX )\n", "( OFT_HARNESS", "sets OFT_HARNESS_CFLAGS inside a subshell"),
                ('  [ -n "$X" ] && CFLAGS="$CFLAGS -DX"\n', "] && CFLAGS", "sets CFLAGS inside an && or || list"),
                ('  [ -n "$X" ] || oft_build_cmake -DENABLE_DEBUG=OFF\n', "] || oft_build_cmake",
                 "-DENABLE_DEBUG= inside an && or || list"),
                ("  CFLAGS=$other\n", "CFLAGS=$other", "sets CFLAGS without $CFLAGS"),
                ("  export CFLAGS\n", "export CFLAGS", "export CFLAGS, which this reader does not read"),
                ("  lib_build\n", "  lib_build", "calls lib_build, which calls itself (lib_build -> lib_build)")):
            with self.subTest(needle=needle):
                text = shared(lib=lib)
                self.port(sources=SHARED_SOURCES, script=text)
                no = line_of(text, at, after=line_of(text, "lib_build() {"))
                self.refused("^%s" % re.escape("%s:%d: %s" % (self.script, no, needle)))

    def test_entry_sources_of_different_origins_are_refused(self):
        # a patch of one of the entry points, in the git tree that targets/zlib-lib links to: the reader cannot tell
        # which entry point the binary of checksum_fuzzer holds, so it takes neither origin
        self.port(sources=SHARED_SOURCES + "patch\text/entries\tentry.patch\n", script=shared(),
                  files=(("entry.patch", PATCH.replace("fuzz.cc", "entrypoints/checksum_fuzzer.cc")),))
        self.refused(r":\d+: the 2 entry sources that the library block zlib-lib compiles have 2 origins "
                     r"\(patched, .*sources:6; upstream, .*sources:4\)")

    def test_the_reading_names_each_entry_source_and_its_block(self):
        # what tools/enroll/facts.py's deviation_record finds again among the compiles of the build: each entry point
        # that the library block compiles, or a plain block's own; a release recipe's reading names none
        text = shared()
        self.port(sources=SHARED_SOURCES, script=text)
        at = "%s:%d" % (self.script, line_of(text, "oft_build_harness"))
        self.assertEqual(self.read().entries, tuple(
            deviation.Entry("/work/targets/zlib-lib/entrypoints/%s.cc" % n, "zlib-lib", at)
            for n in ("checksum_fuzzer", "other_fuzzer")))
        self.port()
        self.assertEqual(self.read().entries, (deviation.Entry(
            "/work/targets/%s/fuzz.cc" % TARGET, TARGET,
            "%s:%d" % (self.script, line_of(port_script(BLOCK), "oft_build_harness"))),))
        Recipes.release(self)
        self.assertIsNone(self.read().entries)

    def test_an_argument_the_shell_may_make_other_words_of_is_refused_naming_the_line(self):
        # Sol's case (the review of #2955, finding 2): the shell splits $ARGS into two words, so $1 is the first; this
        # reader does not split an argument, so it reads none, and names the line of the call. So for a pattern, which
        # pathname expansion reads, an empty value, of which the shell makes no word, a parameter after such an
        # argument, and any expansion outside double quotes where build.sh names IFS
        space = "an expansion outside double quotes whose value %r holds white space: the shell splits it into words " \
                "(field splitting), and this reader does not split an argument"
        pattern = "holds %s outside quotes, which pathname expansion reads as a pattern, and this reader expands none"
        for args, call, harness, top, why in (
                ("'checksum_fuzzer one'", "run_bg entry $ARGS", "$1", "",
                 "$ARGS (line {call}), " + space % "checksum_fuzzer one"),
                ('"checksum\tone"', "run_bg entry $ARGS", "$1", "", "$ARGS (line {call}), " + space % "checksum\tone"),
                ("'checksum_fuzze?'", "run_bg entry $ARGS", "$1", "", "$ARGS (line {call}) " + pattern % "?"),
                ("x", "run_bg entry checksum_fuzz[e]r", "$1", "", "checksum_fuzz[e]r (line {call}) " + pattern % "["),
                ("", "run_bg entry $ARGS", "$1", "",
                 "$ARGS (line {call}), an expansion outside double quotes of an empty value, of which the shell makes "
                 "no word"),
                ("'a b'", "run_bg entry $ARGS checksum_fuzzer", "$2", "",
                 "$2, a parameter after $ARGS, which the call of line {call} may pass as more or fewer words than one"),
                ("checksum_fuzzer", "run_bg entry $ARGS", "$1", "IFS=_\n",
                 "$ARGS (line {call}), an expansion outside double quotes, which build.sh may split otherwise: its "
                 "line {ifs} names IFS")):
            with self.subTest(call=call, args=args):
                text = split_args(args, call, harness, top)
                self.port(sources=SHARED_SOURCES, script=text)
                message = why.format(call=line_of(text, call), ifs=line_of(text, "IFS") if top else None)
                self.refused("^%s$" % re.escape('%s:%d: oft_build_harness "entrypoints/%s.cc", a path this reader '
                                                'cannot name: %s' % (self.script, line_of(text, "oft_build_harness"),
                                                                     harness, message)))

    def test_an_argument_with_no_white_space_and_no_pattern_is_the_one_word_it_reads(self):
        # a value with neither splits to itself; double quotes keep a value with white space one word, and the
        # parameters after it the shell's; and in double quotes a backslash quotes only $ ` " \ and a newline, so the
        # shell keeps it before any other character
        for args, call, harness, name in (
                ("checksum_fuzzer", "run_bg entry $ARGS", "$1", "checksum_fuzzer"),
                ("'checksum fuzzer'", 'run_bg entry "$ARGS"', "$1", "checksum fuzzer"),
                ("'a b'", 'run_bg entry "$ARGS" checksum_fuzzer', "$2", "checksum_fuzzer"),
                ("checksum_fuzzer", "run_bg entry $ARGS", "\\x$1", "\\xchecksum_fuzzer")):
            with self.subTest(call=call, harness=harness):
                self.port(sources=SHARED_SOURCES, script=split_args(args, call, harness))
                r = self.read()
                self.assertEqual(r.values["harness_origin"], "upstream")
                self.assertEqual([e.path for e in r.entries], ["/work/targets/zlib-lib/entrypoints/%s.cc" % name])

    def test_a_harness_name_build_lib_gives_with_a_pattern_is_refused(self):
        # build_lib's words keep no quotes: this reader cannot tell whether the shell expands the pattern
        self.port(BLOCK.replace('"fuzz.cc"', '"fuzz*.cc"'))
        self.refused("^%s$" % re.escape("%s:9: oft_build_harness fuzz*.cc, a path this reader cannot name"
                                        % self.script))

    def test_a_libroot_at_the_blocks_top_level_takes_the_library_blocks_build(self):
        # LIB_ARCHIVE, which the driver links, names the library block's build at the block's top level, and link_lib
        # names none: the block takes that build, as it does through $LIBROOT/zlib-lib in a port function
        text = own_harness(shared()).replace("lib=$LIBROOT/zlib-lib", "lib=$BUILDDIR").replace(
            'LIB_ARCHIVE="lib/liboft.a"', 'LIB_ARCHIVE="$LIBROOT/zlib-lib/lib/liboft.a"')
        self.port(sources=OWN_SOURCES, script=text)
        r = self.read()
        self.assertEqual((r.target, r.library), (TARGET, "zlib-lib"))
        self.assertEqual((r.values["enable_debug"], r.values["unittests"]), (True, True))
        self.assertEqual(r.sources["unittests"], "%s:%d" % (self.script, line_of(text, "-DUNITTESTS")))

    def test_a_path_into_another_blocks_tree_but_libroot_is_refused_naming_the_line(self):
        # the block of checksum_fuzzer, which compiles its own harness, reaching zlib-lib's build by another path than
        # $LIBROOT/zlib-lib, in a port function or at its top level: out of its own directory (..), or by a name of
        # zlib-lib's directory
        climb = "names .., a path out of the block's directory: this reader reads another block's build only as " \
                "$LIBROOT/<target>"
        named = "names the directory of zlib-lib, another block's target (ov_target_begin zlib-lib): this reader " \
                "reads another block's build only as $LIBROOT/<target>"
        for old, new, why in (
                ("lib=$LIBROOT/zlib-lib", 'lib="$BUILDDIR/../zlib-lib"', "lib=$BUILDDIR/../zlib-lib " + climb),
                ("lib=$LIBROOT/zlib-lib", "lib=../zlib-lib", "lib=../zlib-lib " + climb),
                ("lib=$LIBROOT/zlib-lib", "lib=/work/build/lib/plain/zlib-lib",
                 "lib=/work/build/lib/plain/zlib-lib " + named),
                ('LIB_ARCHIVE="lib/liboft.a"', 'LIB_ARCHIVE="$BUILDDIR/../zlib-lib/lib/liboft.a"',
                 "LIB_ARCHIVE=$BUILDDIR/../zlib-lib/lib/liboft.a " + climb),
                ('LIB_ARCHIVE="lib/liboft.a"', 'LIB_ARCHIVE="/work/targets/zlib-lib/liboft.a"',
                 "LIB_ARCHIVE=/work/targets/zlib-lib/liboft.a " + named)):
            with self.subTest(new=new):
                text = own_harness(shared()).replace(old, new)
                self.port(sources=OWN_SOURCES, script=text)
                self.refused("^%s$" % re.escape("%s:%d: %s" % (self.script, line_of(text, new), why)))

    def test_a_library_block_that_names_libroot_is_refused(self):
        text = shared(lib="  other=$LIBROOT/zlib-checksum_fuzzer\n")
        self.port(sources=SHARED_SOURCES, script=text)
        self.refused("^%s$" % re.escape("%s:%d: the library block zlib-lib names $LIBROOT too: this reader does not "
                                        "read a library block that takes the build of another"
                                        % (self.script, line_of(text, "other=$LIBROOT"))))

    def test_a_block_that_runs_oft_build_cmake_and_takes_a_library_blocks_build_is_refused(self):
        text = shared().replace("  link_lib\n  oft_seal_getenv\n", "  oft_build_cmake\n  link_lib\n  oft_seal_getenv\n")
        self.port(sources=SHARED_SOURCES, script=text)
        cmake = line_of(text, "oft_build_cmake", after=line_of(text, "ov_target_begin %s" % TARGET))
        self.refused("^%s$" % re.escape("%s:%d: build_lib runs oft_build_cmake, and takes the build of zlib-lib "
                                        "($LIBROOT/zlib-lib, line %d): this reader cannot tell which library the "
                                        "binary holds" % (self.script, cmake, line_of(text, "lib=$LIBROOT"))))

    def test_a_block_and_a_library_block_of_trees_at_two_commits_are_refused(self):
        # the block's tree a git checkout at another commit than the library block's, the port's own (project.yaml)
        sources = SHARED_SOURCES.replace(
            "link\text/%s/src\text/zlib-lib/src\n" % TARGET,
            "git\text/%s/src\thttps://github.com/madler/zlib.git\t%s\n" % (TARGET, "8" * 40))
        text = shared()
        self.port(sources=sources, script=text)
        top = self.prov + "/port/projects/zlib"
        self.refused("^%s$" % re.escape("%s: the tree of %s (%s/sources:3) is at %s, and the tree of zlib-lib, whose "
                                        "build it takes (line %d), at %s: this reader cannot tell which the binary "
                                        "holds" % (self.script, TARGET, top, "8" * 40, line_of(text, "lib=$LIBROOT"),
                                                   COMMIT)))


class Compare(unittest.TestCase):
    """compare names each field of the record that its build record or its scans contradict, and each build whose
    scan is missing or is of another binary: C1's negative controls."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.t = Tree(render=False)
        self.tree = facts.load(self.t.root)
        self.h = self.tree.projects[HARNESS[0]].harnesses[HARNESS[1]]
        self.builds = self.h.data["builds"]
        self.prov = layout.provenance_dir(*HARNESS, self.tree.unit_layout("/".join(HARNESS)))
        self.record = {"library_commit": COMMIT, "tls_backend": "none", "enable_debug": False, "unittests": False,
                       "sanitizer": dict(SANITIZER), "harness_origin": "upstream", "architecture": "riscv64"}

    def tearDown(self):
        self.t.close()
        self._tmp.cleanup()

    def derived(self, pin=PIN):
        write_release(self.t, self.prov, pin)
        return deviation.from_recipe(self.tree, self.h)

    def scans(self, symbols, **sha):
        path = os.path.join(self._tmp.name, "twin")
        write_elf(path, symbols)
        return {b: deviation.tls_scan(path, sha.get(b.replace("-", "_"), rec["sha256"]))
                for b, rec in self.builds.items()}

    def test_a_record_its_sources_agree_with_passes(self):
        self.assertEqual(deviation.compare(self.record, self.derived(), self.scans(CURL_ONLY), self.builds), [])

    def test_enable_debug_on_with_a_record_of_false_is_refused(self):
        pin = PIN.replace("  oft_build_cmake\n", "  oft_build_cmake -DENABLE_DEBUG=ON\n")
        self.assertEqual(deviation.compare(self.record, self.derived(pin), self.scans(CURL_ONLY), self.builds),
                         ["deviation.enable_debug is false, but %s/recipe/targets/%s/pin:7 gives true"
                          % (self.prov, TARGET)])

    def test_openssl_names_with_a_record_of_none_are_refused(self):
        self.assertEqual(deviation.compare(self.record, self.derived(), self.scans(OPENSSL), self.builds),
                         ["deviation.tls_backend is none, but the scans of builds asan, asan-ubsan, plain, ubsan give "
                          "openssl (asan: SSL_new; asan-ubsan: SSL_new; plain: SSL_new; ubsan: SSL_new)"])

    def test_no_tls_names_with_a_record_of_openssl_are_refused(self):
        found = deviation.compare(dict(self.record, tls_backend="openssl"), self.derived(), self.scans(CURL_ONLY),
                                  self.builds)
        self.assertEqual(found, ["deviation.tls_backend is openssl, but the scans of builds asan, asan-ubsan, plain, "
                                 "ubsan give none"])

    def test_a_scan_of_another_binary_is_refused(self):
        found = deviation.compare(self.record, self.derived(), self.scans(CURL_ONLY, asan=OTHER), self.builds)
        self.assertEqual(found, ["deviation.tls_backend: the scan of builds.asan is of the binary with sha256 %s, but "
                                 "builds.asan.sha256 is %s: scan the twin of this build again"
                                 % (OTHER, self.builds["asan"]["sha256"])])

    def test_a_missing_scan_is_refused(self):
        scans = self.scans(CURL_ONLY)
        del scans["ubsan"]
        self.assertEqual(deviation.compare(self.record, self.derived(), scans, self.builds),
                         ["deviation.tls_backend: builds.ubsan has no scan (evidence/deviation/ubsan.tls.tsv)"])

    def test_a_withheld_build_needs_no_scan_and_its_scan_is_not_compared(self):
        """A withheld build has no sha256 (schemas/harness.yaml `build`) to hold a scan to: lint neither requires its
        scan nor compares one, and tls_backend is what the scans of the other builds give."""
        builds = dict(self.builds, asan={"file": self.builds["asan"]["file"], "withheld": "not-yet-published"})
        scans = self.scans(CURL_ONLY)
        del scans["asan"]
        self.assertEqual(deviation.compare(self.record, self.derived(), scans, builds), [])
        self.assertEqual(deviation.compare(self.record, self.derived(), self.scans(CURL_ONLY, asan=OTHER), builds), [])
        self.assertEqual(deviation.compare(self.record, self.derived(), self.scans(OPENSSL), builds),
                         ["deviation.tls_backend is none, but the scans of builds asan-ubsan, plain, ubsan give "
                          "openssl (asan-ubsan: SSL_new; plain: SSL_new; ubsan: SSL_new)"])

    def test_with_every_build_withheld_any_tls_backend_is_taken(self):
        """With every build withheld no scan gives tls_backend, so compare takes each value of the schema, whatever
        scans there are; the harness README then says that no check reads it (test_generate)."""
        builds = {b: {"file": rec["file"], "withheld": "not-yet-published"} for b, rec in self.builds.items()}
        for tls in ("none",) + deviation.LIBRARIES:
            with self.subTest(tls_backend=tls):
                record = dict(self.record, tls_backend=tls)
                self.assertEqual(deviation.compare(record, self.derived(), {}, builds), [])
                self.assertEqual(deviation.compare(record, self.derived(), self.scans(OPENSSL), builds), [])
                self.assertEqual(deviation.compare(record, self.derived(), self.scans(CURL_ONLY), builds), [])

    def test_each_other_field_that_differs_is_named(self):
        record = dict(self.record, library_commit="9" * 40, unittests=True, harness_origin="patched",
                      sanitizer=dict(SANITIZER, asan="undefined"))
        pin = "%s/recipe/targets/%s/pin" % (self.prov, TARGET)
        self.assertEqual(deviation.compare(record, self.derived(), self.scans(CURL_ONLY), self.builds), [
            "deviation.library_commit is %s, but %s:2 gives %s" % ("9" * 40, pin, COMMIT),
            "deviation.unittests is true, but %s:5-9 gives false" % pin,
            "deviation.harness_origin is patched, but %s:8 gives upstream" % pin,
            "deviation.sanitizer.asan is undefined, but %s/recipe/tools/build-body.sh:15 gives address" % self.prov])

    def test_the_scans_in_the_tree_are_loaded(self):
        paths = deviation.scan_path(self.tree, self.h)
        self.assertEqual(paths["plain"], self.prov + "/evidence/deviation/plain.tls.tsv")
        scans = self.scans(CURL_ONLY)
        deviation.write_scan(self.t.path(paths["plain"]), scans["plain"])
        self.t.write(paths["asan"], "not a scan\n")
        loaded = deviation.load_scans(self.tree, self.h)
        self.assertEqual(sorted(loaded), ["asan", "plain"])
        self.assertEqual(loaded["plain"], scans["plain"])
        self.assertEqual(loaded["asan"], paths["asan"] + ": line 1: not %r" % (deviation.HEADER % ("<sha256>",
                                                                                                    "<sha256>")))


if __name__ == "__main__":
    unittest.main()
