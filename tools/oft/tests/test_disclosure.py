"""disclosure: the canonical forms a release's files are compared in, and the needles no file it keeps may hold.

The table is the probe list of the reviews of internal #80 (the final review's findings 1-8, the deep review's 1-7 and
the code-quality review's 4) and #117 (the final review's 1-5, the deep review's 1-2), each form one row."""
import hashlib
import html
import json
import os
import subprocess
import sys
import unicodedata
import unittest
import urllib.parse

from oft import disclosure, facts, lint, yamlio
from oft.tests.helpers import HELD_PATCH, HELD_PAYLOAD, HERE, Tree, add_findings, folded, patch_copies

FINDING = "findings/zlib/checksum_fuzzer/stand-in-abort"
HEADER = b"\0" * 6
# another driver header: a config of 2 bytes, so the harness is called 1 to 4 times, and the allocation mask
FOUR_CALLS = b"\x02\x00\x03\x00\0\0\0\0"
DRAFT = "\n".join([
    "--- a/adler32.c",
    "+++ b/adler32.c",
    "@@ -60,4 +60,4 @@ uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len)",
    "     sum2 = (adler >> 16) & 0xffff;",
    "-    if (len == 1 && buf[1] != 0) { /* read one byte after the private adler32 input buffer ends */",
    "+    if (len == 1 && buf[0] != 0) { /* read the private adler32 input buffer before it ends */",
    "         adler += buf[0];",
    ""])
# a holding finding's fix of the size real fixes have: one canonical character removed and five added, inside upstream
# lines a harness may quote.  A stand-in: it describes no bug.
SHORT_FIX = "\n".join([
    "diff --git a/scan.c b/scan.c",
    "--- a/scan.c",
    "+++ b/scan.c",
    "@@ -20,7 +20,7 @@ size_t stand_in_width (const char *s, int kind)",
    "   const char *stand_in_cursor = s;",
    "   while (*stand_in_cursor != '\\0' && stand_in_cursor++)",
    "     {",
    "-      w++;",
    "+      w += kind;",
    "     }",
    "   return stand_in_finish (w, stand_in_cursor);",
    " }",
    ""])
# a reproducer of the size real ones have: 21 canonical characters, mostly punctuation
SHORT_PAYLOAD = "Y = $(addprefix ab,$(stand-in))\nzz:\n"


def five_letters(size=418, letters="kmpqw"):
    """A reproducer of size bytes whose only letters are five: no window of it has MIN_DISTINCT characters."""
    out, i = "", 0
    while len(out) < size:
        a, b, c = letters[i % 5], letters[(2 * i + 1) % 5], letters[(3 * i + 2) % 5]
        out += "%s%s:=$(%s %s,%s,$(%s%s))\n" % (a, b, c, a, b, a, b)
        i += 1
    return out[:size - 1] + "\n"


def hold(held=(), statements=None):
    return facts.Hold(held=set(held), private=set(), statements=statements or {})


class Canonical(unittest.TestCase):
    """canonical(data): every in-scope form of a text holds the canonical text of its plain UTF-8 form."""

    TEXT = ("    if (state->next -> avail < 4 && \"stand-in\" != 0)\n"
            "        return 'x';  /* Two spaces.  Then more. */\n")

    def forms(self):
        t = self.TEXT
        return {
            "UTF-8 with a byte order mark": b"\xef\xbb\xbf" + t.encode(),
            "UTF-16": t.encode("utf-16"), "UTF-16-LE": t.encode("utf-16-le"), "UTF-16-BE": t.encode("utf-16-be"),
            "UTF-32": t.encode("utf-32"), "UTF-32-LE": t.encode("utf-32-le"), "UTF-32-BE": t.encode("utf-32-be"),
            "CRLF": t.replace("\n", "\r\n").encode(), "CR CR LF": t.replace("\n", "\r\r\n").encode(),
            "tabs": t.replace("    ", "\t").encode(),
            "HTML twice": html.escape(html.escape(t)).encode(),
            "percent escapes twice": urllib.parse.quote(urllib.parse.quote(t)).encode(),
            "references in percent escapes": urllib.parse.quote(html.escape(t)).encode(),
            "numeric references": "".join("&#%d;" % ord(c) for c in t).encode(),
            "a reply quote": "".join("> " + line for line in t.splitlines(True)).encode(),
            "a C comment": "".join("// " + line for line in t.splitlines(True)).encode(),
            "a Markdown table": ("| " + t.replace("\n", " |\n| ") + " |").encode(),
            "a JSON string": json.dumps(t).encode(),
            "a YAML literal": yamlio.dump({"text": t}).encode(),
            "a C string": ('static const char fix[] = "%s";\n' % t.replace("\n", "\\n").replace('"', '\\"')).encode(),
            "a soft hyphen": t.replace("-", "&shy;").encode(),
            "a zero-width space": t.replace("avail", "av\u200bail").encode(),
            "an interior byte order mark": t.replace("return", "\ufeffreturn").encode(),
            "UTF-16 after one byte": b"#" + t.encode("utf-16-le"),
            "UTF-16 with a bad unit": t.encode("utf-16-le") + b"\x00\xd8",
            "UTF-32 after two bytes": b"##" + t.encode("utf-32-le"),
            "inside other text": b"before\0\xff" + t.encode() + b"after",
        }

    def test_each_form_holds_the_canonical_text(self):
        plain = disclosure.canonical(self.TEXT.encode())
        self.assertGreater(len(plain), disclosure.WINDOW)
        for how, data in self.forms().items():
            with self.subTest(how=how):
                self.assertIn(plain, disclosure.canonical(data))

    def test_other_text_does_not(self):
        plain = disclosure.canonical(self.TEXT.encode())
        for other in (self.TEXT.replace("avail", "bytes"), self.TEXT.replace("'x'", "'y'")):
            self.assertNotIn(plain, disclosure.canonical(other.encode()))

    def test_text_that_decodes_to_no_character_is_read(self):
        """A reference to no character, a bad percent escape or a bad UTF-8 byte reads as text, and does not fail."""
        self.assertIn("a", disclosure.canonical(b"A: &#x110000; &#99999999999999999999; %zz %4 \xff\n"))

    def test_a_control_character_escape_reads_as_the_character(self):
        """`\\f`, `\\v` and `\\b` (C, JSON) and YAML's `\\N`, `\\L` and `\\P` are control and line characters, not the
        letters (internal #80's deep review at 0ac7eb3f05, non-blocking finding 1)."""
        text = "alpha\x0cbeta\x0bgamma\x08delta\x85epsilon\u2028zeta\u2029eta"
        plain = disclosure.canonical(text.encode())
        for how, data in (("C escapes", "alpha\\fbeta\\vgamma\\bdelta\\Nepsilon\\Lzeta\\Peta"),
                          ("json.dumps", json.dumps(text)), ("yamlio", yamlio.dump(text))):
            with self.subTest(how=how):
                self.assertEqual(disclosure.canonical(data.encode()), plain)

    def test_a_numeric_reference_of_more_than_seven_digits_stays_as_it_is(self):
        """No code point has more than 7 decimal digits: a longer reference is text, and no int() reads it (Python
        refuses an int of over 4,300 digits)."""
        self.assertEqual(disclosure.canonical(b"&#12345678;"), "12345678")
        self.assertEqual(disclosure.canonical(b"&#x000000041;"), "a")

    def test_nested_escapes_of_a_long_reference_decode_to_a_bounded_fixed_point(self):
        """internal #80's gates at 0ac7eb3f05: `&#38;#` and 5,000 digits made a reference html.unescape could not read.
        Every nesting of the escapes of `&` decodes without an exception, and the digits stay text."""
        digits = "9" * 5000
        escapes = ("&#38;", "&#x26;", "&amp;", "%26", "\\x26", "\\u0026", "&#0038;")
        cases = ["&#" + digits + ";", "&#38;#" + digits + ";", "&#38;#38;#38;#" + digits]
        for a in escapes:
            for b in escapes:
                for c in escapes:
                    cases.append(("&#" + digits).replace("&", a, 1).replace("&", b, 1).replace("&", c, 1))
        deep = "&#" + digits + ";"
        for _ in range(disclosure.DECODE_ROUNDS + 4):
            deep = deep.replace("&", "&#38;", 1)
            cases.append(deep)
        for text in cases:
            with self.subTest(text=text[:40]):
                try:
                    got = disclosure.canonical(text.encode())
                except Exception as e:      # noqa: BLE001 - any exception is the defect
                    self.fail("%s: %r" % (text[:40], e))
                self.assertIn(digits, got)


class Finds:
    """found and assertFound over cls.needles."""

    def found(self, data, rel="docs/notes.md"):
        return disclosure.found(rel, data if isinstance(data, bytes) else data.encode(), self.needles)

    def assertFound(self, data, label, rel="docs/notes.md"):
        got = self.found(data, rel)
        if label.startswith("hunk "):
            number, patch = label.split(" of ", 1)
            want = "lines of %s of %s" % (number, patch)
            self.assertTrue(any(want in hit for hit in got), (want, got))
        else:
            self.assertTrue(any(g.startswith(label) for g in got), (label, got))


class WholeHold(Finds, unittest.TestCase):
    """The needles of zlib held whole by its reported finding, whose directory also holds a draft fix no field names."""

    @classmethod
    def setUpClass(cls):
        cls.t = Tree()
        add_findings(cls.t)
        y = cls.t.yaml(FINDING + "/finding.yaml")
        y.update(state="reported", upstream="https://bugs.example.org/1")
        cls.t.put_yaml(FINDING + "/finding.yaml", y)
        cls.summary = y["summary"]
        cls.t.write(FINDING + "/0001-stand-in.patch", HELD_PATCH)
        cls.t.write(FINDING + "/0002-draft.patch", DRAFT)
        cls.t.write(FINDING + "/input.bin", HEADER + HELD_PAYLOAD.encode(), mode="wb")
        cls.needles = disclosure.needles(facts.load(cls.t.root), hold(held={"zlib"}))

    @classmethod
    def tearDownClass(cls):
        cls.t.close()

    def test_every_form_of_a_copy_of_the_patch_holds_each_hunk(self):
        for how, data in patch_copies(HELD_PATCH).items():
            with self.subTest(how=how):
                for k in (1, 2):
                    self.assertFound(data, "hunk %d of %s/0001-stand-in.patch" % (k, FINDING))

    def test_a_draft_patch_no_field_names_is_a_needle(self):
        self.assertFound("Draft:\n\n" + "".join("    " + line for line in DRAFT.splitlines(True)),
                         "hunk 1 of %s/0002-draft.patch" % FINDING)
        self.assertFound("see 0002-draft.patch\n", "0002-draft.patch, a patch file name of finding " + FINDING)

    def test_the_summary_as_people_copy_it(self):
        for how, text in (("as finding.yaml folds it", "summary: >-\n" + folded(self.summary, 40, "  ")),
                          ("wrapped again", folded(self.summary, 72)),
                          ("two spaces after a full stop", self.summary.replace(". ", ".  ")),
                          ("in upper case", self.summary.upper())):
            with self.subTest(how=how):
                self.assertFound(text, "the summary of finding " + FINDING)
        self.assertFound(folded(self.summary, 30).replace("\n", "\r\n").encode("utf-16"),
                         "the summary of finding " + FINDING)

    def test_the_input_payload_without_its_header(self):
        label = "the payload of %s/input.bin" % FINDING
        for how, data in (("in a fenced block", ("```\n%s```\n" % HELD_PAYLOAD).encode()),
                          ("indented", "".join("    " + line for line in HELD_PAYLOAD.splitlines(True)).encode()),
                          ("under another header", FOUR_CALLS + HELD_PAYLOAD.encode()),
                          ("in <pre> with references", ("<pre>%s</pre>" % html.escape(HELD_PAYLOAD)).encode())):
            with self.subTest(how=how):
                self.assertFound(data, label)

    def test_the_bytes_of_the_evidence_its_digest_and_its_hex(self):
        with open(self.t.path(FINDING, "control.bin"), "rb") as f:
            control = f.read()
        self.assertFound(b"\x7fELF" + control + b"\0", "the bytes of %s/control.bin" % FINDING, rel="docs/c.bin")
        sha = hashlib.sha256(control).hexdigest()
        self.assertFound("input %s\n" % sha.upper(), "%s, the SHA-256 of %s/control.bin" % (sha, FINDING))
        with open(self.t.path(FINDING, "input.bin"), "rb") as f:
            payload = f.read()
        self.assertFound("input_hex: '%s'\n" % payload.hex(), "the hex of %s/input.bin" % FINDING,
                         rel="docs/witness.yaml")

    def test_an_invisible_character_inside_a_name_or_a_copy(self):
        """A soft hyphen or a zero-width space is what a word processor and a rendered page write; a reader sees
        neither."""
        self.assertFound("see stand&shy;in-abort\n", "stand-in-abort, the slug of finding " + FINDING)
        self.assertFound("see zlib/checksum\u200b_fuzzer\n", "zlib/checksum_fuzzer, a fuzz target of held project zlib")
        summary = self.t.yaml(FINDING + "/finding.yaml")["summary"]
        self.assertFound(summary.replace("stand", "st\u200band"), "the summary of finding " + FINDING)

    def test_a_hex_dump_of_the_evidence(self):
        """`xxd -p` wraps the hex at 60 characters, and `xxd` writes two-byte groups: a reader reads either as the
        reproducer's bytes."""
        with open(self.t.path(FINDING, "input.bin"), "rb") as f:
            data = f.read()
        hx = data.hex()
        label = "the hex of %s/input.bin" % FINDING
        for how, text in (("one line", hx), ("xxd -p", folded(" ".join(hx[i:i + 2] for i in range(0, len(hx), 2)), 59)),
                          ("two-byte groups", " ".join(hx[i:i + 4] for i in range(0, len(hx), 4))),
                          ("upper case", hx.upper())):
            with self.subTest(how=how):
                self.assertFound(text, label)

    def test_a_digest_broken_over_two_lines(self):
        digest = self.t.yaml(FINDING + "/finding.yaml")["input"]["plain"]["stdout_sha256"]
        self.assertFound("stdout: %s\n  %s\n" % (digest[:30], digest[30:]),
                         "%s, a digest finding %s records" % (digest, FINDING))

    def test_an_input_digest_broken_over_two_lines(self):
        """An input's SHA-256 is built as a recorded digest is, so it counts in the same forms (internal #80's
        code-quality review at 0ac7eb3f05, finding 5)."""
        with open(self.t.path(FINDING, "input.bin"), "rb") as f:
            sha = hashlib.sha256(f.read()).hexdigest()
        self.assertFound("sha256: %s\n  %s\n" % (sha[:30], sha[30:]),
                         "%s, the SHA-256 of %s/input.bin" % (sha, FINDING))

    def test_a_name_a_copy_breaks_over_lines_or_spaces_out(self):
        """A reader reads a path or a name through a line break, and through a blank beside a `/`."""
        label = "stand-in-abort, the slug of finding " + FINDING
        for text in ("the stand-\nin-abort bug",):
            with self.subTest(text=text):
                self.assertFound(text, label)
        target = "zlib/checksum_fuzzer, a fuzz target of held project zlib"
        for text in ("see zlib/\nchecksum_fuzzer\n", "see zlib\n/checksum_fuzzer\n", "see zlib / checksum_fuzzer\n"):
            with self.subTest(text=text):
                self.assertFound(text, target)

    def test_blank_padding_is_unwrapped_in_linear_time(self):
        """internal #80's final review at e940441ae6, finding 6: the unwrap pass reads each blank once."""
        import time
        times = []
        for size in (1 << 14, 1 << 16):
            started = time.perf_counter()
            disclosure.found("docs/pad.txt", (" " * size).encode("utf-16-le"), self.needles)
            times.append(time.perf_counter() - started)
        # four times the text must cost much less than sixteen times the time, as a quadratic pass would
        self.assertLess(times[1], 10 * max(times[0], 0.01), times)

    def test_part_of_a_hunk_matches(self):
        """The changed lines alone, one side alone, a reversed diff and a -U0 diff each share a window with a hunk."""
        removed = ("-    if (state->next -> avail < 4 && \"stand-in\" != 0)"
                   " /* reject only the unavailable stand-in checksum bytes */\n")
        added = ("+    if (state->next -> avail <= 4 && \"stand-in\" != 0)"
                 " /* reject each unavailable stand-in checksum byte */\n")
        for how, text in (("changed lines only", removed + added), ("removed side", removed), ("added side", added),
                          ("reversed", added.replace("+", "-", 1) + removed.replace("-", "+", 1)),
                          ("-U0", "@@ -142 +142 @@\n" + removed + added)):
            with self.subTest(how=how):
                self.assertFound(text, "hunk 2 of %s/0001-stand-in.patch" % FINDING)

    def test_upstream_context_alone_is_no_evidence(self):
        """A harness that quotes the upstream lines around the fix quotes what every copy of the library holds."""
        context = ("     register z_crc_t c;\n     register const z_crc_t *buf4;\n"
                   "         c = crc_table[0][(c ^ *buf++) & 0xff] ^ (c >> 8);\n         len--;\n")
        self.assertEqual(self.found(context), set())

    def test_one_sentence_of_the_summary_matches(self):
        for sentence in self.summary.split(". "):
            if len(disclosure.canonical(sentence.encode())) >= disclosure.WINDOW:
                with self.subTest(sentence=sentence):
                    self.assertFound(sentence, "the summary of finding " + FINDING)

    def test_the_commit_message_of_a_patch_matches(self):
        """A release note pasted from the format-patch envelope describes the fix."""
        self.assertFound("## Fixed\n\n- crc32: read the byte the loop stops at, not the one past it\n",
                         "the subject of %s/0001-stand-in.patch" % FINDING)
        self.assertFound("A stand-in commit message for these tests; it describes no bug in zlib.\n",
                         "the commit message of %s/0001-stand-in.patch" % FINDING)

    def test_the_outcome_vocabulary_alone_is_no_evidence(self):
        """Every counterexample note says which builds abort and which exit 0.  A window made only of those words
        (a public note and a held summary may both say 'the plain and ubsan builds exit 0, the control') is no
        evidence; a window with one word of the finding's own still is."""
        summary = ("stand_in_scan reads one byte past its buffer: the asan and asan-ubsan builds abort, the plain and "
                   "ubsan builds exit 0, the control exits 0 on every build.")
        with Tree() as t:
            add_findings(t)
            y = t.yaml(FINDING + "/finding.yaml")
            y["summary"] = summary
            t.put_yaml(FINDING + "/finding.yaml", y)
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        note = "note: The asan build aborts, the plain and ubsan builds exit 0, the control exits 0 on every build.\n"
        self.assertEqual(disclosure.found("counterexamples/a/b/c/expect.yaml", note.encode(), needles), set())
        self.assertNotIn("aborttheplainandubsanbuildsexit0", needles.windows)
        self.assertIn("the summary of finding " + FINDING,
                      disclosure.found("docs/n.md", b"past its buffer: the asan and asan-ubsan builds abort", needles))

    def test_a_copy_at_every_offset_of_the_probe_stride_is_found(self):
        """The index is probed every few positions; a copy of exactly one window is still found wherever it starts."""
        window = disclosure.canonical(HELD_PAYLOAD.encode())[:disclosure.WINDOW]
        self.assertIn(window, self.needles.windows)
        for offset in range(17):
            with self.subTest(offset=offset):
                text = ("q" * offset + window + "q" * 40).encode()
                self.assertIn("the payload of %s/input.bin" % FINDING, self.found(text))

    def test_low_complexity_windows_are_no_evidence(self):
        """A run of one repeated character is chance text; a real code window has MIN_DISTINCT characters."""
        self.assertEqual(disclosure._windows("=" + "y" * 40000, "repeat"), {})
        windows = disclosure._windows("if (private_crc32_buffer_ends_here) return the released byte;", "code")
        self.assertTrue(windows)
        self.assertTrue(all(len(set(w)) >= disclosure.MIN_DISTINCT for w in windows))

    def test_the_forms_of_normal_work_match(self):
        """`//` comments, this repository's YAML writer (which doubles `'`), json.dumps of non-ASCII text, and a
        Markdown-escaped copy."""
        sentence = "The stand-in’s crc32 loop reads é past the input buffer’s end — said the stand-in report."
        with Tree() as t:
            add_findings(t)
            y = t.yaml(FINDING + "/finding.yaml")
            y["summary"] = sentence
            t.put_yaml(FINDING + "/finding.yaml", y)
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        label = "the summary of finding " + FINDING
        for how, text in (("// comments", "".join("// " + line for line in folded(sentence, 30).splitlines(True))),
                          ("yamlio single quotes", yamlio.dump({"note": "it: " + sentence.replace("’", "'")})),
                          ("json.dumps", json.dumps({"summary": sentence})),
                          ("Markdown escapes", sentence.replace("-", "\\-").replace(".", "\\."))):
            with self.subTest(how=how):
                got = disclosure.found("docs/notes.md", text.encode(), needles)
                self.assertIn(label, got, text)

    def test_a_binary_input_has_byte_digest_and_hex_needles(self):
        """A minimised reproducer of a binary format has no printable run of PAYLOAD_MIN characters; its bytes, its
        digest and the windows of its hex still count (internal #80's bug-finder at e940441ae6, finding 3), and so do
        its bytes as Python's repr, a C string of `\\x` escapes and `xxd -i` spell them (its gates at 0ac7eb3f05)."""
        payload = b"".join(bytes([0x80 + i % 64, 0x41 + i % 26, 0x00]) for i in range(100))
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER + payload, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        data = HEADER + payload
        rel = FINDING + "/input.bin"
        self.assertIn("the bytes of " + rel, disclosure.found("tests/data/crash-0001", data, needles))
        sha = hashlib.sha256(data).hexdigest()
        self.assertIn("%s, the SHA-256 of %s" % (sha, rel), disclosure.found("docs/n.md", sha.encode(), needles))
        dump = folded(" ".join(data.hex()[i:i + 4] for i in range(0, len(data.hex()), 4)), 60)
        self.assertIn("the hex of " + rel, disclosure.found("docs/n.md", dump.encode(), needles))

        def escaped(b):
            return "".join("\\x%02x" % c for c in b)
        rows = [data[i:i + 12] for i in range(0, len(data), 12)]
        for how, text in (
                ("Python's repr", "DATA = %r\n" % data),
                ("Python's repr of the payload alone", "def test_crash():\n    run(%r)\n" % payload),
                ("a C string of \\x escapes", 'static const char data[] = "%s";\n' % escaped(data)),
                ("C strings of \\x escapes, line by line",
                 "static const char data[] =\n" + "".join('    "%s"\n' % escaped(r) for r in rows) + ";\n"),
                ("xxd -i", "unsigned char input_bin[] = {\n" + ",\n".join(
                    "  " + ", ".join("0x%02x" % c for c in r) for r in rows)
                 + "\n};\nunsigned int input_bin_len = %d;\n" % len(data))):
            with self.subTest(how=how):
                self.assertIn("the bytes of " + rel, disclosure.found("tests/test_crash.c", text.encode(), needles))

    def test_a_huge_numeric_reference_reads_as_text(self):
        """A decimal reference of thousands of digits, and one a decoding round makes from `&#38;#`, are text in a
        kept file: the search reads them, and nothing held is in them."""
        for data in (HEADER + b"&#" + b"9" * 4400 + b";", b"&#38;#" + b"9" * 4400 + b";"):
            with self.subTest(data=data[:12]):
                self.assertEqual(disclosure.found("counterexamples/a/b/c/input.bin", data, self.needles), set())

    def test_the_needle_is_decoded_as_the_text_is(self):
        """A hunk with `%20s` and `&amp;` in its C code: a verbatim copy decodes them, so the needle must too."""
        patch = ("--- a/fmt.c\n+++ b/fmt.c\n@@ -1 +1 @@\n"
                 "-    printf(\"%08x %20s &amp; the stand-in private format width\\n\", value, name);\n"
                 "+    printf(\"%08x %-20s &amp; the stand-in private format width\\n\", value, name);\n")
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/0003-fmt.patch", patch)
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        got = disclosure.found("docs/fmt.md", patch.split("@@\n", 1)[1].encode(), needles)
        self.assertIn("removed lines of hunk 1 of %s/0003-fmt.patch" % FINDING, got)

    def test_the_slug_in_each_form(self):
        label = "stand-in-abort, the slug of finding " + FINDING
        for text in ("Fixed %53tand-in-abort.", "Fixed &#83;tand-in-abort.", "stand&hyphen;in&hyphen;abort",
                     "stand%26%2345%3Bin-abort", "stand&amp;#45;in&amp;#45;abort", "STAND-IN-ABORT",
                     "stand\u2011in\u2013abort", "见stand-in-abort中", "(stand-in-abort)"):
            with self.subTest(text=text):
                self.assertFound(text, label)
        self.assertFound(b"", label, rel="docs/stand-in-abort.md")

    def test_a_held_fuzz_target_in_each_form(self):
        target = "zlib/checksum_fuzzer, a fuzz target of held project zlib"
        module = "OssFuzzTheorems.zlib.checksum_fuzzer, the Rocq module of held fuzz target zlib/checksum_fuzzer"
        for text, label in (("see zlib/checksum_fuzzer\n", target), ("see zlib/./checksum_fuzzer\n", target),
                            ("see zlib//checksum_fuzzer\n", target), ("zlib%2Fchecksum_fuzzer", target),
                            ("zlib/checksum-fuzzer", target),
                            ("Require OssFuzzTheorems.zlib.checksum_fuzzer.Statements.", module),
                            ("From OssFuzzTheorems Require zlib.checksum_fuzzer.Statements.", module),
                            ("see zlib/api-driver", "zlib/api-driver, a fuzz target of held project zlib"),
                            ("see zlib/minigzip_fuzzer", "zlib/minigzip_fuzzer, a fuzz target of held project zlib")):
            with self.subTest(text=text):
                self.assertFound(text, label)

    def test_a_name_inside_a_longer_name_is_no_mention(self):
        """A needle that is a name counts only at a name boundary: a prefix of another name never matches."""
        for text in ("see zlib/checksum_fuzzer_v2", "Require OssFuzzTheorems.zlib.checksum_fuzzer_v2.Statements.",
                     "the stand-in-abort-repro case", "0001-stand-in.patch-v2", "xzlib/checksum_fuzzer"):
            with self.subTest(text=text):
                self.assertEqual(self.found(text), set())

    def test_a_source_file_named_after_a_fuzz_target_is_no_mention(self):
        """A path name followed by a source or header suffix is a file's name: a header, or the harness source a
        build record cites (main's recipe records cite four real projects' harness sources so; one real harness
        includes <openssl/x509.h>, and openssl has a fuzz target x509).  Any other suffix names the fuzz target: the
        repository writes `analyses/known-issues.md` and `toolchain/allowed-axioms.txt` for its own paths."""
        for text in ("#include <zlib/checksum_fuzzer.h>", "#include \"zlib/checksum_fuzzer.hpp\"",
                     "github.com/google/oss-fuzz.git@955c6866:projects/zlib/checksum_fuzzer.c (git blob 80ba8c3e)"):
            with self.subTest(text=text):
                self.assertEqual(self.found(text), set())
        target = "zlib/checksum_fuzzer, a fuzz target of held project zlib"
        for text in ("a bug in zlib/checksum_fuzzer.\n", "the page is zlib/checksum_fuzzer.md\n",
                     "see zlib/checksum_fuzzer.html\n", "see zlib/checksum_fuzzer.yaml\n"):
            with self.subTest(text=text):
                self.assertFound(text, target)

    def test_short_text_is_no_window(self):
        """A payload run shorter than PAYLOAD_MIN is no needle, whole or in windows: the fixture's control is 7."""
        self.assertFalse(any("the payload of %s/control.bin" % FINDING in label
                             for labels in self.needles.windows.values() for label in labels))
        self.assertEqual(self.found("```\ncontrol\n```\n"), set())

    def test_an_input_with_no_payload_is_no_needle(self):
        """A driver header with no payload is in every counterexample input and says nothing about the bug."""
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
            self.assertEqual([n.label for n in needles.exact if "input.bin" in n.label], [])
            self.assertEqual([label for labels in needles.windows.values() for label in labels
                              if "input.bin" in label], [])
            self.assertEqual(disclosure.found("counterexamples/a/b/c/input.bin", HEADER + b"x", needles), set())


class ShortEvidence(Finds, unittest.TestCase):
    """Evidence shorter than a window counts whole (internal #80's gates at 0ac7eb3f05): a fix of the size real ones
    have, a reproducer of 21 canonical characters, and one of 418 bytes whose only letters are five."""

    @classmethod
    def setUpClass(cls):
        cls.t = Tree()
        add_findings(cls.t)
        cls.t.write(FINDING + "/0002-width.patch", SHORT_FIX)
        cls.t.write(FINDING + "/input.bin", HEADER + SHORT_PAYLOAD.encode(), mode="wb")
        cls.t.write(FINDING + "/control.bin", HEADER + five_letters().encode(), mode="wb")
        cls.needles = disclosure.needles(facts.load(cls.t.root), hold(held={"zlib"}))

    @classmethod
    def tearDownClass(cls):
        cls.t.close()

    def test_a_short_fix_counts_whole_and_by_its_new_side(self):
        """One character removed and five added: a copy of the whole hunk, a reply quote of it and the patched code
        each count; the upstream lines around the fix do not."""
        hunk = SHORT_FIX[SHORT_FIX.index("@@"):]
        body = hunk.splitlines()[1:]
        patched = "".join(line[1:] + "\n" for line in body if not line.startswith("-"))
        upstream = "".join(line[1:] + "\n" for line in body if not line.startswith("+"))
        label = "hunk 1 of %s/0002-width.patch" % FINDING
        for how, text in (("a diff block", "```diff\n%s```\n" % hunk),
                          ("a reply quote", "".join("> " + line for line in hunk.splitlines(True))),
                          ("the patched code, indented", "".join("    " + line for line in patched.splitlines(True))),
                          ("the patched code in // comments",
                           "".join("// " + line for line in patched.splitlines(True)))):
            with self.subTest(how=how):
                self.assertFound(text, label)
        self.assertEqual(self.found("```c\n%s```\n" % upstream), set())

    def test_a_short_reproducer_counts_whole(self):
        """A reproducer of 21 canonical characters, mostly punctuation, as people and tools copy it."""
        label = "the payload of %s/input.bin" % FINDING
        p = SHORT_PAYLOAD
        for how, text in (("a fenced block", "```make\n%s```\n" % p),
                          ("a reply quote", "".join("> " + line for line in p.splitlines(True))),
                          ("json.dumps", json.dumps({"input": p})),
                          ("yamlio", yamlio.dump({"input": p})),
                          ("a C string", 'const char *repro = "%s";\n' % p.replace("\n", "\\n")),
                          ("C strings, line by line",
                           "static const char repro[] =\n" + "".join('    "%s\\n"\n' % line for line in p.splitlines())
                           + ";\n"),
                          ("a shell here-string", "make -f - <<< '%s'\n" % p)):
            with self.subTest(how=how):
                self.assertFound(text, label)

    def test_a_long_reproducer_of_five_letters_counts_whole(self):
        """418 bytes whose only letters are five: no window has MIN_DISTINCT characters, so the whole reproducer
        counts, in a fenced block, a reply quote and a YAML file."""
        p = five_letters()
        self.assertEqual(len(p), 418)
        self.assertFalse(any("the payload of %s/control.bin" % FINDING in label
                             for labels in self.needles.windows.values() for label in labels))
        label = "the payload of %s/control.bin" % FINDING
        for how, text in (("a fenced block", "```make\n%s```\n" % p),
                          ("a reply quote", "".join("> " + line for line in p.splitlines(True))),
                          ("yamlio", yamlio.dump({"input": p}))):
            with self.subTest(how=how):
                self.assertFound(text, label)


# a binary reproducer that holds every byte value, a NUL before digits (YAML writes `\0` and then `12`, which C and
# Python read as the one octal escape `\012`), and the bytes C or YAML give an escape of their own (BEL, ESC, NBSP)
BINARY = bytes(range(256)) + b"\x0012\x07\x1b\xa0" * 4 + bytes(range(255, -1, -1))
# a fix whose lines go on after a backslash, as a C macro's do; its added text is shorter than a window.  A stand-in
CONTINUED_FIX = "\n".join([
    "diff --git a/macro.h b/macro.h",
    "--- a/macro.h",
    "+++ b/macro.h",
    "@@ -10,3 +10,3 @@",
    " #define STAND_IN_STEP(p, n) \\",
    "-  do { (p) += (n); \\",
    "+  do { (p) += (n) - 1; \\",
    "   } while (0)",
    ""])

# a fix whose added line holds `(*t` inside it, which a mark would take where a rewrap or a fold starts a line there
DEREF_FIX = "\n".join([
    "--- a/scan.c",
    "+++ b/scan.c",
    "@@ -30 +30 @@",
    "-  while (stand_in_pointer_ok && *t != 0)",
    "+  while (stand_in_pointer_ok && (*t != '\\0'))",
    ""])


def xxd(data):
    """data as `xxd` prints it: the offset, eight groups of two bytes, two blanks and the text column."""
    lines = []
    for i in range(0, len(data), 16):
        row = data[i:i + 16]
        groups = " ".join(row[j:j + 2].hex() for j in range(0, len(row), 2))
        lines.append("%08x: %-39s  %s\n" % (i, groups, "".join(chr(c) if 32 <= c < 127 else "." for c in row)))
    return "".join(lines)


def octal_minimal(data):
    """data as a C string of octal escapes in their shortest form, as strace and gdb write them: three digits only
    before a digit."""
    out = []
    for i, c in enumerate(data):
        if 32 <= c < 127 and c not in b'"\\':
            out.append(chr(c))
        else:
            out.append(("\\%03o" if i + 1 < len(data) and 48 <= data[i + 1] <= 57 else "\\%o") % c)
    return '"%s"' % "".join(out)


def yaml_escaped(data):
    """data as a YAML double-quoted scalar, with YAML's own escapes (`\\0`, `\\a`, `\\e`, `\\_`) and `\\xNN` for every
    other byte that is not printable ASCII."""
    own = {0: "\\0", 7: "\\a", 8: "\\b", 9: "\\t", 10: "\\n", 11: "\\v", 12: "\\f", 13: "\\r", 27: "\\e", 34: '\\"',
           92: "\\\\", 0xa0: "\\_"}
    return '"%s"' % "".join(own.get(c) or (chr(c) if 32 <= c < 127 else "\\x%02X" % c) for c in data)


class ClosedList(Finds, unittest.TestCase):
    """The closed list of what the check catches (disclosure's docstring, tools/oft/README.md), one test for each item.
    It was frozen on 2026-10-26; a copy in any other form is out of scope."""

    INPUT = "the bytes of %s/input.bin" % FINDING
    CONTROL = "the bytes of %s/control.bin" % FINDING
    PAYLOAD = "the payload of %s/control.bin" % FINDING
    MACRO = "hunk 1 of %s/0002-macro.patch" % FINDING
    ADDED = "added lines of hunk 1 of %s/0002-macro.patch" % FINDING
    DEREF = "added lines of hunk 1 of %s/0003-deref.patch" % FINDING
    SUMMARY = "the summary of finding " + FINDING

    @classmethod
    def setUpClass(cls):
        cls.t = Tree()
        add_findings(cls.t)
        y = cls.t.yaml(FINDING + "/finding.yaml")
        y.update(state="reported", upstream="https://bugs.example.org/1")
        cls.t.put_yaml(FINDING + "/finding.yaml", y)
        cls.summary = y["summary"]
        cls.data, cls.control = HEADER + BINARY, HEADER + SHORT_PAYLOAD.encode()
        cls.t.write(FINDING + "/0001-stand-in.patch", HELD_PATCH)
        cls.t.write(FINDING + "/0002-macro.patch", CONTINUED_FIX)
        cls.t.write(FINDING + "/0003-deref.patch", DEREF_FIX)
        cls.t.write(FINDING + "/input.bin", cls.data, mode="wb")
        cls.t.write(FINDING + "/control.bin", cls.control, mode="wb")
        cls.needles = disclosure.needles(facts.load(cls.t.root), hold(held={"zlib"}))

    @classmethod
    def tearDownClass(cls):
        cls.t.close()

    def assertEach(self, cases):
        for how, data, label in cases:
            with self.subTest(how=how):
                self.assertFound(data, label)

    @staticmethod
    def macro():
        """(CONTINUED_FIX's hunk from its @@ line, its patched code)."""
        hunk = CONTINUED_FIX[CONTINUED_FIX.index("@@"):]
        return hunk, "".join(line[1:] + "\n" for line in hunk.splitlines()[1:] if not line.startswith("-"))

    def test_1_whole_a_long_part_or_a_whole_short_unit(self):
        hunk, patched = self.macro()
        part = disclosure.canonical(self.summary.encode())[4:4 + disclosure.WINDOW]
        self.assertEach([("the whole patch", HELD_PATCH, "the bytes of %s/0001-stand-in.patch" % FINDING),
                         ("a window of the summary", "see %s here\n" % part, self.SUMMARY),
                         ("a hunk whose lines go on after a backslash", "```diff\n%s```\n" % hunk, self.MACRO),
                         ("its patched code", patched, self.ADDED),
                         ("a short reproducer", "```make\n%s```\n" % SHORT_PAYLOAD, self.PAYLOAD)])

    def test_2_with_changes_of_white_space_line_endings_case_or_unicode_normal_form(self):
        hunk, _ = self.macro()
        wide = "".join(chr(ord(c) + 0xfee0) if "!" <= c <= "~" else c for c in self.summary)
        self.assertEach([("rewrapped and indented", folded(self.summary, 30, "    "), self.SUMMARY),
                         ("CRLF", hunk.replace("\n", "\r\n"), self.MACRO),
                         ("tabs for blanks", SHORT_PAYLOAD.replace(" ", "\t"), self.PAYLOAD),
                         ("upper case", SHORT_PAYLOAD.upper(), self.PAYLOAD),
                         ("full-width characters", wide, self.SUMMARY),
                         ("NFKD", unicodedata.normalize("NFKD", self.summary), self.SUMMARY),
                         ("a line rewrapped before a `(*`", "  while (stand_in_pointer_ok &&\n  (*t != '\\0'))\n",
                          self.DEREF)])

    def test_3_in_utf_8_utf_16_or_utf_32(self):
        hunk, _ = self.macro()
        self.assertEach([("%s: %s" % (enc, label), text.encode(enc), label)
                         for enc in ("utf-8", "utf-16", "utf-16-le", "utf-16-be", "utf-32", "utf-32-le", "utf-32-be")
                         for text, label in ((self.summary, self.SUMMARY), (hunk, self.MACRO),
                                             ("DATA = %r\n" % self.data, self.INPUT))])

    def test_4_through_references_percent_escapes_and_backslash_escapes(self):
        d = self.data
        self.assertEach([
            ("HTML decimal references", "".join("&#%d;" % c for c in d), self.INPUT),
            ("HTML hex references", "".join("&#x%x;" % c for c in d), self.INPUT),
            ("percent escapes, which keep their bytes", urllib.parse.quote_from_bytes(d), self.INPUT),
            ("Python's repr", "data = %r\n" % d, self.INPUT),
            ("json.dumps", json.dumps({"input": d.decode("latin-1")}), self.INPUT),
            ("a C string of \\x escapes", '"%s"' % "".join("\\x%02x" % c for c in d), self.INPUT),
            ("a C string of octal escapes", '"%s"' % "".join("\\%03o" % c for c in d), self.INPUT),
            ("octal escapes as strace and gdb write them", octal_minimal(d), self.INPUT),
            ("YAML's \\0, \\a, \\e and \\_", "input: %s\n" % yaml_escaped(d), self.INPUT),
            ("this repository's YAML writer, which folds the string", yamlio.dump({"input": d.decode("latin-1")}),
             self.INPUT),
            ("a text reproducer, octal escapes", 'const char *r = "%s";\n' % SHORT_PAYLOAD.replace("\n", "\\012"),
             self.PAYLOAD),
            ("a text reproducer, references", "".join("&#%d;" % ord(c) for c in SHORT_PAYLOAD), self.PAYLOAD),
            ("a text reproducer, percent escapes", urllib.parse.quote(SHORT_PAYLOAD), self.PAYLOAD)])

    def test_4_every_window_through_the_escapes_that_differ(self):
        """An input each of whose byte windows holds a NUL before digits, a BEL, an ESC and the byte 0xa0, which is no
        UTF-8 alone: only the octal reading, YAML's reading of `\\0` (and `\\a`, `\\e`, `\\_`), its folded strings, and
        percent escapes read one byte each find it."""
        payload = b"\x0012\x07\x1bab\xa0cd" * 40
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER + payload, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        d = HEADER + payload
        for how, text in (("YAML's \\0, \\a, \\e and \\_", "input: %s\n" % yaml_escaped(d)),
                          ("this repository's YAML writer", yamlio.dump({"input": d.decode("latin-1")})),
                          ("percent escapes", urllib.parse.quote_from_bytes(d)),
                          ("octal escapes as strace and gdb write them", octal_minimal(d)),
                          ("a C string of octal escapes", '"%s"' % "".join("\\%03o" % c for c in d))):
            with self.subTest(how=how):
                self.assertIn(self.INPUT, disclosure.found("docs/notes.md", text.encode(), needles))

    def test_4_a_string_this_repositorys_yaml_writer_folds_is_read_joined(self):
        """yamlio.dump folds a long double-quoted string with a backslash at the line's end and blanks before the next
        line, which YAML deletes; here no line holds a byte window, so only the joined reading finds the input."""
        payload = bytes(range(0x80, 0x9e))
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER + payload, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        text = yamlio.dump({"evidence": {"input": (HEADER + payload).decode("latin-1")}})
        self.assertIn("\\\n", text)
        self.assertIn(self.INPUT, disclosure.found("docs/notes.yaml", text.encode(), needles))

    def test_4_a_string_this_repositorys_yaml_writer_folds_before_a_mark_counts(self):
        """internal #80's final review at 85988e9f79, finding B2: yamlio.dump folds a string at a blank, and the next
        line begins `\\ (*t`, which the punctuation form reads as a Rocq comment's mark; the plain form reads it."""
        added = "  while (stand_in_pointer_ok && (*t != '\\0'))"
        s = added.replace("\\", "\\\\").replace('"', '\\"')
        i = s.index(" (*t")
        self.assertFound('fix: "%s\\\n    \\%s"\n' % (s[:i], s[i:]), self.DEREF, rel="docs/fix.yaml")

    def test_4_an_input_whose_bytes_a_decoder_reads_counts(self):
        """internal #80's final review at 85988e9f79, finding B3: each decoder alone reads a copy, so none reads the
        bytes another wrote (an input's `\\`, `&lt;`, `%41`, `0x41`, or a quote, a line break and a quote); and a Python
        string continued after a backslash (its deep review, finding 4).  The input is shorter than a byte window, so
        only its exact bytes count."""
        payload = b'a\\b&lt;c%41d"\n"e0x41f'
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER + payload, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        d = HEADER + payload
        self.assertLess(len(d), disclosure.WINDOW)

        def escaped(b):
            return "".join("\\x%02x" % c for c in b)
        for how, text in (("HTML references", "".join("&#%d;" % c for c in d)),
                          ("percent escapes", urllib.parse.quote_from_bytes(d)),
                          ("Python's repr", "x = %r\n" % d),
                          ("json.dumps", json.dumps({"input": d.decode("latin-1")})),
                          ("a C string of \\x escapes", '"%s"\n' % escaped(d)),
                          ("this repository's YAML writer", yamlio.dump({"input": d.decode("latin-1")})),
                          ("a Python string continued after a backslash",
                           "x = b'%s\\\n%s'\n" % (escaped(d[:13]), escaped(d[13:])))):
            with self.subTest(how=how):
                self.assertIn(self.INPUT, disclosure.found("docs/notes.md", text.encode(), needles))

    def test_4_yamls_nul_before_a_payload_run_that_begins_with_a_digit(self):
        """internal #80's deep review at 85988e9f79, finding 4: YAML writes a NUL and then `12` as `\\012`, which C
        reads as one octal escape; the payload run after the NUL counts in YAML's reading too.  The copy is shorter
        than a byte window and is not the whole input, so only the run counts."""
        run = b"1234 stand-in run"
        with Tree() as t:
            add_findings(t)
            t.write(FINDING + "/input.bin", HEADER + b"\x00" + run, mode="wb")
            needles = disclosure.needles(facts.load(t.root), hold(held={"zlib"}))
        self.assertTrue(needles.nul_digit)
        copy = "run: %s\n" % yaml_escaped(b"\x00" + run)
        self.assertIn("the payload of %s/input.bin" % FINDING, disclosure.found("docs/notes.yaml", copy.encode(), needles))

    def test_5_with_the_line_prefixes_of_markdown_quoting_and_code_comments(self):
        hunk, patched = self.macro()
        cases = []
        for how, start, end in (("a reply quote", "> ", ""), ("a quote in a quote", "> > ", ""),
                                ("// comments", "// ", ""), ("# comments", "# ", ""), ("-- comments", "-- ", ""),
                                ("; comments", "; ", ""), ("a block comment", " * ", ""),
                                ("Rocq comments", "(* ", " *)")):
            for text, label in ((SHORT_PAYLOAD, self.PAYLOAD), (hunk, self.MACRO), (patched, self.ADDED)):
                cases.append(("%s: %s" % (how, label), "".join(start + line + end + "\n" for line in text.splitlines()),
                              label))
        self.assertEach(cases)

    def test_6_as_hex_in_the_layouts_of_xxd_and_xxd_p_and_as_a_c_array_of_bytes(self):
        cases = []
        for data, label in ((self.data, self.INPUT), (self.control, self.CONTROL)):
            hx = data.hex()
            plain = "".join(hx[i:i + 60] + "\n" for i in range(0, len(hx), 60))
            rows = [data[i:i + 12] for i in range(0, len(data), 12)]
            cases += [("xxd", xxd(data), label),
                      ("xxd in a fenced block", "```\n%s```\n" % xxd(data), label),
                      ("xxd in a reply quote", "".join("> " + line for line in xxd(data).splitlines(True)), label),
                      ("xxd -p", plain, label),
                      ("xxd -p in a reply quote", "".join("> " + line for line in plain.splitlines(True)), label),
                      ("xxd -p in Rocq comments", "".join("(* %s *)\n" % line for line in plain.splitlines()), label),
                      ("xxd -p in -- comments", "".join("-- " + line for line in plain.splitlines(True)), label),
                      ("xxd -p in C comments", "".join("/* %s */\n" % line for line in plain.splitlines()), label),
                      ("xxd in Rocq comments", "".join("(* %s *)\n" % line for line in xxd(data).splitlines()), label),
                      ("xxd -i", "unsigned char input_bin[] = {\n%s\n};\n" % ",\n".join(
                          "  " + ", ".join("0x%02x" % c for c in r) for r in rows), label),
                      ("a C array of hex() items", "data = [%s]\n" % ", ".join(hex(c) for c in data), label),
                      ("a C array in decimal", "static const unsigned char in[] = {%s};\n" % ", ".join(map(str, data)),
                       label),
                      ("json.dumps of a list of the bytes", json.dumps(list(data)), label)]
        self.assertEach([("%s: %s" % (how, label), text, label) for how, text, label in cases])

    def test_6_a_hex_line_with_a_long_blank_run_is_searched_in_linear_time(self):
        """internal #80's deep review (6431365684) and bug-finder (6430615819) at 361959911c: two blank runs side by
        side in the `xxd -p` line pattern took time that grew with the square of the blanks (758 s for 262,144).  A
        line of hex, 262,144 blanks and one other character is searched in under a second."""
        import time
        text = "00112233445566778899aabbccddeeff" + " " * (1 << 18) + "x"
        started = time.perf_counter()
        self.found(text, rel="docs/pad.txt")
        self.assertLess(time.perf_counter() - started, 1.0)

    def test_7_by_an_inputs_exact_bytes_or_its_sha256(self):
        sha = hashlib.sha256(self.data).hexdigest()
        digest = "%s, the SHA-256 of %s/input.bin" % (sha, FINDING)
        self.assertEach([("the bytes", self.data, self.INPUT),
                         ("the bytes inside others", b"\x7fELF\0" + self.data + b"\0tail", self.INPUT),
                         ("the SHA-256", "sha256: %s\n" % sha, digest),
                         ("the SHA-256 in upper case", sha.upper(), digest)])


class Search(unittest.TestCase):
    """search: every file a cut keeps, on lint's forked scanner."""

    @unittest.skipIf(lint.default_jobs() < 2, "one CPU: the search runs in this process")
    def test_a_worker_that_dies_fails_the_search_instead_of_hanging_it(self):
        """internal #80's code-quality review at 0ac7eb3f05, finding 2: a worker the out-of-memory killer ends."""
        tools = os.path.dirname(os.path.dirname(HERE))
        script = "\n".join([
            "import os, signal, sys",
            "from oft import disclosure, facts",
            "real = disclosure.found",
            "def dying(rel, data, needles):",
            "    if rel == 'docs/dies.md':",
            "        os.kill(os.getpid(), signal.SIGKILL)",
            "    return real(rel, data, needles)",
            "disclosure.found = dying",
            "tree = facts.load(sys.argv[1])",
            "disclosure.search(sys.argv[1], disclosure.needles(tree, facts.Hold({'zlib'}, set(), {})), (), {})",
            ""])
        with Tree() as t:
            add_findings(t)
            t.write("docs/dies.md", "nothing held here\n")
            try:
                r = subprocess.run([sys.executable, "-B", "-c", script, t.root], cwd=tools,
                                   env=dict(os.environ, PYTHONPATH=tools), capture_output=True, text=True, timeout=60)
            except subprocess.TimeoutExpired:
                self.fail("the search still waited on a dead worker after 60 s")
        self.assertNotEqual(r.returncode, 0, r.stderr)
        self.assertIn("BrokenProcessPool", r.stderr)


class StatementHold(unittest.TestCase):
    """The needles of zlib/checksum_fuzzer's asan_agrees and its pair, held by an open finding of an enrolled zlib."""

    HELD = {"checksum_fuzzer/" + s for s in ("asan_agrees", "asan_disagrees_at_most", "asan_agreement_decidable")}

    @classmethod
    def setUpClass(cls):
        cls.t = Tree()
        cls.needles = disclosure.needles(facts.load(cls.t.root), hold(statements={"zlib": cls.HELD}))

    @classmethod
    def tearDownClass(cls):
        cls.t.close()

    def found(self, text, rel="docs/notes.md"):
        return disclosure.found(rel, text.encode(), self.needles)

    def test_a_held_statement_in_each_form(self):
        sid = "zlib/checksum_fuzzer/asan_agrees"
        stmt = "%s, a statement an open finding of zlib holds back" % sid
        for text, label in (
                (sid, stmt), ("zlib/checksum-fuzzer/asan-agrees", stmt), ("zlib%2Fchecksum_fuzzer%2Fasan_agrees", stmt),
                ("zlib/checksum_fuzzer/asan&#95;agrees", stmt), ("zlib%2Fchecksum%5Ffuzzer%2Fasan%5Fagrees", stmt),
                ("see %s." % sid, stmt), ("见%s中" % sid, stmt),
                ("[a proof](../proofs/zlib/./checksum_fuzzer/asan_agrees/Proof.v)", stmt),
                ("see proofs/zlib//checksum_fuzzer/./asan_agrees", stmt),
                ("[a proof](../proofs/zlib/checksum_fuzzer/ubsan_agrees/../asan_agrees/Proof.v)", stmt),
                ("OssFuzzTheorems.zlib.checksum_fuzzer.Statements.asan_agrees",
                 "OssFuzzTheorems.zlib.checksum_fuzzer.Statements.asan_agrees, the Rocq name of held statement " + sid),
                ("Check zlib.checksum_fuzzer.Statements.asan_agrees.",
                 "OssFuzzTheorems.zlib.checksum_fuzzer.Statements.asan_agrees, the Rocq name of held statement " + sid),
                ("OssFuzzTheorems.zlib.checksum_fuzzer.asan_agrees",
                 "OssFuzzTheorems.zlib.checksum_fuzzer.asan_agrees, the Rocq name of held statement " + sid),
                ("Proofs.zlib.checksum_fuzzer.asan_agrees",
                 "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.asan_agrees, the Rocq name of held statement " + sid),
                ("OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.asan_agrees.Proof.asan_agrees_holds",
                 "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.asan_agrees, the Rocq name of held statement " + sid),
                ("checksum_fuzzer/asan_agrees is held.",
                 "checksum_fuzzer/asan_agrees, held statement %s without its project" % sid)):
            with self.subTest(text=text):
                got = self.found(text)
                self.assertTrue(any(g.startswith(label) for g in got), (label, got))

    def test_a_short_name_counts_in_a_file_about_its_fuzz_target(self):
        """`<s>` and `<s>_holds` name the statement in the fuzz target's own directories, the project's notes, and a
        file that names the fuzz target's Rocq module."""
        label = "held statement zlib/checksum_fuzzer/asan_agrees in a file about its fuzz target"
        for rel, text in (("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "(* Statements.asan_agrees *)"),
                          ("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "(* asan_agrees_holds *)"),
                          ("projects/zlib/checksum_fuzzer/notes.md", "asan_agrees is false"),
                          ("notes/zlib.md", "asan_agrees is withheld while the bug is open."),
                          ("proofs/lib/Held.v", "From OssFuzzTheorems.zlib.checksum_fuzzer Require Statements.\n"
                                                "Definition open_bug : Prop := Statements.asan_agrees.\n"),
                          ("docs/notes.md", "From OssFuzzTheorems Require zlib.checksum_fuzzer.Statements.\n"
                                            "Check Statements.asan_agrees.\n")):
            with self.subTest(rel=rel, text=text):
                got = self.found(text, rel)
                self.assertTrue(any(label in g for g in got), got)

    def test_what_names_another_statement_is_no_mention(self):
        for rel, text in (
                ("docs/notes.md", "see zlib/checksum_fuzzer/asan_agrees_x and zlib/checksum_fuzzer/asan_agreesx"),
                ("docs/notes.md", "see zlib/checksum_fuzzer/ubsan_agrees and asan_agrees"),
                ("docs/json.md", "json/checksum_fuzzer/asan_agrees and json.checksum_fuzzer.Statements.asan_agrees"),
                ("notes/zlib.md", "api-driver/asan_agrees is open; so is asan_ubsan_agrees"),
                ("proofs/zlib/checksum_fuzzer/ubsan_agrees/Proof.v", "(* Statements.ubsan_agrees *)"),
                # internal #80's final review, finding 7: a fuzz target whose module begins with the held one's
                ("projects/zlib/checksum_fuzzer_v2/Statements.v",
                 "From OssFuzzTheorems.zlib.checksum_fuzzer_v2 Require Images.\n"
                 "Definition asan_disagrees_at_most := 0.\nDefinition asan_agrees := 0.\n"),
                ("docs/notes.md", "In OssFuzzTheorems.zlib.checksum_fuzzer_v2, Statements.asan_agrees holds.")):
            with self.subTest(rel=rel, text=text):
                self.assertEqual(self.found(text, rel), set())


if __name__ == "__main__":
    unittest.main()
