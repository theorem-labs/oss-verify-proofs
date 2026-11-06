"""classify.py (oft classify): each function of two builds' symbol facts is identical, moved, changed, added or
removed, matched by name, with the names that share an address and a size (aliases) as one function."""
import contextlib
import hashlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest

from oft import __main__ as cli
from oft import classify, keys, symbols
from oft.tests.helpers import HERE

LIBREAC = os.path.join(HERE, "fixtures", "libreac")
# libreac's fuzz_pcap plain build of 1.8.0 and of 1.9.0, cut to six functions (fixtures/libreac/README.md)
BEFORE = os.path.join(LIBREAC, "fuzz_pcap-1.8.0.plain.tsv")
AFTER = os.path.join(LIBREAC, "fuzz_pcap-1.9.0.plain.tsv")


def sym(name, address, exact, masked, size=16):
    """A stand-in function's Sym: exact and masked are labels of its bytes and of its masked bytes."""
    return symbols.Sym(name, "func", address, size, hashlib.sha256(exact.encode()).hexdigest(),
                       hashlib.sha256(masked.encode()).hexdigest(), "-")


def classes(rows):
    """{names: class} of rows."""
    return {r.names: r.cls for r in rows}


class Classify(unittest.TestCase):
    """The class of each function, between a base and a head build."""

    def test_same_bytes_same_address_is_identical(self):
        b, h = sym("f", 0x100, "f", "F"), sym("f", 0x100, "f", "F")
        self.assertEqual(classify.classify([b], [h]), [classify.Row("identical", ("f",), b, h)])

    def test_same_masked_bytes_new_address_is_moved(self):
        """f calls out of itself, so at 0x140 its bytes differ, but only in their address immediates."""
        b, h = sym("f", 0x100, "f", "F"), sym("f", 0x140, "f at 0x140", "F")
        self.assertEqual(classify.classify([b], [h]), [classify.Row("moved", ("f",), b, h)])

    def test_same_bytes_new_address_is_moved(self):
        """A function with no address immediate has the same bytes anywhere: at a new address it moved."""
        b, h = sym("f", 0x100, "f", "F"), sym("f", 0x140, "f", "F")
        self.assertEqual(classes(classify.classify([b], [h])), {("f",): "moved"})

    def test_other_masked_bytes_is_changed(self):
        """At the same address and size, other bytes that mask to other bytes are a changed function."""
        b, h = sym("f", 0x100, "f", "F"), sym("f", 0x100, "f2", "F2")
        self.assertEqual(classify.classify([b], [h]), [classify.Row("changed", ("f",), b, h)])

    def test_a_name_only_in_head_is_added(self):
        f, g = sym("f", 0x100, "f", "F"), sym("g", 0x200, "g", "G")
        self.assertEqual(classify.classify([f], [f, g]),
                         [classify.Row("identical", ("f",), f, f), classify.Row("added", ("g",), None, g)])

    def test_a_name_only_in_base_is_removed(self):
        f, g = sym("f", 0x100, "f", "F"), sym("g", 0x200, "g", "G")
        self.assertEqual(classify.classify([f, g], [f]),
                         [classify.Row("identical", ("f",), f, f), classify.Row("removed", ("g",), g, None)])

    def test_an_alias_pair_is_one_row(self):
        """h is an alias of g: one body, two names at one address and size, so one row, by the Sym of g."""
        base = [sym("g", 0x200, "g", "G"), sym("h", 0x200, "g", "G")]
        head = [sym("g", 0x240, "g", "G"), sym("h", 0x240, "g", "G")]
        rows = classify.classify(base, head)
        self.assertEqual(len(rows), 1, rows)
        self.assertEqual(rows[0].names, ("g", "h"))
        self.assertEqual(rows[0], classify.Row("moved", ("g", "h"), base[0], head[0]))

    def test_an_alias_that_goes_is_removed(self):
        """The head keeps the body of g but no longer names it h: a contract that names h has no function."""
        base = [sym("g", 0x200, "g", "G"), sym("h", 0x200, "g", "G")]
        head = [sym("g", 0x200, "g", "G")]
        self.assertEqual(classify.classify(base, head),
                         [classify.Row("identical", ("g",), base[0], head[0]),
                          classify.Row("removed", ("h",), base[1], None)])

    def test_a_duplicate_name_is_matched_by_masked_bytes(self):
        """Two static functions named pad, in two files: each is matched with the head's pad of the same masked
        bytes, not by order."""
        one, two = sym("pad", 0x100, "pad 1", "PAD 1"), sym("pad", 0x200, "pad 2", "PAD 2")
        two_moved = sym("pad", 0x180, "pad 2 at 0x180", "PAD 2")
        one_moved = sym("pad", 0x300, "pad 1 at 0x300", "PAD 1")
        self.assertEqual(classify.classify([one, two], [two_moved, one_moved]),
                         [classify.Row("moved", ("pad",), one, one_moved),
                          classify.Row("moved", ("pad",), two, two_moved)])

    def test_an_unmatched_duplicate_is_removed_and_added(self):
        """A pad whose masked bytes no pad of the other build has is matched with none: removed in the base and
        added in the head, never paired by its name alone."""
        one, two = sym("pad", 0x100, "pad 1", "PAD 1"), sym("pad", 0x200, "pad 2", "PAD 2")
        three = sym("pad", 0x240, "pad 3", "PAD 3")
        self.assertEqual(classify.classify([one, two], [one, three]),
                         [classify.Row("identical", ("pad",), one, one),
                          classify.Row("removed", ("pad",), two, None),
                          classify.Row("added", ("pad",), None, three)])

    def test_a_duplicate_at_its_own_address_is_identical(self):
        """Two pads of the same masked bytes, and the head keeps the second where it was: that pair is identical,
        and the first is removed, not moved onto the second's address."""
        one, two = sym("pad", 0x100, "pad", "PAD"), sym("pad", 0x200, "pad", "PAD")
        self.assertEqual(classify.classify([one, two], [two]),
                         [classify.Row("removed", ("pad",), one, None),
                          classify.Row("identical", ("pad",), two, two)])

    def test_a_duplicate_name_keeps_to_the_function_its_alias_matched(self):
        """Every function is one nop (13 00 00 00): base 0x100 {g, h} and 0x200 {h}, head 0x300 {h} and 0x400 {g, h}.
        g matches 0x100 with 0x400, so h of 0x100 goes with it, and h of 0x200 is matched by bytes with h of 0x300:
        two functions, two rows, and the alias pair is not split."""
        nop = bytes.fromhex("13000000")

        def one(name, address):
            return symbols.Sym(name, "func", address, 4, hashlib.sha256(nop).hexdigest(),
                               hashlib.sha256(symbols.mask(nop, address)).hexdigest(), "-")

        base = [one("g", 0x100), one("h", 0x100), one("h", 0x200)]
        head = [one("h", 0x300), one("g", 0x400), one("h", 0x400)]
        self.assertEqual(classify.classify(base, head),
                         [classify.Row("moved", ("g", "h"), base[0], head[1]),
                          classify.Row("moved", ("h",), base[2], head[0])])

    def test_data_objects_are_not_classified(self):
        """A symbol fact's data objects are no functions: no row names one, whether it is in both builds, moved,
        changed or in one build only."""
        f = sym("f", 0x100, "f", "F")
        stays, moves = (symbols.Sym(n, "object", 0x2000, 4, "-", "-", "-") for n in ("stays", "moves"))
        moved = symbols.Sym("moves", "object", 0x3000, 4, "1f" * 32, "-", "-")
        added = symbols.Sym("added", "object", 0x4000, 8, "-", "-", "-")
        self.assertEqual(classify.classify([f, stays, moves], [stays, f, moved, added]),
                         [classify.Row("identical", ("f",), f, f)])

    def test_a_function_of_no_size_is_not_classified(self):
        """A function of size 0 (musl's _start) has no bytes to compare: no row names it, moved or not."""
        f = sym("f", 0x100, "f", "F")
        start, moved = (symbols.Sym("_start", "func", a, 0, "-", "-", "-") for a in (0x80, 0x90))
        self.assertEqual(classify.classify([start, f], [moved, f]), [classify.Row("identical", ("f",), f, f)])

    def test_sections_are_not_classified(self):
        """A symbol fact's sections name places, not functions: no row names one, moved or changed."""
        f = sym("f", 0x100, "f", "F")
        got, moved = (symbols.Sym(".got", "section", a, 16, s, "-", "-") for a, s in ((0x1000, "1f" * 32),
                                                                                      (0x1100, "2e" * 32)))
        self.assertEqual(classify.classify([f, got], [f, moved]), [classify.Row("identical", ("f",), f, f)])

    def test_the_libreac_v19_change(self):
        """libreac 1.9.0 changed pcap_source_next and moved the other five functions of the fixture, among them
        pcap_source_open and the alias pair libc_start_init and __libc_start_init."""
        _sha, base = symbols.load(BEFORE)
        _sha, head = symbols.load(AFTER)
        rows = classify.classify(base, head)
        self.assertEqual(classes(rows)[("pcap_source_next",)], "changed")
        self.assertEqual(classes(rows)[("pcap_source_open",)], "moved")
        self.assertEqual(classes(rows), {
            ("main",): "moved",
            ("libreac_fuzz_fopen",): "moved",
            ("pcap_source_open",): "moved",
            ("pcap_source_next",): "changed",
            ("pcap_source_close",): "moved",
            ("__libc_start_init", "libc_start_init"): "moved",
        })
        nxt = next(r for r in rows if r.names == ("pcap_source_next",))
        self.assertEqual((nxt.base.address, nxt.base.size, nxt.head.address, nxt.head.size),
                         (0x132e0, 788, 0x132a0, 732))


class ClassifyCommand(unittest.TestCase):
    """`oft classify BASE.tsv HEAD.tsv [--json]`: a row per function and a count per class."""

    def oft(self, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = cli.main(["classify", *args])
        return rc, out.getvalue()

    def test_oft_classify_prints_each_function_and_the_counts(self):
        """A row per function, by base address, its names joined by a space (a name holds none), then a count per
        class."""
        self.assertEqual(self.oft(BEFORE, AFTER), (0, (
            "class\tnames\tbase_address\tbase_size\thead_address\thead_size\n"
            "moved\tmain\t0x12714\t708\t0x126d4\t708\n"
            "moved\tlibreac_fuzz_fopen\t0x12bb4\t144\t0x12b74\t144\n"
            "moved\tpcap_source_open\t0x13208\t216\t0x131c8\t216\n"
            "changed\tpcap_source_next\t0x132e0\t788\t0x132a0\t732\n"
            "moved\tpcap_source_close\t0x135f4\t48\t0x1357c\t48\n"
            "moved\t__libc_start_init libc_start_init\t0x13854\t76\t0x137dc\t76\n"
            "6 functions: 0 identical, 5 moved, 1 changed, 0 added, 0 removed\n")))

    def test_a_function_in_one_build_has_no_address_in_the_other(self):
        """An added function's base and a removed one's head are `-`; added rows follow the rest, by head
        address."""
        _sha, base = symbols.load(BEFORE)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "head.tsv")
            symbols.write(path, [s for s in base if s.name != "main"] + [sym("extra", 0x20000, "x", "X")],
                          "0" * 64)
            rc, said = self.oft(BEFORE, path)
        self.assertEqual(rc, 0, said)
        lines = said.splitlines()
        self.assertEqual(lines[1], "removed\tmain\t0x12714\t708\t-\t-")
        self.assertEqual(lines[-2], "added\textra\t-\t-\t0x20000\t16")
        self.assertEqual(lines[-1], "7 functions: 5 identical, 0 moved, 0 changed, 1 added, 1 removed")

    def test_oft_classify_json(self):
        """--json: every row with each build's Sym (its address as the fact writes it), and the counts."""
        rc, said = self.oft(BEFORE, AFTER, "--json")
        self.assertEqual(rc, 0, said)
        got = json.loads(said)
        self.assertEqual(got["counts"], {"identical": 0, "moved": 5, "changed": 1, "added": 0, "removed": 0})
        self.assertEqual(len(got["rows"]), 6)
        _sha, base = symbols.load(BEFORE)
        _sha, head = symbols.load(AFTER)
        nxt = [r for r in got["rows"] if r["names"] == ["pcap_source_next"]]
        b = next(s for s in base if s.name == "pcap_source_next")
        h = next(s for s in head if s.name == "pcap_source_next")
        self.assertEqual(nxt, [{"class": "changed", "names": ["pcap_source_next"],
                                "base": dict(b._asdict(), address="0x132e0"),
                                "head": dict(h._asdict(), address="0x132a0")}])

    def test_a_fact_that_does_not_load_is_refused(self):
        """A file that is no symbol fact is named, with why, and the exit status is 1."""
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "head.tsv")
            with open(path, "w", encoding="utf-8") as f:
                f.write("not a symbol fact\n")
            rc, said = self.oft(BEFORE, path)
            missing = os.path.join(d, "missing.tsv")
            rc2, said2 = self.oft(missing, AFTER)
        self.assertEqual(rc, 1)
        self.assertTrue(said.startswith("FAIL oft classify: %s: line 1: " % path), said)
        self.assertEqual(rc2, 1)
        self.assertTrue(said2.startswith("FAIL oft classify: %s: " % missing), said2)

    def test_classify_is_not_the_checker(self):
        """keys.NOT_THE_CHECKER names classify.py, so a change to it re-checks no fuzz target; that holds only while
        a check opens it not, so oft.check, with oft.facts and oft.fetch, does not import it."""
        self.assertTrue(keys.not_the_checker("tools/oft/classify.py"))
        tools = os.path.dirname(os.path.dirname(os.path.abspath(classify.__file__)))
        done = subprocess.run([sys.executable, "-c", "import sys, oft.check, oft.facts, oft.fetch; "
                               "print('oft.classify' in sys.modules)"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=tools))
        self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "False\n", ""))


if __name__ == "__main__":
    unittest.main()
