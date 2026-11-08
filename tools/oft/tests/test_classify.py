"""classify.py (oft classify): each function of two builds' symbol facts is identical, moved, changed, added or
removed, matched by name, with the names that share an address and a size (aliases) as one function."""
import contextlib
import hashlib
import io
import json
import os
import struct
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


def sym(name, address, exact, masked, size=16, targets="-"):
    """A stand-in function's Sym: exact and masked are labels of its bytes and of its masked bytes, and targets is
    one of what its masked immediates point at (a label too, but for `-` and `?`)."""
    return symbols.Sym(name, "func", address, size, hashlib.sha256(exact.encode()).hexdigest(),
                       hashlib.sha256(masked.encode()).hexdigest(),
                       targets if targets in ("-", "?") else hashlib.sha256(targets.encode()).hexdigest(), "-")


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
                               hashlib.sha256(symbols.mask(nop, address)).hexdigest(), "-", "-")

        base = [one("g", 0x100), one("h", 0x100), one("h", 0x200)]
        head = [one("h", 0x300), one("g", 0x400), one("h", 0x400)]
        self.assertEqual(classify.classify(base, head),
                         [classify.Row("moved", ("g", "h"), base[0], head[1]),
                          classify.Row("moved", ("h",), base[2], head[0])])

    def test_data_objects_are_not_classified(self):
        """A symbol fact's data objects are no functions: no row names one, whether it is in both builds, moved,
        changed or in one build only."""
        f = sym("f", 0x100, "f", "F")
        stays, moves = (symbols.Sym(n, "object", 0x2000, 4, "-", "-", "-", "-") for n in ("stays", "moves"))
        moved = symbols.Sym("moves", "object", 0x3000, 4, "1f" * 32, "-", "-", "-")
        added = symbols.Sym("added", "object", 0x4000, 8, "-", "-", "-", "-")
        self.assertEqual(classify.classify([f, stays, moves], [stays, f, moved, added]),
                         [classify.Row("identical", ("f",), f, f)])

    def test_a_function_of_no_size_is_not_classified(self):
        """A function of size 0 (musl's _start) has no bytes to compare: no row names it, moved or not."""
        f = sym("f", 0x100, "f", "F")
        start, moved = (symbols.Sym("_start", "func", a, 0, "-", "-", "-", "-") for a in (0x80, 0x90))
        self.assertEqual(classify.classify([start, f], [moved, f]), [classify.Row("identical", ("f",), f, f)])

    def test_sections_are_not_classified(self):
        """A symbol fact's sections name places, not functions: no row names one, moved or changed."""
        f = sym("f", 0x100, "f", "F")
        got, moved = (symbols.Sym(".got", "section", a, 16, s, "-", "-", "-") for a, s in ((0x1000, "1f" * 32),
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

    def test_a_fact_of_the_revision_before_the_targets_is_changed_against_one_with_them(self):
        """main's symbol facts are of `oss-fuzz-theorems/symbols/1`, which has no targets column, and these
        tools land before the facts that have it: a function of such a fact reads `?`, which is equal to
        nothing, so it is changed against a fact of the new revision, never moved and never identical.  Here the
        head is the base's own fact of revision 1, written again as revision 2 with its real targets."""
        with open(BEFORE, encoding="utf-8") as f:
            text = f.read()
        old = "\n".join(["# oss-fuzz-theorems/symbols/1 " + line.split(" ", 2)[2] if i == 0 else
                         "\t".join(f[:6] + f[7:]) for i, line in enumerate(text[:-1].split("\n"))
                         for f in [line.split("\t")]]) + "\n"
        _sha, before = symbols.parse(old)
        _sha, after = symbols.load(BEFORE)
        self.assertEqual({s.targets for s in before if s.kind == "func" and s.size}, {"?"})
        self.assertEqual([s._replace(targets="-") for s in before], [s._replace(targets="-") for s in after])
        self.assertEqual(set(classes(classify.classify(before, after)).values()), {"changed"})
        self.assertEqual(set(classes(classify.classify(after, before)).values()), {"changed"})


def jal(disp):
    """jal ra, disp."""
    return (((disp >> 20) & 1) << 31 | ((disp >> 1) & 0x3FF) << 21 | ((disp >> 11) & 1) << 20
            | ((disp >> 12) & 0xFF) << 12 | 1 << 7 | 0x6F)


def jal_x0(disp):
    """jal x0, disp: a jump that links no register."""
    return jal(disp) & ~(0x1F << 7)


def auipc_ld(at, to):
    """auipc a0, %pcrel_hi(to); ld a0, %pcrel_lo(to)(a0), the two instructions at the address at."""
    delta = to - at
    high = (delta + 0x800) >> 12
    low = delta - (high << 12)
    return ((high & 0xFFFFF) << 12 | 10 << 7 | 0x17,
            (low & 0xFFF) << 20 | 10 << 15 | 3 << 12 | 10 << 7 | 0x03)


RET = 0x00008067


def built(functions, objects=(), slots=(), empty=()):
    """[Sym] of a build whose functions are (name, address, the words of its code), whose data objects are
    (name, address, size), whose .got slots are (address, the value the slot holds) and whose functions of size 0
    are (name, address), in a .text of 0x2000 bytes at 0x10000, a .data of 0x2000 bytes at 0x20000 and a .got of
    0x100 bytes at 0x23000: the rows symbols.read would write, with each function's targets resolved against
    them all."""
    rows, points = [], {}
    for name, address, ws in functions:
        code = struct.pack("<%dI" % len(ws), *ws)
        masked, found = symbols.mask_targets(code, address)
        points[len(rows)] = found
        rows.append(symbols.Sym(name, "func", address, len(code), hashlib.sha256(code).hexdigest(),
                                hashlib.sha256(masked).hexdigest(), "-", "-"))
    rows += [symbols.Sym(n, "object", a, s, "1f" * 32, "-", "-", "-") for n, a, s in objects]
    rows += [symbols.Sym(n, "func", a, 0, "-", "-", "-", "-") for n, a in empty]
    rows += [symbols.Sym(n, "section", a, s, "2e" * 32, "-", "-", "-")
             for n, a, s in ((".text", 0x10000, 0x2000), (".data", 0x20000, 0x2000), (".got", 0x23000, 0x100))]
    held = dict(slots)
    find = symbols.locator(rows, lambda address: held.get(address))
    for i, found in points.items():
        rows[i] = rows[i]._replace(targets=symbols.target_id(found, find))
    return rows


class Targets(unittest.TestCase):
    """A function that calls another function or reads another global is changed, never moved and never identical:
    mask() zeroes the call's displacement and the halves of a data address, so its masked bytes say nothing about
    them, and the targets of the symbol fact hold what they point at, by symbol and offset."""

    def cls(self, base, head, name="f"):
        return classes(classify.classify(base, head))[(name,)]

    def test_a_call_of_another_function_at_one_address_is_changed(self):
        """f calls g in the base and h in the head, from the same address: the jal's displacement is all that
        differs, and mask() zeroes it, so only the targets tell the two apart."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("g", 0x10100, (RET,)), ("h", 0x10200, (RET,))])
        head = built([("f", 0x10000, (jal(0x200), RET)), ("g", 0x10100, (RET,)), ("h", 0x10200, (RET,))])
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertNotEqual(base[0].targets, head[0].targets)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_call_of_another_function_that_moved_too_is_changed(self):
        """f moved and now calls h, not g: its masked bytes are those of the move, so its targets alone keep it out
        of moved."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("g", 0x10100, (RET,)), ("h", 0x10200, (RET,))])
        head = built([("f", 0x10040, (jal(0x1c0), RET)), ("g", 0x10100, (RET,)), ("h", 0x10200, (RET,))])
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_read_of_another_global_is_changed(self):
        """f reads g1 in the base and g2 in the head: mask() zeroes the auipc's high half and the load's low half,
        so the two mask equal."""
        objects = (("g1", 0x20000, 8), ("g2", 0x20100, 8))
        base = built([("f", 0x10000, auipc_ld(0x10000, 0x20000) + (RET,))], objects)
        head = built([("f", 0x10000, auipc_ld(0x10000, 0x20100) + (RET,))], objects)
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertNotEqual(base[0].targets, head[0].targets)
        self.assertEqual(self.cls(base, head), "changed")

    def test_the_same_bytes_whose_callee_is_another_function_are_changed(self):
        """f has the same bytes at the same address in both builds, but the function at the address it calls is g
        in the base and h in the head: it would read as identical, and the proof of f would be left alone."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("g", 0x10100, (RET,))])
        head = built([("f", 0x10000, (jal(0x100), RET)), ("h", 0x10100, (RET,))])
        self.assertEqual(base[0].exact, head[0].exact)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_function_whose_targets_moved_with_it_is_moved(self):
        """f and the g it calls both moved by 0x40: the call lands on the same symbol at the same offset, so f only
        moved, and no proof of it needs work."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("g", 0x10100, (RET,))])
        head = built([("f", 0x10040, (jal(0x100), RET)), ("g", 0x10140, (RET,))])
        self.assertEqual((base[0].masked, base[0].targets), (head[0].masked, head[0].targets))
        self.assertEqual(self.cls(base, head), "moved")

    def test_a_caller_of_a_function_that_moved_stays_where_it_is(self):
        """caller did not move, and the f it calls did: its jal's displacement, which mask() zeroes, is all that
        differs, and the call lands on f at offset 0 in both builds.  Nothing in caller changed, so it is moved,
        the class of a function whose address immediates alone differ, and not changed."""
        base = built([("f", 0x10000, (RET,)), ("caller", 0x10200, (jal(-0x200), RET))])
        head = built([("f", 0x10040, (RET,)), ("caller", 0x10200, (jal(-0x1c0), RET))])
        self.assertNotEqual(base[1].exact, head[1].exact)
        self.assertEqual((base[1].masked, base[1].targets), (head[1].masked, head[1].targets))
        self.assertEqual(self.cls(base, head, "caller"), "moved")

    def test_a_target_that_lands_nowhere_is_changed(self):
        """A target outside every symbol and every section of its build is `?`, which is equal to nothing: f is
        changed, though its bytes, its masked bytes and its address are the same."""
        rows = built([("f", 0x10000, (jal(0x100), RET)), ("g", 0x10100, (RET,))])
        lost = [rows[0]._replace(targets="?")] + rows[1:]
        self.assertEqual(self.cls(lost, lost), "changed")

    def test_a_got_slot_that_holds_another_symbol_is_changed(self):
        """f reads the same .got slot in both builds, and the linker gave that slot to g2 instead of g1: the slot
        has no symbol, so its place says nothing, and the targets carry what it holds."""
        objects = (("g1", 0x20000, 8), ("g2", 0x20100, 8))
        code = [("f", 0x10000, auipc_ld(0x10000, 0x23040) + (RET,))]
        base = built(code, objects, ((0x23040, 0x20000),))
        head = built(code, objects, ((0x23040, 0x20100),))
        self.assertEqual(base[0].exact, head[0].exact)
        self.assertNotEqual(base[0].targets, head[0].targets)
        self.assertEqual(self.cls(base, head), "changed")

    def test_an_auipc_with_no_masked_low_half_is_changed(self):
        """The mask zeroes every auipc, but it zeroed no low half here (nothing completes this one), so the fact
        cannot say which address the pair forms: the targets are `?` and f is changed, not identical."""
        auipc, _ld = auipc_ld(0x10000, 0x20800)
        rows = built([("f", 0x10000, (auipc, RET))])
        self.assertEqual(rows[0].targets, "?")
        self.assertEqual(self.cls(rows, rows), "changed")

    def test_a_gp_relative_read_is_changed(self):
        """gp holds an address this function never forms, so the fact cannot say where a gp-relative read lands:
        its targets are `?`."""
        ld_gp = (0x10 & 0xFFF) << 20 | 3 << 15 | 3 << 12 | 10 << 7 | 0x03
        rows = built([("f", 0x10000, (ld_gp, RET))])
        self.assertEqual(rows[0].targets, "?")
        self.assertEqual(self.cls(rows, rows), "changed")

    def test_a_slot_that_holds_another_number_is_changed(self):
        """The slot of a thread-local variable holds its offset from the thread pointer, which lands in no symbol
        and in no section: the targets carry the number, so another variable's offset reads as changed."""
        code = [("f", 0x10000, auipc_ld(0x10000, 0x23040) + (RET,))]
        base, head = built(code, (), ((0x23040, 0x8),)), built(code, (), ((0x23040, 0x10),))
        self.assertEqual(base[0].exact, head[0].exact)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_general_dynamic_slot_pair_carries_its_second_word(self):
        """A general-dynamic TLS pair holds the module in its first word and the variable's offset in its second,
        both numbers: a 16-aligned slot of two numbers carries both, so a change of the second is changed."""
        code = [("f", 0x10000, auipc_ld(0x10000, 0x23040) + (RET,))]
        base = built(code, (), ((0x23040, 1), (0x23048, 0x8)))
        head = built(code, (), ((0x23040, 1), (0x23048, 0x10)))
        self.assertEqual(base[0].exact, head[0].exact)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_call_of_another_function_of_size_0_is_changed(self):
        """An assembly function with no `.size` (musl's __clone) holds no address range, so a call of it would
        land in .text alone: it is matched at its own address, and a call of another one there is changed."""
        code = [("f", 0x10000, (jal(0x100), RET))]
        base, head = built(code, (), (), (("g", 0x10100),)), built(code, (), (), (("h", 0x10100),))
        self.assertEqual(base[0].exact, head[0].exact)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_call_of_another_function_of_the_same_name_is_changed(self):
        """Two static functions share the name `pad`, of 8 and of 16 bytes: the size is in the target, so a call
        that lands on the other one is changed, not moved."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("pad", 0x10100, (RET, RET)),
                      ("pad", 0x10200, (RET, RET, RET, RET))])
        head = built([("f", 0x10000, (jal(0x200), RET)), ("pad", 0x10100, (RET, RET)),
                      ("pad", 0x10200, (RET, RET, RET, RET))])
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertEqual(self.cls(base, head, "f"), "changed")

    def test_a_call_of_a_function_of_the_same_name_and_size_is_changed(self):
        """Two static functions share the name `pad` AND their size, so the name and the size tell them apart
        no better than the name: neither names a place, and the call lands in .text at its own offset."""
        base = built([("f", 0x10000, (jal(0x100), RET)), ("pad", 0x10100, (RET, RET)),
                      ("pad", 0x10200, (RET, RET))])
        head = built([("f", 0x10000, (jal(0x200), RET)), ("pad", 0x10100, (RET, RET)),
                      ("pad", 0x10200, (RET, RET))])
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertEqual(self.cls(base, head, "f"), "changed")

    def test_a_read_of_an_object_of_the_same_name_and_size_is_changed(self):
        """The same of data: musl has two `buf` and the sanitizers five `lock`, several of them of one size.
        f reads one in the base and the other in the head, from the same address."""
        objects = (("lock", 0x20000, 4), ("lock", 0x20100, 4))
        base = built([("f", 0x10000, auipc_ld(0x10000, 0x20000) + (RET,))], objects)
        head = built([("f", 0x10000, auipc_ld(0x10000, 0x20100) + (RET,))], objects)
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertEqual(self.cls(base, head), "changed")

    def test_a_target_outside_every_row_makes_the_locator_give_nothing(self):
        """The `?` of a target that lands nowhere comes from the locator, not from a row written by hand: a jal
        that leaves .text lands in no row of the build."""
        rows = built([("f", 0x10800, (jal(0x7f800), RET))])
        self.assertEqual(rows[0].targets, "?")
        self.assertEqual(self.cls(rows, rows), "changed")

    def test_a_low_half_of_two_high_halves_keeps_which_is_which(self):
        """One load completes an auipc of g1 on one path and an auipc of g2 on the other.  Swapping the two in
        the head leaves the set of places equal, so the targets hold each place by the high half that forms it:
        with the places alone the two builds would read as moved."""
        objects = (("g1", 0x20040, 8), ("g2", 0x21040, 8))
        nop = 0x00000013

        def body(first, second):
            """beq a0,a0,+12 (to the far jal); auipc a0,hi(first); j +0x1000 (to the load); j +0xff8 (to the
            second auipc); 1021 nops; auipc a0,hi(second); ld a0,lo(a0); ret.  The two auipc are 0x1000 bytes
            apart and so are the two globals, so all four pairs have the same 12-bit low half: one load
            completes either auipc, and the mask zeroes the two high halves and that low half, whichever way
            the two globals are paired with the two auipc."""
            one, low_one = auipc_ld(0x10004, first)
            two, low_two = auipc_ld(0x11004, second)
            assert symbols.i_imm(low_one) == symbols.i_imm(low_two), (low_one, low_two)
            beq = 10 << 20 | 10 << 15 | 6 << 8 | 0x63      # beq a0,a0,+12
            return (beq, one, jal_x0(0x1000), jal_x0(0xff8)) + (nop,) * 1021 + (two, low_two, RET)

        base = built([("f", 0x10000, body(0x20040, 0x21040))], objects)
        head = built([("f", 0x10000, body(0x21040, 0x20040))], objects)
        self.assertEqual(base[0].masked, head[0].masked)
        self.assertNotEqual(base[0].targets, "?")
        self.assertEqual(self.cls(base, head), "changed")


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
