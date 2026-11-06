"""elf.py and symbols.py (oft symbols): a build's symbol fact is read from its unstripped twin, is of the binary
harness.yaml pins, lists every function and alias with the SHA-256 of its bytes, exact and with its address
immediates masked, and its source lines, and every data object with the SHA-256 of its bytes when it has any, and
reads back as it was written."""
import contextlib
import hashlib
import io
import json
import os
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

from oft import __main__ as cli
from oft import elf, facts, keys, symbols
from oft.tests.helpers import HERE, tree

ELF = os.path.join(HERE, "fixtures", "elf")
UNSTRIPPED = os.path.join(ELF, "two.unstripped")
STRIPPED = os.path.join(ELF, "two.stripped")
LINES = os.path.join(ELF, "two.lines.txt")
# sha256sum two.stripped (fixtures/elf/README.md)
STRIPPED_SHA = "5bfde43310ed9ace655eed147acc43fc7553d2ed0e0058ccb7f569cc98f2dfb9"
UNIT = "zlib/checksum_fuzzer"
# the fixture tree's stand-in pin of that fuzz target's plain build (harness.yaml builds.plain.sha256)
PLAIN_PIN = "64e0aab9f6e65f69a654dcebbc0ee2553fcd665b258f6e6d6bebf3e7bc019543"
FACT = "projects/zlib/checksum_fuzzer/symbols/plain.tsv"


def words(*ws):
    return struct.pack("<%dI" % len(ws), *ws)


# an Image with one section that holds every address, so that only the control flow decides which lui is masked
EVERY_ADDRESS = symbols.NO_IMAGE._replace(sections=((0, 1 << 64),))


def lines_text():
    with open(LINES, encoding="utf-8") as f:
        return f.read()


def fixture(lines=None):
    """symbols.read of the fixture, pinned at its own sha256: {name: Sym}."""
    return {s.name: s for s in symbols.read(UNSTRIPPED, STRIPPED, lines_text() if lines is None else lines,
                                            STRIPPED_SHA)}


class Symbols(unittest.TestCase):
    """The symbol fact of the fixture build: what it lists, what refuses it, and how its bytes are masked."""

    def test_every_function_and_alias_is_read(self):
        """f, g, h and _start are the functions of the symbol table; h is an alias of g, kept under its own name at
        g's address."""
        syms = fixture()
        self.assertEqual({n for n, s in syms.items() if s.kind == "func"}, {"f", "g", "h", "_start"})
        self.assertEqual(syms["g"].address, syms["h"].address)
        self.assertEqual((syms["f"].address, syms["f"].size, syms["g"].address, syms["g"].size),
                         (0x112a8, 108, 0x11314, 40))

    def test_a_function_of_no_size_is_kept_without_bytes(self):
        """_start is a function of size 0, as musl's is: its row has its address and size 0, and no bytes to hash and
        no lines, so exact, masked and lines are -.  Symbols.v still names its address, which fuzz_pcap's proofs use."""
        self.assertEqual(fixture()["_start"], symbols.Sym("_start", "func", 0x1129c, 0, "-", "-", "-"))

    def test_each_data_object_is_read(self):
        """seed (0x5eed, in .data) and counter (zero, in .bss) are the data objects: exact is the SHA-256 of an
        object's bytes in the stripped binary, or - for one in a section with no file contents; neither has masked
        bytes or source lines."""
        syms, seed = fixture(), (0x5eed).to_bytes(4, "little")
        self.assertEqual({n for n, s in syms.items() if s.kind == "object"}, {"seed", "counter"})
        self.assertEqual(elf.Elf(STRIPPED).contents(0x1233c, 4), seed)
        self.assertIsNone(elf.Elf(STRIPPED).contents(0x12340, 4))
        self.assertEqual(syms["seed"],
                         symbols.Sym("seed", "object", 0x1233c, 4, hashlib.sha256(seed).hexdigest(), "-", "-"))
        self.assertEqual(syms["counter"], symbols.Sym("counter", "object", 0x12340, 4, "-", "-", "-"))
        self.assertRaisesRegex(ValueError, "no allocated section", elf.Elf(STRIPPED).contents, 0x20000, 4)

    def test_each_allocated_section_is_read(self):
        """Every allocated section of the stripped binary is a row of kind section (llvm-readelf -S two.stripped), so
        that data no symbol names, a GOT slot among it, is its section's address and an offset: exact is the SHA-256 of
        its bytes, or - for .bss, which has none in the file.  The twins are two links, and each hashes its own output
        into its build-id note, so the notes differ and the fact takes the stripped one's."""
        bare, seed = elf.Elf(STRIPPED), (0x5eed).to_bytes(4, "little")
        sections = {n: s for n, s in fixture().items() if s.kind == "section"}
        self.assertEqual({n: (s.address, s.size) for n, s in sections.items()},
                         {".note.gnu.build-id": (0x10200, 0x24), ".eh_frame_hdr": (0x10224, 0x1c),
                          ".eh_frame": (0x10240, 0x5c), ".text": (0x1129c, 0xa0), ".data": (0x1233c, 4),
                          ".bss": (0x12340, 4)})
        self.assertEqual(sections[".data"],
                         symbols.Sym(".data", "section", 0x1233c, 4, hashlib.sha256(seed).hexdigest(), "-", "-"))
        self.assertEqual(sections[".bss"], symbols.Sym(".bss", "section", 0x12340, 4, "-", "-", "-"))
        self.assertEqual(sections[".text"].exact, hashlib.sha256(bare.text).hexdigest())
        note = bare.data[0x200:0x224]
        self.assertNotEqual(elf.Elf(UNSTRIPPED).data[0x200:0x224], note)
        self.assertEqual(sections[".note.gnu.build-id"].exact, hashlib.sha256(note).hexdigest())

    def test_a_stripped_twin_with_other_bytes_is_refused(self):
        """A stripped file that is not the binary harness.yaml pins is refused, naming both SHA-256 values."""
        other = hashlib.sha256(b"another build").hexdigest()
        with self.assertRaises(ValueError) as e:
            symbols.read(UNSTRIPPED, STRIPPED, lines_text(), other)
        self.assertIn(STRIPPED_SHA, str(e.exception))
        self.assertIn(other, str(e.exception))

    def test_a_pair_whose_text_differs_is_refused(self):
        """The addresses come from the unstripped file and the bytes from the stripped one: two files whose .text
        differs are no twins, and are refused even when the stripped one is the pinned binary."""
        text = elf.Elf(STRIPPED)
        with tempfile.TemporaryDirectory() as d:
            changed = os.path.join(d, "two.stripped")
            shutil.copy(STRIPPED, changed)
            offset = text.data.index(text.text) + 8
            with open(changed, "r+b") as f:
                f.seek(offset)
                f.write(bytes([text.data[offset] ^ 0xFF]))
            with self.assertRaisesRegex(ValueError, r"\.text"):
                symbols.read(UNSTRIPPED, changed, lines_text(), elf.Elf(changed).sha256)

    def test_a_pair_whose_object_bytes_differ_is_refused(self):
        """An object's bytes come from the stripped file too: a pair whose .text agrees but whose seed differs is no
        twin either.  seed is at file offset 0x33c of two.stripped (llvm-readelf -S: .data at 0x1233c, offset
        0x33c)."""
        bare = elf.Elf(STRIPPED)
        self.assertEqual(bare.data[0x33c:0x340], bare.contents(0x1233c, 4))
        with tempfile.TemporaryDirectory() as d:
            changed = os.path.join(d, "two.stripped")
            shutil.copy(STRIPPED, changed)
            with open(changed, "r+b") as f:
                f.seek(0x33c)
                f.write(b"\x00")
            self.assertEqual(elf.Elf(changed).text, bare.text)
            with self.assertRaisesRegex(ValueError, "seed"):
                symbols.read(UNSTRIPPED, changed, lines_text(), elf.Elf(changed).sha256)

    def test_a_pair_whose_sections_differ_is_refused(self):
        """A section's bytes come from the stripped file too: a pair whose .text and objects agree but whose .eh_frame
        differs (file offset 0x240 of two.stripped, llvm-readelf -S) is no twin either."""
        bare = elf.Elf(STRIPPED)
        with tempfile.TemporaryDirectory() as d:
            changed = os.path.join(d, "two.stripped")
            shutil.copy(STRIPPED, changed)
            with open(changed, "r+b") as f:
                f.seek(0x240)
                f.write(bytes([bare.data[0x240] ^ 0xFF]))
            self.assertEqual(elf.Elf(changed).text, bare.text)
            with self.assertRaisesRegex(ValueError, r"\.eh_frame"):
                symbols.read(UNSTRIPPED, changed, lines_text(), elf.Elf(changed).sha256)

    def test_a_tls_section_holds_no_data_object(self):
        """A TLS section's addresses are a template's (a .tbss overlaps the sections after it), so an object's bytes
        are never looked up in one: here section 3 of two.stripped, .eh_frame at 0x10240 (llvm-readelf -S), is made a
        .tbss over seed's address, and seed's bytes still come from .data."""
        bare = elf.Elf(STRIPPED)
        header = struct.unpack_from("<Q", bare.data, 0x28)[0] + 3 * 64   # e_shoff, then Elf64_Shdr 3
        self.assertEqual(struct.unpack_from("<Q", bare.data, header + 16)[0], 0x10240)
        data = bytearray(bare.data)
        struct.pack_into("<IQQ", data, header + 4, elf.SHT_NOBITS, 0x3 | elf.SHF_TLS, 0x1233c)   # write, alloc, TLS
        struct.pack_into("<Q", data, header + 32, 4)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "two.stripped")
            with open(path, "wb") as f:
                f.write(data)
            self.assertEqual(elf.Elf(path).contents(0x1233c, 4), (0x5eed).to_bytes(4, "little"))

    def test_a_row_of_another_shape_for_its_kind_is_refused(self):
        """A function has two SHA-256s, or - for both and for its lines when its size is 0; an object has a size, its
        bytes' SHA-256 or -, no masked bytes and no lines; a section has its bytes' SHA-256 or -, and no masked bytes
        and no lines; and no row has another kind."""
        sha = "1f" * 32
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "plain.tsv")
            for row in ("f\tfunc\t0x112a8\t108\t-\t%s\t-" % sha, "seed\tobject\t0x1233c\t4\t%s\t%s\t-" % (sha, sha),
                        "seed\tobject\t0x1233c\t4\t%s\t-\ttwo.c:6-6" % sha, "seed\tdata\t0x1233c\t4\t-\t-\t-",
                        "_start\tfunc\t0x1129c\t0\t%s\t%s\t-" % (sha, sha), "_start\tfunc\t0x1129c\t0\t-\t-\ttwo.c:1-1",
                        "seed\tobject\t0x1233c\t0\t-\t-\t-", ".got\tsection\t0x1d8e0\t152\t%s\t%s\t-" % (sha, sha),
                        ".got\tsection\t0x1d8e0\t152\t-\t-\ttwo.c:1-1"):
                with self.subTest(row=row):
                    with open(path, "w", encoding="utf-8") as f:
                        f.write("# oss-fuzz-theorems/symbols/1 sha256=%s\n%s\n" % (STRIPPED_SHA, row))
                    self.assertRaisesRegex(ValueError, "^line 2: ", symbols.load, path)

    def test_masking_zeroes_address_immediates_only(self):
        """auipc a0,0x12; jal ra,0x40; addi a1,a1,5: the auipc's and the jal's immediates (the jal leaves the
        function) are zeroed, and the 5 of addi, which takes no address, is kept."""
        masked = symbols.mask(words(0x00012517, 0x040000EF, 0x00558593), 0x10000)
        self.assertEqual(masked, words(0x00000517, 0x000000EF, 0x00558593))
        auipc, jal, addi = struct.unpack("<3I", masked)
        self.assertEqual((symbols.u_imm(auipc), symbols.jal_imm(jal), symbols.i_imm(addi)), (0, 0, 5))

    def test_a_jump_inside_the_function_keeps_its_displacement(self):
        """beq +8, j +8 and j -8 land inside the 16 bytes at 0x10000 and keep their displacements: a function that
        only moved still masks equal, and a changed loop does not.  bne +16 leaves it and is masked."""
        code = words(0x00B50463, 0x0080006F, 0xFF9FF06F, 0x00B51863)
        self.assertEqual([symbols.b_imm(0x00B50463), symbols.jal_imm(0x0080006F), symbols.jal_imm(0xFF9FF06F),
                          symbols.b_imm(0x00B51863)], [8, 8, -8, 16])
        want = words(0x00B50463, 0x0080006F, 0xFF9FF06F, 0x00B51063)
        self.assertEqual(symbols.mask(code, 0x10000), want)
        self.assertEqual(symbols.mask(code, 0x24680), want)

    def test_only_a_lui_that_forms_an_address_in_a_section_is_masked(self):
        """lui a0,0x12345; addi a0,a0,0x678; lui a2,0x12345; sw a1,0x67c(a2); lui a1,0x1; addiw a1,a1,-1: with a section
        at [0x12345000, 0x12346000), the luis form 0x12345678 and 0x1234567c in it, the high and low halves of
        addresses, so all four immediates are masked; addiw takes no base, so lui a1,0x1 makes the number 4095 and is
        kept.  With no section there (NO_IMAGE), every lui and low half is kept."""
        code = words(0x12345537, 0x67850513, 0x12345637, 0x66B62E23, 0x000015B7, 0xFFF5859B)
        image = symbols.NO_IMAGE._replace(sections=((0x12345000, 0x12346000),))
        self.assertEqual(symbols.mask(code, 0x10000, image),
                         words(0x00000537, 0x00050513, 0x00000637, 0x00B62023, 0x000015B7, 0xFFF5859B))
        self.assertEqual(symbols.mask(code, 0x10000), code)

    def test_a_lui_with_one_use_outside_every_section_is_kept(self):
        """lui a0,0x12345; ld a1,0x678(a0); ld a2,-0x800(a0): 0x12345678 is in the section [0x12345000, 0x12346000)
        but 0x12344800 is in none, so the lui makes no address, and it and both offsets are kept."""
        code = words(0x12345537, 0x67853583, 0x80053603)
        self.assertEqual(symbols.mask(code, 0x10000, symbols.NO_IMAGE._replace(sections=((0x12345000, 0x12346000),))),
                         code)

    def test_a_call_ends_what_a_caller_saved_register_held(self):
        """lui a0,0x10; jal ra,+0x40; addi a0,a0,5; ret: the callee may overwrite every caller-saved register, so
        after the call a0 is its return value, no address high half, and addi a0,a0,5 against 6 is a changed
        function.  Neither addi nor the lui is masked; the jal leaves the function and is."""
        five = words(0x00010537, 0x040000EF, 0x00550513, 0x00008067)
        six = words(0x00010537, 0x040000EF, 0x00650513, 0x00008067)
        self.assertNotEqual(symbols.mask(five, 0x10000, EVERY_ADDRESS), symbols.mask(six, 0x10000, EVERY_ADDRESS))
        self.assertEqual(symbols.mask(five, 0x10000, EVERY_ADDRESS),
                         words(0x00010537, 0x000000EF, 0x00550513, 0x00008067))

    def test_a_call_keeps_an_address_in_a_callee_saved_register(self):
        """lui s0,0x10; jal ra,+0x40; addi a0,s0,0x678: s0 survives the call, so the pair is still an address (0x10678,
        in the section [0x10000, 0x20000))."""
        code = words(0x00010437, 0x040000EF, 0x67840513)
        self.assertEqual(symbols.mask(code, 0x10000, symbols.NO_IMAGE._replace(sections=((0x10000, 0x20000),))),
                         words(0x00000437, 0x000000EF, 0x00040513))

    def test_a_low_half_reached_by_a_branch_is_masked(self):
        """auipc s0,0x47; ld a0,0x2b4(s0); beqz a0,+12; ld s0,0(sp); ret; ld a0,0x2b4(s0): the last load is reached
        only by the branch, on which s0 still holds the high half, so its low half is masked although the early
        return before it in address order restores s0.  Data that moved inside the page (0x374) masks equal."""
        def code(lo):
            load = 0x00043503 | lo << 20
            return words(0x00047417, load, 0x00050663, 0x00013403, 0x00008067, load)
        want = words(0x00000417, 0x00043503, 0x00050663, 0x00013403, 0x00008067, 0x00043503)
        self.assertEqual(symbols.mask(code(0x2B4), 0x5B640), want)
        self.assertEqual(symbols.mask(code(0x374), 0x5B640), want)

    def test_a_moved_function_with_a_low_half_on_a_branch_path_masks_equal(self):
        """__asan::HaveStackTraceBasedSuppressions() of libreac's fuzz_pcap asan build, 120 bytes at 0x5b640, at
        v1.9.0 and at libreac commit 848c6cb5d3f: only data addresses differ (4 low halves), one of them in
        `ld a0, lo(s0)` at 0x5b67c, which only the branch at 0x5b664 reaches, past the early return at 0x5b670."""
        v190 = bytes.fromhex(
            "130101ff2334110023308100177404000335442b630205049755fcff9385952fefd0d03d630c0500130510008330810003340100"
            "13010101678000000335442b9755fcff9385552e8330810003340100130101016fd0903a17b5fbff97e5fbff130575d3138695b2"
            "930560039306000013070000ef004126")
        head = bytes.fromhex(
            "130101ff23341100233081001774040003354437630205049755fcff9385952fefd0d03d630c0500130510008330810003340100"
            "1301010167800000033544379755fcff9385552e8330810003340100130101016fd0903a17b5fbff97e5fbff130575d4138695b3"
            "930560039306000013070000ef004126")
        # the exact column of each build's symbol fact
        self.assertEqual(hashlib.sha256(v190).hexdigest(),
                         "d31ee5de737a2e8cd8d2ae287ec8ceb2ba1b1d095daaf965db07c6c69cdc9e70")
        self.assertEqual(hashlib.sha256(head).hexdigest(),
                         "e11ed98273ff12cb22b0f96b868ac5ebf73ae4816c1df605e3cc4a921ff0f4a1")
        self.assertEqual(symbols.mask(v190, 0x5B640), symbols.mask(head, 0x5B640))

    def test_a_low_half_reached_by_a_loop_back_edge_is_masked(self):
        """j +8; ld a0,0x2b4(s0); auipc s0,0x47; bnez a1,-8; ret: the load comes before the auipc in address order,
        but only the loop's back edge reaches it, after the auipc, so its low half is masked."""
        code = words(0x0080006F, 0x2B443503, 0x00047417, 0xFE059CE3, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000),
                         words(0x0080006F, 0x00043503, 0x00000417, 0xFE059CE3, 0x00008067))

    def test_a_jump_with_no_proven_table_may_go_to_every_instruction(self):
        """auipc s1,0x47; jr a5; ld a0,0x2b4(s1); ret: the jump through a5 has no proven jump table, so it may go to
        every instruction; only it passes control to the load, and s1 holds the high half there, so the low half is
        masked."""
        code = words(0x00047497, 0x00078067, 0x2B44B503, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000), words(0x00000497, 0x00078067, 0x0004B503, 0x00008067))

    def test_a_target_of_a_jump_with_no_proven_table_meets_what_the_jump_held(self):
        """bnez a0,+12; auipc s0,0x19; j +12; ld s0,0(a1); jr a5; ld a0,16(s0); ret: the last load is the j's target
        too, and the jump through a5 may also go there, with s0 a loaded pointer: 16 is a field offset and 24 is a
        changed function.  a5 is an argument, neither a loaded pointer nor a number the code makes, so its target is
        unknown even when the build stores no label (and here also when it stores 0x10014, or with NO_IMAGE).  The same
        with jal ra (a call that ends what a0 held) before jr a5, and a0 as the base."""
        for code in (lambda lo: words(0x00051663, 0x00019417, 0x00C0006F, 0x0005B403, 0x00078067,
                                      0x00043503 | lo << 20, 0x00008067),
                     lambda lo: words(0x00061663, 0x00019517, 0x00C0006F, 0x100000EF, 0x00078067,
                                      0x00053583 | lo << 20, 0x00008067)):
            for image in (symbols.NO_IMAGE._replace(stored=()), symbols.NO_IMAGE._replace(stored=(0x10014,)),
                          symbols.NO_IMAGE):
                with self.subTest(code=code(16).hex(), stored=image.stored):
                    self.assertEqual(symbols.mask(code(16), 0x10000, image)[20:24], code(16)[20:24])
                    self.assertNotEqual(symbols.mask(code(16), 0x10000, image), symbols.mask(code(24), 0x10000, image))

    def test_a_jump_to_a_target_arithmetic_makes_may_go_anywhere(self):
        """With the build storing no label, a jump whose target arithmetic makes may still reach a label: bnez a0,+12;
        auipc s0,0x19; j +24; ld s0,0(a1); auipc a5,0; li a4,16; add a5,a5,a4; jr a5 (to 0x10020); ld a0,16(s0); ret
        keeps the 16 and is changed against 24; ld t1,0(a1); addi t1,t1,8 keeps the 0x50 of tail_call; and TABLE_CODE
        with its table in writable bytes ([0x1000, -0x7d0]: lw, then add of the table's address) keeps the 16 of
        ld a4,16(s0).  A target the code makes as auipc t1,0; addi t1,t1,0x14, 0x1001c, outside the function, is a tail
        call: the 0x50 of tail_call is masked.  Made as auipc a0,0; addi t1,a0,0x14 instead, a0 still holds 0x10008,
        an address of the function, which the tail call passes as an argument, so the 0x50 is kept."""
        none = symbols.NO_IMAGE._replace(stored=())
        def added(lo):
            return words(0x00051663, 0x00019417, 0x0180006F, 0x0005B403, 0x00000797, 0x01000713, 0x00E787B3,
                         0x00078067, 0x00043503 | lo << 20, 0x00008067)
        self.assertEqual(symbols.mask(added(16), 0x10000, none)[32:36], added(16)[32:36])
        self.assertNotEqual(symbols.mask(added(16), 0x10000, none), symbols.mask(added(24), 0x10000, none))
        stepped = words(0x00045597, 0x0505B583, 0x0005B303, 0x00830313, 0x00030067)
        self.assertEqual(symbols.mask(stepped, 0x10000, none)[4:8], stepped[4:8])
        table = {0x10800: struct.pack("<i", 0x1000), 0x10804: struct.pack("<i", -0x7D0)}
        writable = none._replace(data=lambda address, size: table.get(address))
        self.assertEqual(symbols.mask(words(*self.TABLE_CODE), 0x10000, writable)[48:52], struct.pack("<I", 0x01043703))
        made = words(0x00045597, 0x0505B583, 0x00000317, 0x01430313, 0x00030067)
        self.assertEqual(symbols.mask(made, 0x10000, none)[4:8], struct.pack("<I", 0x0005B583))
        passed = words(0x00045597, 0x0505B583, 0x00000517, 0x01450313, 0x00030067)
        self.assertEqual(symbols.mask(passed, 0x10000, none)[4:8], struct.pack("<I", 0x0505B583))

    # auipc a1,0x45; ld a1,lo(a1); ld t1,0(a1); mv a1,zero; jr t1: a tail call to a function whose address a global
    # holds (__asan_set_shadow_00 of the asan runtime, which tail-calls internal_memset)
    def tail_call(self, lo, before=()):
        return words(*before + (0x00045597, 0x0005B583 | lo << 20, 0x0005B303, 0x00000593, 0x00030067))

    def test_a_tail_call_through_a_register_leaves_the_function(self):
        """tail_call, in a build that stores no address of an instruction of it but its entry (0x10000): the jump
        through t1 has no jump table, so it is a tail call to a function's entry and leaves the function; the low half
        0x50 is masked, and the global that moved to 0x58 masks equal.  With NO_IMAGE (labels unknown) the jump may go
        to every instruction, the ld too, where a1 is no high half, so 0x50 is kept."""
        want = words(0x00000597, 0x0005B583, 0x0005B303, 0x00000593, 0x00030067)
        for stored in ((), (0x10000, 0x20000)):
            image = symbols.NO_IMAGE._replace(stored=stored)
            with self.subTest(stored=stored):
                self.assertEqual(symbols.mask(self.tail_call(0x50), 0x10000, image), want)
                self.assertEqual(symbols.mask(self.tail_call(0x58), 0x10000, image), want)
        self.assertEqual(symbols.mask(self.tail_call(0x50), 0x10000)[4:8], struct.pack("<I", 0x0505B583))

    def test_a_function_whose_label_the_program_takes_keeps_its_jump_conservative(self):
        """tail_call when the program may take the address of one of its instructions but the entry, so that the jump
        through t1 may be a computed goto: the build stores 0x10008 as data; or auipc a2,0; addi a2,a2,12 before it
        forms 0x1000c; or auipc a2,0; addi a2,a2,0x7ec forms 0x107ec, whose 32-bit word -0x7e0 leads to 0x1000c (a
        relative jump table).  The jump may go to every instruction, so the 0x50 is kept.  A word at 0x107ec that leads
        outside the function (0x100000) takes no label, and the 0x50 is masked."""
        table = {0x107EC: struct.pack("<i", -0x7E0)}
        relative = symbols.NO_IMAGE._replace(stored=(), data=lambda address, size: table.get(address))
        outside = symbols.NO_IMAGE._replace(stored=(), data=lambda address, size: struct.pack("<i", 0x100000))
        for code, image, low in ((self.tail_call(0x50), symbols.NO_IMAGE._replace(stored=(0x10008,)), 0x0505B583),
                                 (self.tail_call(0x50, (0x00000617, 0x00C60613)), symbols.NO_IMAGE._replace(stored=()),
                                  0x0505B583),
                                 (self.tail_call(0x50, (0x00000617, 0x7EC60613)), relative, 0x0505B583),
                                 (self.tail_call(0x50, (0x00000617, 0x7EC60613)), outside, 0x0005B583)):
            with self.subTest(code=code.hex(), stored=image.stored):
                got = struct.unpack("<%dI" % (len(code) // 4), symbols.mask(code, 0x10000, image))
                self.assertEqual(got[-4], low)

    def test_a_compiled_computed_goto_keeps_its_jump_conservative(self):
        """computed_goto_global.elf (fixtures/elf/README.md): GCC 13.3 compiles `goto *saved` with saved = &&start +
        offsets[which], the offsets label differences (0 and 60, in .rodata), as lla a3,.L2 (the entry, auipc a3,0;
        addi a3,a3,-0x1c); add; sd; ld; jr a5, to 0x1003c for which = 1, inside the function.  The build stores no
        address of it, and the target is a loaded value, but the function forms its entry for an add, not to call it
        or jump to it, so the jump may go to every instruction: there a5, a3 and a4 hold no high half, and the low
        halves of lla a5,offsets (0x3c), lla a3,.L2 (-0x1c) and lla a4,saved (0x34) are kept."""
        binary = elf.Elf(os.path.join(ELF, "computed_goto_global.elf"))
        self.assertEqual(binary.sha256, "d24e6b3307f5b9a71e19839d154a8e50a184dabd17fc7e23b2c496568e5f0c5d")
        functions = binary.symbols()
        image = symbols.build_image(binary, binary.sections(), symbols.noreturn_addresses(functions))
        f = next(s for s in functions if s.name == "computed_goto_global")
        offsets = next(s for s in functions if s.name == "offsets.0")
        self.assertEqual((f.address, f.size, image.stored), (0x10000, 68, ()))
        self.assertEqual(struct.unpack("<qq", binary.contents(offsets.address, offsets.size)), (0, 60))
        code = binary.contents(f.address, f.size)
        got, kept = struct.unpack("<17I", symbols.mask(code, f.address, image)), struct.unpack("<17I", code)
        self.assertEqual((kept[4], kept[8], kept[10], kept[14]), (0x03C78793, 0xFE468693, 0x03470713, 0x00078067))
        self.assertEqual((got[4], got[8], got[10]), (kept[4], kept[8], kept[10]))

    def test_a_label_address_spilled_and_reloaded_keeps_the_jump_conservative(self):
        """bnez a0,+12; auipc s0,0x19; j +32; ld s0,0(a1); auipc a5,0; li a4,24; add a5,a5,a4 (or addi a5,a5,24;
        mv a5,a5); sd a5,0(sp); ld a5,0(sp); jr a5 (to 0x10028); ld a0,16(s0); ret: the jump's target is a reloaded
        value, but the function forms an address of itself, 0x10010 for an add or 0x10028 for an addi, so the jump may
        go to the last load, where s0 is a loaded pointer: the 16 is kept, and 24 is a changed function."""
        none = symbols.NO_IMAGE._replace(stored=())
        for make in ((0x01800713, 0x00E787B3), (0x01878793, 0x00078793)):
            def code(lo):
                return words(0x00051663, 0x00019417, 0x0200006F, 0x0005B403, 0x00000797, *make, 0x00F13023, 0x00013783,
                             0x00078067, 0x00043503 | lo << 20, 0x00008067)
            with self.subTest(make=[hex(w) for w in make]):
                self.assertEqual(symbols.mask(code(16), 0x10000, none)[40:44], code(16)[40:44])
                self.assertNotEqual(symbols.mask(code(16), 0x10000, none), symbols.mask(code(24), 0x10000, none))

    def test_a_compiled_computed_goto_with_a_biased_label_keeps_its_jump_conservative(self):
        """computed_goto_biased.elf (fixtures/elf/README.md): GCC 13.3 compiles encoded = &&start + 8192 and
        goto *(encoded - 8192 + offsets[which]) as lla a5,.L2+8192; sd a5,0(a4); ...; ld a5,0(a4); lui a6,2;
        sub a5,a5,a6; add a5,a5,a3; sd; ld; jr a5, to 0x1004c for which = 1, inside the function.  The value it forms is
        8 KiB past the function, but it stores it and takes it into arithmetic, so the jump may go to every
        instruction: there a4, a5 and a3 hold no high half, and the low halves of lla a4,encoded (0x64),
        lla a5,.L2+8192 (-0xc) and lla a3,offsets (0x38) are kept."""
        binary = elf.Elf(os.path.join(ELF, "computed_goto_biased.elf"))
        self.assertEqual(binary.sha256, "f80852c101dfc40f02e3442e4faaa88c0c58cb6d3b1d171df4306e7bebff8b29")
        functions = binary.symbols()
        image = symbols.build_image(binary, binary.sections(), symbols.noreturn_addresses(functions))
        f = next(s for s in functions if s.name == "computed_goto_biased")
        offsets = next(s for s in functions if s.name == "offsets.0")
        self.assertEqual((f.address, f.size, image.stored), (0x10000, 84, ()))
        self.assertEqual(struct.unpack("<qq", binary.contents(offsets.address, offsets.size)), (0, 76))
        code = binary.contents(f.address, f.size)
        got, kept = struct.unpack("<21I", symbols.mask(code, f.address, image)), struct.unpack("<21I", code)
        self.assertEqual((kept[2], kept[4], kept[9], kept[18]), (0x06470713, 0xFF478793, 0x03868693, 0x00078067))
        self.assertEqual((got[2], got[4], got[9]), (kept[2], kept[4], kept[9]))

    def test_a_label_biased_far_from_the_function_keeps_the_jump_conservative(self):
        """bnez a0,+12; auipc s0,0x19; j +36; ld s0,0(a1); auipc a5,2 (0x12010, 8 KiB past the function);
        lui a4,-2; addi a4,a4,28; add a5,a5,a4; sd a5,0(sp); ld a5,0(sp); jr a5 (to 0x1002c); ld a0,16(s0); ret: the
        value of the auipc is far from the function, but the add takes it into arithmetic, so the jump may go to the
        last load, where s0 is a loaded pointer: the 16 is kept, and 24 is a changed function."""
        none = symbols.NO_IMAGE._replace(stored=())
        def code(lo):
            return words(0x00051663, 0x00019417, 0x0240006F, 0x0005B403, 0x00002797, 0xFFFFE737, 0x01C70713,
                         0x00E787B3, 0x00F13023, 0x00013783, 0x00078067, 0x00043503 | lo << 20, 0x00008067)
        self.assertEqual(symbols.mask(code(16), 0x10000, none)[44:48], code(16)[44:48])
        self.assertNotEqual(symbols.mask(code(16), 0x10000, none), symbols.mask(code(24), 0x10000, none))

    def test_a_value_an_auipc_makes_that_only_addresses_memory_keeps_the_tail_call(self):
        """tail_call: auipc a1,0x45 makes 0x55000, which only ld a1,0x50(a1) takes, as a base, so the jump through t1
        is still a tail call and the 0x50 is masked.  With slli a2,a1,1, or sd a1,0(sp), after the auipc instead, the
        value goes into arithmetic or memory, whatever its distance from the function, and the 0x50 is kept."""
        none = symbols.NO_IMAGE._replace(stored=())
        for after, low in (((), 0x0005B583), ((0x00159613,), 0x0505B583), ((0x00B13023,), 0x0505B583)):
            with self.subTest(after=[hex(w) for w in after]):
                code = words(0x00045597, *after, 0x0505B583, 0x0005B303, 0x00000593, 0x00030067)
                self.assertEqual(struct.unpack("<%dI" % (len(after) + 5), symbols.mask(code, 0x10000, none))[-4], low)

    def test_a_function_that_forms_its_entry_to_call_it_or_jump_to_it_keeps_its_tail_call(self):
        """tail_call after auipc ra,0; jalr ra,0(ra) (a call of itself, recursion) or after beqz a0,+12; auipc t2,0;
        jalr x0,-4(t2) (a jump to its entry, `tail` of itself): forming the entry to call it or jump to it takes no
        label, so the jump through t1 is still a tail call and the 0x50 is masked.  After auipc a2,0; addi a2,a2,0,
        the entry formed for anything else (GNU C's anchor of label differences), the 0x50 is kept."""
        none = symbols.NO_IMAGE._replace(stored=())
        for before, low in (((0x00000097, 0x000080E7), 0x0005B583), ((0x00050663, 0x00000397, 0xFFC38067), 0x0005B583),
                            ((0x00000617, 0x00060613), 0x0505B583)):
            with self.subTest(before=[hex(w) for w in before]):
                masked = symbols.mask(self.tail_call(0x50, before), 0x10000, none)
                self.assertEqual(struct.unpack("<%dI" % (len(before) + 5), masked)[-4], low)

    def test_code_addresses_are_the_aligned_words_inside_text(self):
        """code_addresses keeps the 4-aligned 32-bit words at 4-aligned addresses that are 4-aligned addresses in
        [lo, hi): of a section at 0x20002, the words at 0x20004 and 0x2000c; 0x10010 (the low word of a 64-bit
        pointer) and 0x10000 count, 0x10002 (unaligned value), 0x0ffff (outside) and the word at 0x20002 (unaligned
        address) do not; a section with no bytes (.bss) holds none, and the unwind tables (.eh_frame, .eh_frame_hdr,
        .gcc_except_table), whose words are offsets and function starts, are not read."""
        data = struct.pack("<H", 0) + struct.pack("<I", 0x10010) + struct.pack("<I", 0) + struct.pack("<III", 0x10000,
                                                                                                     0x10002, 0xFFFF)
        sections = [elf.Section(".data", 1, 0x20002, len(data), data), elf.Section(".bss", 8, 0x30000, 64, None),
                    elf.Section(".x", 1, 0x20002, 4, struct.pack("<I", 0x10004))]
        sections += [elf.Section(name, 1, 0x40000, 4, struct.pack("<I", 0x10008)) for name in symbols.UNWIND]
        self.assertEqual(symbols.code_addresses(sections, 0x10000, 0x10020), (0x10000, 0x10010))

    @staticmethod
    def eh_frame(base, fdes):
        """The bytes of an .eh_frame at base with a CIE of augmentation "zLR" (an LSDA, pointers pcrel sdata4), a CIE
        of "zR", and an FDE of each (code start, size, with an LSDA) of fdes, then a terminator."""
        def entry(body):
            body += b"\0" * (-(len(body) + 4) % 4)   # DW_CFA_nop
            return struct.pack("<I", len(body)) + body
        data = entry(struct.pack("<IB", 0, 1) + b"zLR\0" + bytes([1, 0x78, 1, 2, 0x1B, 0x1B]))
        plain = len(data)   # the offset of the "zR" CIE; the "zLR" one is at 0
        data += entry(struct.pack("<IB", 0, 1) + b"zR\0" + bytes([1, 0x78, 1, 1, 0x1B]))
        for start, size, lsda in fdes:
            here = len(data)   # the CIE pointer, at here + 4, is the distance back to its CIE
            body = struct.pack("<Iii", here + 4 - (0 if lsda else plain), start - (base + here + 8), size)
            data += entry(body + (bytes([4]) + struct.pack("<i", 0x100) if lsda else bytes([0])))
        return data + struct.pack("<I", 0)

    def test_a_function_with_landing_pads_holds_no_high_half(self):
        """An FDE whose CIE has an 'L' augmentation (an LSDA) covers [0x10000, 0x10014): the unwinder may enter that
        code at its landing pads with the registers of the call that threw, so in auipc a1,0x45; ld a1,0x50(a1); ret
        at 0x10000 the 0x50 is kept.  An FDE of a CIE with no 'L' (at 0x20000) makes no landing pads, and with no
        landing pad there the 0x50 is masked.  An .eh_frame that cannot be read gives every function landing pads."""
        data = self.eh_frame(0x30000, ((0x10000, 0x14, True), (0x20000, 0x10, False)))
        self.assertEqual(symbols.landing_ranges([elf.Section(".eh_frame", 1, 0x30000, len(data), data)]),
                         ((0x10000, 0x10014),))
        bad = data.replace(b"zLR\0", b"zLX\0")
        warned = []
        self.assertEqual(symbols.landing_ranges([elf.Section(".eh_frame", 1, 0x30000, len(bad), bad)],
                                                warn=warned.append),
                         ((0, 1 << 64),))
        self.assertEqual(len(warned), 1)
        self.assertIn(".eh_frame at 0x30000 cannot be read", warned[0])
        self.assertIn("low-half masking is disabled", warned[0])
        code = words(0x00045597, 0x0505B583, 0x00008067)
        for landing, low in ((((0x10000, 0x10014),), 0x0505B583), (((0x20000, 0x20010),), 0x0005B583), ((), 0x0005B583),
                             (((0, 1 << 64),), 0x0505B583)):
            with self.subTest(landing=landing):
                got = symbols.mask(code, 0x10000, symbols.NO_IMAGE._replace(landing=landing))
                self.assertEqual(struct.unpack("<3I", got)[1], low)

    def test_eh_frame_cies_of_versions_1_3_and_4_are_read_and_others_are_not(self):
        """A "zLR" CIE of version 1, 3 (a uleb128 return address register) or 4 (address and segment selector sizes
        before the alignment factors), with absolute 64-bit FDE pointers, gives the landing range [0x10000, 0x10020).
        Version 2, three bytes, a record longer than the section and bytes after the terminator are read as every
        function having landing pads."""
        def entry(body):
            body += b"\0" * (-(len(body) + 4) % 4)
            return struct.pack("<I", len(body)) + body

        def frames(version):
            cie = entry(struct.pack("<IB", 0, version) + b"zLR\0" + (bytes([8, 0]) if version == 4 else b"")
                        + bytes([1, 0x78, 1, 2, 0x1B, 0x00]))
            fde = entry(struct.pack("<IQQ", len(cie) + 4, 0x10000, 0x20) + bytes([4]) + struct.pack("<I", 0x100))
            return cie + fde + struct.pack("<I", 0)

        def landing(data):
            return symbols.landing_ranges([elf.Section(".eh_frame", 1, 0x30000, len(data), data)])
        for version in (1, 3, 4):
            with self.subTest(version=version):
                self.assertEqual(landing(frames(version)), ((0x10000, 0x10020),))
        for bad in (frames(2), b"\x01\x02\x03", frames(1)[:-12], frames(1) + b"\x01\0\0\0"):
            with self.subTest(bad=bad.hex()):
                self.assertEqual(landing(bad), ((0, 1 << 64),))

    # ld s0,0(a1); bnez a3,+40; then LLVM's jump table code: li a5,1; bltu a5,a0,+44; slli a0,a0,2; auipc a2,0;
    # addi a2,a2,0x7ec; add a0,a0,a2; lw a0,0(a0); add a0,a0,a2; jr a0; then the bnez's target auipc s0,0x19 and
    # ld a4,16(s0) at 0x30; ret at 0x34 and 0x38.  The table is at 0x10014 + 0x7ec = 0x10800, two entries.
    TABLE_CODE = (0x0005B403, 0x02069463, 0x00100793, 0x02A7E663, 0x00251513, 0x00000617, 0x7EC60613, 0x00C50533,
                  0x00052503, 0x00C50533, 0x00050067, 0x00019417, 0x01043703, 0x00008067, 0x00008067)

    def table_mask(self, entries):
        """symbols.mask of TABLE_CODE at 0x10000 with the table's entries (offsets from 0x10800) in bytes the program
        cannot write, or, for None, in bytes it can (Elf.constant gives None)."""
        table = {} if entries is None else {0x10800 + 4 * k: struct.pack("<i", e) for k, e in enumerate(entries)}
        return symbols.mask(words(*self.TABLE_CODE), 0x10000,
                            symbols.NO_IMAGE._replace(constant=lambda address, size: table.get(address)))

    def test_a_proven_jump_table_goes_only_to_its_entries(self):
        """TABLE_CODE with both entries leading to the ret at 0x34 (0x10834 - 0x10800 = -0x7cc), or one to an address
        outside the function: the jump goes to no other instruction, so ld a4,16(s0), which only the path through
        auipc s0 reaches, is masked."""
        want = words(0x0005B403, 0x02069463, 0x00100793, 0x02A7E663, 0x00251513, 0x00000617, 0x00060613, 0x00C50533,
                     0x00052503, 0x00C50533, 0x00050067, 0x00000417, 0x00043703, 0x00008067, 0x00008067)
        for entries in ((-0x7CC, -0x7CC), (-0x7CC, 0x1000)):
            with self.subTest(entries=entries):
                self.assertEqual(self.table_mask(entries), want)

    def test_a_jump_table_entry_or_a_writable_table_reaches_the_load(self):
        """TABLE_CODE with an entry leading to ld a4,16(s0) at 0x30 (-0x7d0), where s0 is then the loaded pointer, or
        with its table in bytes the program can write: 16 is a field offset and kept.  With the table proven, the low
        half of the table's own address (addi a2,a2,0x7ec) is masked; with a writable table the jump may go to every
        instruction, the addi too, where a2 is no high half (the addi wrote it), so the 0x7ec is kept."""
        for entries, addi in (((-0x7D0, -0x7CC), 0x00060613), (None, 0x7EC60613)):
            with self.subTest(entries=entries):
                got = struct.unpack("<15I", self.table_mask(entries))
                self.assertEqual((got[6], got[11], got[12]), (addi, 0x00000417, 0x01043703))

    # auipc s3,0; addi s3,s3,0x7ec (the table, 0x107ec); li s1,1; ld s0,0(a1); then a loop at 0x10: bnez a3,+28;
    # bltu s1,a0,+36; slli a0,a0,2; add a0,a0,s3; lw a0,0(a0); add a0,a0,s3; jr a0; then the bnez's target auipc s0,0x19
    # at 0x2c, ld a4,16(s0), j -36 back to the loop; ret at 0x38: the table's address and its bound are set before the
    # loop, as LLVM hoists them (FormattedStackTracePrinter::RenderFrame of the asan runtime)
    LOOP_TABLE = (0x00000997, 0x7EC98993, 0x00100493, 0x0005B403, 0x00069E63, 0x02A4E263, 0x00251513, 0x01350533,
                  0x00052503, 0x01350533, 0x00050067, 0x00019417, 0x01043703, 0xFDDFF06F, 0x00008067)

    def test_a_jump_table_whose_address_and_bound_are_set_before_a_loop_is_proven(self):
        """LOOP_TABLE with both entries leading to the ret (0x10038 - 0x107ec = -0x7b4): s3 and s1 hold the table's
        address and 1 on every path to the loop, so the table is proven, the jump goes only to the ret, and both the
        table's low half and ld a4,16(s0) are masked.  With li s1,2 instead of the load, s1 holds 1 on one path to
        the bltu and 2 on the other, so no bound is proven, the jump may go to every instruction, and the table's
        low half (0x7ec) is kept."""
        table = {0x107EC: struct.pack("<i", -0x7B4), 0x107F0: struct.pack("<i", -0x7B4)}
        image = symbols.NO_IMAGE._replace(constant=lambda address, size: table.get(address))
        got = struct.unpack("<15I", symbols.mask(words(*self.LOOP_TABLE), 0x10000, image))
        self.assertEqual((got[1], got[12]), (0x00098993, 0x00043703))
        code = list(self.LOOP_TABLE)
        code[12] = 0x00200493   # li s1,2
        self.assertEqual(struct.unpack("<15I", symbols.mask(words(*code), 0x10000, image))[1], 0x7EC98993)

    def test_a_lui_that_reaches_no_base_is_kept(self):
        """beqz a0,+12; lui a7,0x1; ret; addi a7,a7,1; ret: no path takes the lui to the addi (the return is between
        them), so the two make no address, and a changed 1 is a changed function."""
        code = words(0x00050663, 0x000018B7, 0x00008067, 0x00188893, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000, EVERY_ADDRESS), code)

    def test_a_lui_on_one_path_to_a_base_is_kept(self):
        """ld s0,0x30(s0); lui a0,0x1; bltu a0,s0,+8; lui s0,0x1; addi a0,s0,-1; ret: s0 is the page size on one path
        to the addi and a loaded size on the other, so it holds no high half on every path, and the lui and the -1
        of the page mask are kept (__malloc_alloc_meta of musl).  A changed -1 is a changed function."""
        code = words(0x03043403, 0x00001537, 0x00856463, 0x00001437, 0xFFF40513, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000, EVERY_ADDRESS), code)

    def test_a_lui_on_a_loop_back_edge_only_is_kept(self):
        """addi a5,zero,9; mv a6,a5; lui a5,0x800; beq a6,a5,-8; ret: the mv (addi a6,a5,0) takes a5 as 9 on the
        way in and as the lui only on the back edge, so the lui is a number and kept
        (__sanitizer::StackStore::BlockInfo::Pack of the asan runtime)."""
        code = words(0x00900793, 0x00078813, 0x008007B7, 0xFEF80CE3, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000, EVERY_ADDRESS), code)

    def test_a_lui_and_addi_that_make_a_number_are_kept(self):
        """bnez a0,+12; lui a0,0x40000; j +8; lui a0,0x48000; addi a0,a0,4; ret (__sanitizer::MaybeInstallSigaction of
        the asan runtime): both paths to the addi put a lui in a0, but 0x40000004 and 0x48000004 are sigaction flags,
        in no section of the build (here [0x10000, 0x1d000)), so the luis and the addi are kept, and lui a0,0x50000
        instead of 0x40000 is a changed function."""
        def code(flags):
            return words(0x00051663, flags << 12 | 0x537, 0x0080006F, 0x48000537, 0x00450513, 0x00008067)
        image = symbols.NO_IMAGE._replace(sections=((0x10000, 0x1D000),))
        self.assertEqual(symbols.mask(code(0x40000), 0x10000, image), code(0x40000))
        self.assertNotEqual(symbols.mask(code(0x40000), 0x10000, image), symbols.mask(code(0x50000), 0x10000, image))

    def test_an_auipc_high_half_spilled_to_a_frame_slot_is_reloaded(self):
        """auipc a1,0x19; sd a1,0x40(s1); sd s6,0x618(a1); sd s3,0(s2); jal ra,+0x100; ld a1,0x40(s1);
        ld a3,0x618(a1); ret: the compiler spills the high half to a frame slot and reloads it after a store through
        another register and a call, so the reloaded a1 holds it and 0x618 is masked, and the data that moved by 0xa0
        (0x6b8) masks equal (LLVMFuzzerTestOneInput of libreac's fuzz_pcap asan build at v1.8.0 and v1.9.0).  A raw
        auipc result is never a C value, so no C pointer may write its spill slot."""
        def code(lo):
            store = 0x0165B023 | (lo >> 5) << 25 | (lo & 0x1F) << 7
            return words(0x00019597, 0x04B4B023, store, 0x01393023, 0x100000EF, 0x0404B583, 0x0005B683 | lo << 20,
                         0x00008067)
        want = words(0x00000597, 0x04B4B023, 0x0165B023, 0x01393023, 0x000000EF, 0x0404B583, 0x0005B683, 0x00008067)
        self.assertEqual(code(0x618)[8:12], struct.pack("<I", 0x6165BC23))   # sd s6,0x618(a1)
        for lo in (0x618, 0x6B8):
            with self.subTest(lo=hex(lo)):
                self.assertEqual(symbols.mask(code(lo), 0x10000), want)

    def test_a_lui_spilled_to_a_frame_slot_is_not_carried(self):
        """lui a1,0x19; sd a1,0x40(s1); ld a1,0x40(s1); ld a3,0x618(a1); ret: a lui's value may be a C number kept in
        a variable, which a pointer may change, so no slot carries it, and the lui and the 0x618 are kept."""
        code = words(0x000195B7, 0x04B4B023, 0x0404B583, 0x6185B683, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000, EVERY_ADDRESS), code)

    def test_a_frame_slot_a_store_writes_over_holds_no_high_half(self):
        """auipc a1,0x19; sd a1,0x40(s1); then sd a2,0x40(s1), or sw a2,0x44(s1) over half of the slot; then
        ld a1,0x40(s1); ld a3,0x618(a1); ret: the reload is not the spilled high half, so the 0x618 is kept."""
        for store in (0x04C4B023, 0x04C4A223):
            with self.subTest(store=hex(store)):
                code = words(0x00019597, 0x04B4B023, store, 0x0404B583, 0x6185B683, 0x00008067)
                self.assertEqual(symbols.mask(code, 0x10000),
                                 words(0x00000597, 0x04B4B023, store, 0x0404B583, 0x6185B683, 0x00008067))

    def test_a_frame_slot_ends_when_its_base_register_is_written(self):
        """auipc a1,0x19; sd a1,0x40(s1); addi s1,s1,16; ld a1,0x40(s1); ld a3,0x618(a1); ret: once s1 moves,
        0x40(s1) is another slot, so the reload holds no high half and the 0x618 is kept."""
        code = words(0x00019597, 0x04B4B023, 0x01048493, 0x0404B583, 0x6185B683, 0x00008067)
        self.assertEqual(symbols.mask(code, 0x10000),
                         words(0x00000597, 0x04B4B023, 0x01048493, 0x0404B583, 0x6185B683, 0x00008067))

    # bnez a0,+0x1c; auipc a1,0x19; sd a1,0x40(s1); bnez a2,+0x18; ld a1,0x40(s1); ld a3,0x618(a1); ret; then two
    # ASan slow paths at 0x1c and 0x24, each blt a4,a5 back to its check and jal ra,0x10100 (a report call): the first
    # one runs into the second, which only the check after the spill branches to (LLVMFuzzerTestOneInput of libreac's
    # fuzz_pcap asan build)
    SLOW_PATHS = (0x00051E63, 0x00019597, 0x04B4B023, 0x00061C63, 0x0404B583, 0x6185B683, 0x00008067, 0xFEF744E3,
                  0x0E0000EF, 0xFEF746E3, 0x0D8000EF)

    def test_a_call_that_never_returns_does_not_fall_through(self):
        """SLOW_PATHS with a global or weak report function NORETURN names at 0x10100: the first report call never
        returns, so the reload at 0x10 holds the spilled high half on every path to it, and the 0x618 is masked."""
        want = words(0x00051E63, 0x00000597, 0x04B4B023, 0x00061C63, 0x0404B583, 0x0005B683, 0x00008067, 0xFEF744E3,
                     0x000000EF, 0xFEF746E3, 0x000000EF)
        for name, binding in (("__asan_report_load8", "global"), ("__asan_report_exp_store_n", "global"),
                              ("__ubsan_handle_add_overflow_abort", "global"), ("abort", "global"),
                              ("exit", "global"), ("_Exit", "weak"), ("__assert_fail", "global")):
            with self.subTest(name=name):
                dead = symbols.noreturn_addresses([elf.Symbol(name, "func", 0x10100, 16, binding)])
                self.assertEqual(dead, {0x10100})
                self.assertEqual(symbols.mask(words(*self.SLOW_PATHS), 0x10000,
                                              symbols.NO_IMAGE._replace(noreturn=dead)), want)

    def test_a_call_that_may_return_falls_through(self):
        """SLOW_PATHS with a function at 0x10100 that NORETURN does not name, or names but that is local: an ASan report
        that returns (*_noabort), a UBSan handler that returns, and a program's own static exit or abort.  The first
        report call falls through into the second slow path on a path where nothing was spilled, so the reload holds
        no high half and the 0x618 is kept."""
        want = words(0x00051E63, 0x00000597, 0x04B4B023, 0x00061C63, 0x0404B583, 0x6185B683, 0x00008067, 0xFEF744E3,
                     0x000000EF, 0xFEF746E3, 0x000000EF)
        for name, binding in (("__asan_report_load8_noabort", "global"), ("__ubsan_handle_add_overflow", "global"),
                              ("free", "global"), ("exit_group_helper", "global"), ("exit", "local"),
                              ("abort", "local"), ("__asan_report_load8", "local")):
            with self.subTest(name=name, binding=binding):
                dead = symbols.noreturn_addresses([elf.Symbol(name, "func", 0x10100, 16, binding)])
                self.assertEqual(dead, frozenset())
                self.assertEqual(symbols.mask(words(*self.SLOW_PATHS), 0x10000,
                                              symbols.NO_IMAGE._replace(noreturn=dead)), want)

    def test_a_symbol_keeps_its_binding(self):
        """f, g, h and _start of the fixture are global (llvm-readelf -s two.unstripped); with f's st_info made local
        (its Elf64_Sym found by its value 0x112a8 and size 108), f reads as local and the others stay global."""
        self.assertEqual({s.name: s.binding for s in elf.Elf(UNSTRIPPED).symbols()},
                         {"_start": "global", "f": "global", "g": "global", "h": "global", "seed": "global",
                          "counter": "global"})
        data = bytearray(elf.Elf(UNSTRIPPED).data)
        value = data.find(struct.pack("<QQ", 0x112a8, 108))
        self.assertEqual(data.count(struct.pack("<QQ", 0x112a8, 108)), 1)
        self.assertEqual(data[value - 4], 0x12)   # st_info: STB_GLOBAL << 4 | STT_FUNC
        data[value - 4] = 0x02                    # STB_LOCAL << 4 | STT_FUNC
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "two.unstripped")
            with open(path, "wb") as f:
                f.write(data)
            self.assertEqual({s.name: s.binding for s in elf.Elf(path).symbols() if s.kind == "func"},
                             {"_start": "global", "f": "local", "g": "global", "h": "global"})

    def test_a_load_from_a_register_no_auipc_set_keeps_its_offset(self):
        """ld s0,0(sp); ld a0,0x10(s0); ret: s0 holds no address high half, so the 0x10 is a field offset, and
        0x18 is a changed function."""
        self.assertEqual(symbols.mask(words(0x00013403, 0x01043503, 0x00008067), 0x10000),
                         words(0x00013403, 0x01043503, 0x00008067))

    def test_exact_and_masked_hash_the_function_bytes(self):
        """exact is the SHA-256 of the function's bytes in the stripped binary, masked that of symbols.mask of
        them; f calls h with a jal that leaves f, so the two differ."""
        bare = elf.Elf(STRIPPED)
        f = fixture()["f"]
        code = bare.text[f.address - bare.text_addr:f.address - bare.text_addr + f.size]
        self.assertEqual(f.exact, hashlib.sha256(code).hexdigest())
        self.assertEqual(f.masked, hashlib.sha256(symbols.mask(code, f.address)).hexdigest())
        self.assertNotEqual(f.exact, f.masked)

    def test_lines_come_from_the_line_table(self):
        """two.lines.txt gives f the rows from 0x112a8 to its end_sequence at 0x11314, lines 12 to 20 of two.c (a
        line 0 row is code of no line), and g and h one line, 25."""
        syms = fixture()
        self.assertEqual((syms["f"].lines, syms["g"].lines, syms["h"].lines),
                         ("two.c:12-20", "two.c:25-25", "two.c:25-25"))

    def test_a_function_in_two_files_has_a_range_for_each(self):
        """A function with code from two files has one range per file, in the order of their first row; a file in
        a folder under the compilation directory is named from there."""
        text = ("debug_line[0x00000000]\n"
                "         version: 5\n"
                'include_directories[  0] = "/src"\n'
                'include_directories[  1] = "/src/inc"\n'
                "file_names[  0]:\n"
                '           name: "two.c"\n'
                "      dir_index: 0\n"
                "file_names[  1]:\n"
                '           name: "two.h"\n'
                "      dir_index: 1\n"
                "Address            Line   Column File   ISA Discriminator OpIndex Flags\n"
                "------------------ ------ ------ ------ --- ------------- ------- -------------\n"
                "0x00000000000112a8      7      0      0   0             0       0  is_stmt\n"
                "0x00000000000112bc      4      5      1   0             0       0  is_stmt\n"
                "0x00000000000112c8      3      5      1   0             0       0  is_stmt\n"
                "0x00000000000112d8      9      5      0   0             0       0  is_stmt\n"
                "0x0000000000011314      9      5      0   0             0       0  end_sequence\n")
        self.assertEqual(fixture(text)["f"].lines, "two.c:7-9,inc/two.h:3-4")

    def test_a_function_the_line_table_misses_has_no_lines(self):
        self.assertEqual({s.lines for s in fixture("").values()}, {"-"})

    def test_the_fact_round_trips(self):
        """load(write(...)) gives back the stripped binary's sha256 and every row as read."""
        syms = symbols.read(UNSTRIPPED, STRIPPED, lines_text(), STRIPPED_SHA)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "symbols", "plain.tsv")
            symbols.write(path, syms, STRIPPED_SHA)
            with open(path, encoding="utf-8") as f:
                self.assertEqual(f.readline(), "# oss-fuzz-theorems/symbols/1 sha256=%s\n" % STRIPPED_SHA)
            self.assertEqual(symbols.load(path), (STRIPPED_SHA, syms))

    def test_a_file_that_is_no_64_bit_little_endian_elf_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            for name, data in (("text", b"not an ELF file at all, but long enough for a header" * 2),
                               ("elf32", b"\x7fELF\x01\x01\x01" + bytes(57)),
                               ("big-endian", b"\x7fELF\x02\x02\x01" + bytes(57))):
                with self.subTest(name=name):
                    path = os.path.join(d, name)
                    with open(path, "wb") as f:
                        f.write(data)
                    self.assertRaises(ValueError, elf.Elf, path)

    def test_a_stripped_file_has_no_symbols_to_read(self):
        """The stripped twin has no .symtab: reading its functions is refused, not an empty list."""
        self.assertRaisesRegex(ValueError, "symbol table", elf.Elf(STRIPPED).symbols)

    def test_the_symbol_tools_are_not_the_checker(self):
        """keys.NOT_THE_CHECKER names elf.py and symbols.py, so a change to them re-checks no fuzz target; that
        holds only while a check opens neither, so oft.check, with oft.facts, imports neither."""
        self.assertTrue(keys.not_the_checker("tools/oft/symbols.py"))
        self.assertTrue(keys.not_the_checker("tools/oft/elf.py"))
        tools = os.path.dirname(os.path.dirname(os.path.abspath(symbols.__file__)))
        done = subprocess.run([sys.executable, "-c", "import sys, oft.check, oft.facts, oft.fetch; "
                               "print(sorted(m for m in sys.modules if m in ('oft.elf', 'oft.symbols')))"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=tools))
        self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "[]\n", ""))


# auipc a1,0x45; ld a1,0x50(a1); ld t1,0(a1); li a1,0; jr t1 after the words of before: Symbols.tail_call
def tail_call(before):
    return words(*before + (0x00045597, 0x0505B583, 0x0005B303, 0x00000593, 0x00030067))


KEPT, MASKED = 0x0505B583, 0x0005B583


class LoadedTailCalls(unittest.TestCase):
    """A function whose every jump through a register with no proven table is a tail call through a pointer loaded
    with nothing added keeps its tail calls although a value an auipc or a lui made goes into arithmetic, unless the
    function stores such a value, or hands one on after arithmetic moved it (moves it to an FP register, passes it to
    a call or a tail call, gives it back), or takes a label otherwise (Symbols holds those rules); then every jump
    through a register may go to every instruction, as before, and the 0x50 of tail_call's ld a1,0x50(a1) is kept."""

    def low(self, before):
        masked = symbols.mask(tail_call(before), 0x10000, symbols.NO_IMAGE._replace(stored=()))
        return struct.unpack("<%dI" % (len(before) + 5), masked)[-4]

    def test_a_moved_value_the_function_hands_on_keeps_the_jump_conservative(self):
        """auipc a3,0x45 (0x55004, far from the function), slli a2,a3,1, then: sd a2,0(sp); li a2,0 (stored) /
        fmv.d.x fa0,a2; li a2,0 (to an FP register) / jal ra,+0x1000; li a2,0 (passed to a call) / nothing more
        (passed by the tail call in a2).  And beqz a0,+16; auipc a3,0x45; slli a0,a3,1; ret before tail_call (given
        back).  Each may carry a label of the function out, so the 0x50 is kept."""
        for before in ((0x00045697, 0x00169613, 0x00C13023, 0x00000613),
                       (0x00045697, 0x00169613, 0xF2060553, 0x00000613),
                       (0x00045697, 0x00169613, 0x000010EF, 0x00000613),
                       (0x00045697, 0x00169613),
                       (0x00050863, 0x00045697, 0x00169513, 0x00008067)):
            with self.subTest(before=[hex(w) for w in before]):
                self.assertEqual(self.low(before), KEPT)

    def test_a_value_stored_as_it_is_keeps_the_jump_conservative(self):
        """auipc a3,0x45; sd a3,0(sp): a label biased by any amount may be stored as it is and moved into the label by
        other code, so the 0x50 is kept.  bnez a0,+12; auipc s0,0x19; j +28; ld s0,0(a1); lla a5,.L+8192 (auipc
        a5,2; addi a5,a5,-12, computed_goto_biased.c's encoded = &&start + 8192); sd a5,0(a1); ld t1,0(a1); jr t1;
        ld a0,16(s0); ret: the jump may reach the last load, where s0 is a loaded pointer, so the 16 is kept and 24 is
        a changed function."""
        self.assertEqual(self.low((0x00045697, 0x00D13023)), KEPT)
        none = symbols.NO_IMAGE._replace(stored=())

        def code(lo):
            return words(0x00051663, 0x00019417, 0x01C0006F, 0x0005B403, 0x00002797, 0xFF478793, 0x00F5B023,
                         0x0005B303, 0x00030067, 0x00043503 | lo << 20, 0x00008067)
        self.assertEqual(symbols.mask(code(16), 0x10000, none)[36:40], code(16)[36:40])
        self.assertNotEqual(symbols.mask(code(16), 0x10000, none), symbols.mask(code(24), 0x10000, none))

    def test_a_jal_that_leaves_the_function_passes_its_arguments(self):
        """bnez a0,+12; auipc s0,0x19; j +32; ld s0,0(a1); ld t1,0(a1); beqz a1,+8; jr t1; auipc a5,0x19;
        slli a2,a5,1; j +0x1000 (a tail call to a function outside, `return g(x)`, passing a2); ld a0,16(s0); ret:
        the moved value leaves in a2, so the jump may reach the last load and the 16 is kept."""
        none = symbols.NO_IMAGE._replace(stored=())

        def code(lo):
            return words(0x00051663, 0x00019417, 0x0200006F, 0x0005B403, 0x0005B303, 0x00058463, 0x00030067,
                         0x00019797, 0x00179613, 0x0000106F, 0x00043503 | lo << 20, 0x00008067)
        self.assertEqual(symbols.mask(code(16), 0x10000, none)[40:44], code(16)[40:44])
        self.assertNotEqual(symbols.mask(code(16), 0x10000, none), symbols.mask(code(24), 0x10000, none))

    def test_a_stack_address_plus_a_label_less_the_stack_is_the_label(self):
        """The masker idiom with lla a5,.L+8192, then add a2,sp,a5; sub a4,a2,sp (or sub a2,sp,a5; sub a4,sp,a2):
        a4 is a5 again, and sd a4,0(a1) stores it, so the 16 is kept and 24 is a changed function.  The stack address
        plus a value an auipc made is no plain stack address."""
        none = symbols.NO_IMAGE._replace(stored=())
        for x, y in ((0x00F10633, 0x40260733), (0x40F10633, 0x40C10733)):
            def code(lo):
                return words(0x00051663, 0x00019417, 0x0240006F, 0x0005B403, 0x00002797, 0xFF478793, x, y,
                             0x00E5B023, 0x0005B303, 0x00030067, 0x00043503 | lo << 20, 0x00008067)
            with self.subTest(x=hex(x), y=hex(y)):
                self.assertNotEqual(symbols.mask(code(16), 0x10000, none), symbols.mask(code(24), 0x10000, none))

    def test_a_stack_address_plus_a_label_stored_keeps_the_jump_conservative(self):
        """lla a5 (auipc a5,2; addi a5,a5,-12), add a2,sp,a5, sd a2,0(sp): the store may hold the label plus the stack
        address, which other code can take away, so the 0x50 of tail_call is kept.  add a2,sp,a0 (a0 an argument);
        lui a3,1; sub a2,a2,a3 passed to jal ra,+0x1000 is a stack address less a number: masked."""
        self.assertEqual(self.low((0x00002797, 0xFF478793, 0x00F10633, 0x00C13023)), KEPT)
        self.assertEqual(self.low((0x00A10633, 0x000016B7, 0x40D60633, 0x000010EF)), MASKED)

    def test_a_stack_address_or_a_comparison_takes_no_label(self):
        """lui a2,1; sub a2,sp,a2 (a frame address 4 KiB down, asan's strcmp interceptor), or addi s0,sp,16 first and
        sub a2,s0,a2, or add a2,sp,a2, passed to jal ra,+0x1000: a stack address and a number are no label.
        auipc a3,0x45; sltu a2,a3,a0; sd a2,0(sp) (__unw_step's snez of an address, stored): 0 or 1, no label.  The
        0x50 is masked.  lui a2,1; sub a2,a0,a2 with a0 an argument, or auipc t2,0x45; slli t2,t2,1; add a2,sp,t2 (a
        stack address plus a moved value), passed to the call, may be a label, and the 0x50 is kept."""
        for before, low in (((0x00001637, 0x40C10633, 0x000010EF), MASKED),
                            ((0x01010413, 0x00001637, 0x40C40633, 0x000010EF), MASKED),
                            ((0x00001637, 0x00C10633, 0x000010EF), MASKED),
                            ((0x00045697, 0x00A6B633, 0x00C13023), MASKED),
                            ((0x00001637, 0x40C50633, 0x000010EF, 0x00000613), KEPT),
                            ((0x00045397, 0x00139393, 0x00710633, 0x000010EF, 0x00000613), KEPT)):
            with self.subTest(before=[hex(w) for w in before]):
                self.assertEqual(self.low(before), low)

    def test_an_unfollowed_value_or_an_address_of_the_function_it_hands_on_keeps_the_jump_conservative(self):
        """lui t2,1; sub t2,sp,t2 (a stack address: Ruling 53 alone takes it, the loaded tail call rule does not), then
        auipc a2,0x45; addi a2,a2,8 in a loop (bnez a0,-4): the analysis follows no more than 8 values, so a2 may be
        any of them, and jal ra,+0x1000; li a2,0 passes it: the 0x50 is kept.  auipc a2,0; jal ra,+0x1000; li a2,0
        passes the function's own entry as an argument, as the rules of Symbols take a label: kept too."""
        for before in ((0x000013B7, 0x407103B3, 0x00045617, 0x00860613, 0xFE051EE3, 0x000010EF, 0x00000613),
                       (0x00000617, 0x000010EF, 0x00000613)):
            with self.subTest(before=[hex(w) for w in before]):
                self.assertEqual(self.low(before), KEPT)

    def test_a_tail_call_through_a_number_or_a_moved_load_keeps_the_rule_of_53(self):
        """lui a2,1; sub a2,sp,a2 takes a lui's value into arithmetic, which the narrower rule allows only for a tail
        call through a loaded pointer: with jr t1 through auipc t1,0; addi t1,t1,0x14 (a number, 0x10024 outside the
        function) or through ld t1,0(a1); addi t1,t1,8 (a moved load, which may be a label), the 0x50 is kept."""
        none = symbols.NO_IMAGE._replace(stored=())
        for code in (words(0x00001637, 0x40C10633, 0x00045597, 0x0505B583, 0x00000317, 0x01430313, 0x00030067),
                     words(0x00001637, 0x40C10633, 0x00045597, 0x0505B583, 0x0005B303, 0x00830313, 0x00030067)):
            with self.subTest(code=code.hex()):
                self.assertEqual(struct.unpack("<I", symbols.mask(code, 0x10000, none)[12:16])[0], KEPT)


class JumpTableWords(unittest.TestCase):
    """The entries of a jump table a function's code proves (jump_table_words) are offsets, so code_addresses leaves
    them out of the stored code addresses, and a word of one that reads as an address of another function takes no
    label of it; a table no proof covers, or in bytes the program can write, stays in."""

    # Symbols.TABLE_CODE at 0x10000 (60 bytes, its table at 0x10800), then tail_call at 0x10040
    TEXT = words(*Symbols.TABLE_CODE) + tail_call(())

    def table(self, entries, writable=False):
        """The constant of the build: the entries at 0x10800, unless writable."""
        rows = {0x10800 + 4 * k: struct.pack("<i", e) for k, e in enumerate(entries)}
        return lambda address, size: None if writable else rows.get(address)

    def test_a_proven_table_is_left_out_of_the_stored_code_addresses(self):
        """TABLE_CODE's entries -0x7cc (its ret at 0x10034) and 0x10044 (0x20844, outside it: it leaves): read as an
        address, 0x10044 is the ld t1 of tail_call (at 0x1003c), so without the proof the build stores a label of
        tail_call and its 0x50 is kept; with it the 0x50 is masked.  With the table writable, or TABLE_CODE given no
        function, nothing is left out."""
        entries = (-0x7CC, 0x10044)
        rodata = [elf.Section(".rodata", 1, 0x10800, 8, struct.pack("<ii", *entries))]
        functions = [(0x10000, 60), (0x1003C, 20)]
        spans = symbols.jump_table_words(self.TEXT, 0x10000, functions, self.table(entries))
        self.assertEqual(spans, ((0x10800, 0x10808),))
        self.assertEqual(symbols.code_addresses(rodata, 0x10000, 0x10050, spans), ())
        self.assertEqual(symbols.code_addresses(rodata, 0x10000, 0x10050), (0x10044,))
        self.assertEqual(symbols.jump_table_words(self.TEXT, 0x10000, functions, self.table(entries, True)), ())
        self.assertEqual(symbols.jump_table_words(self.TEXT, 0x10000, [(0x1003C, 20)], self.table(entries)), ())
        for stored, low in (((), MASKED), ((0x10044,), KEPT)):
            with self.subTest(stored=stored):
                masked = symbols.mask(tail_call(()), 0x1003C, symbols.NO_IMAGE._replace(stored=stored))
                self.assertEqual(struct.unpack("<5I", masked)[1], low)

    def test_a_function_with_a_jump_no_table_proves_leaves_its_words_in(self):
        """TABLE_CODE with its jump through a0 at 0x28 turned into jr a5 (a5 an argument): no proof, so its table's
        words stay stored code addresses."""
        code = list(Symbols.TABLE_CODE)
        code[10] = 0x00078067
        self.assertEqual(symbols.jump_table_words(words(*code), 0x10000, [(0x10000, 60)], self.table((-0x7CC, 0))), ())

    def test_overlapping_tables_give_one_range(self):
        """TABLE_CODE at 0x10000 (its table at 0x10800) and again at 0x1003c with addi a2,a2,0x7b4 (its table at
        0x10050 + 0x7b4 = 0x10804), every entry 0x100000 (outside both): [0x10800, 0x10808) and [0x10804, 0x1080c)
        make one range."""
        shifted = list(Symbols.TABLE_CODE)
        shifted[6] = 0x7B460613
        text = words(*Symbols.TABLE_CODE) + words(*shifted)
        got = symbols.jump_table_words(text, 0x10000, [(0x10000, 60), (0x1003C, 60)], self.table((0x100000,) * 3))
        self.assertEqual(got, ((0x10800, 0x1080C),))


class RuntimeNoreturn(unittest.TestCase):
    """A function of a sanitizer runtime that NORETURN_RUNTIME names never returns, local (a static link's) or not;
    a C name of the same words is a program's own function, which may."""

    def test_check_failed_never_returns_and_a_local_c_function_may(self):
        for name, binding, dead in (("_ZN11__sanitizer11CheckFailedEPKciS1_yy", "local", {0x10100}),
                                    ("_ZN11__sanitizer11CheckFailedEPKciS1_yy", "global", {0x10100}),
                                    ("CheckFailed", "local", set()), ("CheckFailed", "global", set())):
            with self.subTest(name=name, binding=binding):
                got = symbols.noreturn_addresses([elf.Symbol(name, "func", 0x10100, 16, binding)])
                self.assertEqual(got, dead)


MASKER = os.path.join(HERE, "fixtures", "masker")


class RealLoadedTailCalls(unittest.TestCase):
    """Six functions of the asan runtime in libreac's fuzz_ctrl asan and asan-ubsan builds (fixtures/masker/README.md)
    that 1842185 only moved the data of, each ending in a tail call through a loaded pointer (wcrtomb's words aside):
    strcmp, wcrtomb, PoisonShadow and __unw_step mask equal across 3425050 -> 1842185, while a change of their code,
    or a moved value they pass on, still shows; memcmp and bcmp store an auipc's value, a possible biased label, and
    stay unequal."""

    EQUAL = ("___interceptor_strcmp", "___interceptor_wcrtomb", "_ZN6__asan12PoisonShadowEmmh", "__unw_step")

    @classmethod
    def setUpClass(cls):
        with open(os.path.join(MASKER, "fuzz_ctrl-asan.json")) as f:
            cls.fixture = json.load(f)

    def image(self, side, build, name, strict=True):
        """The Image mask saw for the function, from what the fixture recorded; strict, a question it did not record
        fails the test, else its answer is None (unknown)."""
        f = self.fixture["functions"]["%s/%s" % (side, build)][name]

        def recorded(rows):
            def ask(address, size):
                key = "%x:%d" % (address, size)
                if strict:
                    self.assertIn(key, rows)
                return None if rows.get(key) is None else bytes.fromhex(rows[key])
            return ask
        return symbols.Image(frozenset(f["noreturn"]), recorded(f["constant"]), recorded(f["data"]),
                             tuple(tuple(s) for s in self.fixture["sections"]["%s/%s" % (side, build)]),
                             tuple(f["stored"]), tuple(tuple(r) for r in f["landing"]))

    def masked(self, side, build, name, code=None, strict=True, stored=None):
        f = self.fixture["functions"]["%s/%s" % (side, build)][name]
        image = self.image(side, build, name, strict)
        if stored is not None:
            image = image._replace(stored=stored)
        return hashlib.sha256(symbols.mask(code or bytes.fromhex(f["code"]), f["address"], image)).hexdigest()

    def test_four_mask_equal_across_the_move(self):
        for build in ("asan", "asan-ubsan"):
            for name in self.EQUAL:
                with self.subTest(build=build, name=name):
                    self.assertEqual(self.masked("3425050", build, name), self.masked("1842185", build, name))

    def test_memcmp_and_bcmp_store_an_auipc_value_and_stay_unequal(self):
        """sd a0,8(sp) of auipc a0; addi a0,a0,lo (a report's argument): stored as it is, it may be a label biased
        far from the function that other code moves into the label, so the jr t1 may go anywhere."""
        for build in ("asan", "asan-ubsan"):
            for name in ("___interceptor_memcmp", "___interceptor_bcmp"):
                with self.subTest(build=build, name=name):
                    self.assertNotEqual(self.masked("3425050", build, name), self.masked("1842185", build, name))

    def test_a_change_of_the_code_shows(self):
        """1842185's code with a frame 16 bytes larger (each starts with addi sp,sp,-N) masks unequal."""
        for build in ("asan", "asan-ubsan"):
            for name in self.EQUAL:
                code = bytearray.fromhex(self.fixture["functions"]["1842185/" + build][name]["code"])
                first = struct.unpack_from("<I", code)[0]
                self.assertEqual(first & 0xFFFFF, 0x10113)    # addi sp,sp,imm
                struct.pack_into("<I", code, 0, ((symbols.i_imm(first) - 16) & 0xFFF) << 20 | 0x10113)
                with self.subTest(build=build, name=name):
                    self.assertNotEqual(self.masked("1842185", build, name, bytes(code), strict=False),
                                        self.masked("3425050", build, name))

    def test_a_moved_value_strcmp_passes_on_takes_its_tail_call(self):
        """strcmp's lui a1,1; sub a1,s0,a1 makes a frame address, which it passes to a call in a1; with
        sub a1,a0,a1 instead (a0 no stack address) in both builds, a1 may be a label, so the jr t1 may go anywhere,
        the moved data's low halves are kept, and the two builds mask unequal."""
        for build in ("asan", "asan-ubsan"):
            got = []
            for side in ("3425050", "1842185"):
                code = bytearray.fromhex(self.fixture["functions"]["%s/%s" % (side, build)]["___interceptor_strcmp"]
                                         ["code"])
                ws = struct.unpack("<%dI" % (len(code) // 4), code)
                for at in [k for k, w in enumerate(ws) if w == 0x40B405B3]:      # sub a1,s0,a1
                    struct.pack_into("<I", code, 4 * at, 0x40B505B3)             # sub a1,a0,a1
                got.append(self.masked(side, build, "___interceptor_strcmp", bytes(code), strict=False))
            with self.subTest(build=build):
                self.assertIn(0x40B405B3, struct.unpack("<%dI" % (len(code) // 4), bytes.fromhex(
                    self.fixture["functions"]["1842185/" + build]["___interceptor_strcmp"]["code"])))
                self.assertNotEqual(*got)

    def test_vsnprintf_table_words_take_no_label_of_wcrtomb(self):
        """__sanitizer::VSNPrintf's jump table at 0x20e70 holds 33 offsets, 29 of them in [0x4654c, 0x46abc) when read
        as addresses, inside wcrtomb.  jump_table_words proves the table from VSNPrintf's code, so code_addresses
        leaves them out; stored, they would make wcrtomb's tail call a possible computed goto, and it would mask
        unequal across the move, as 40e964d5bd98 had it."""
        v = self.fixture["vsnprintf"]
        rows = {int(k.split(":")[0], 16): bytes.fromhex(b) for k, b in v["constant"].items() if b}
        spans = symbols.jump_table_words(bytes.fromhex(v["code"]), v["address"],
                                         [(v["address"], len(v["code"]) // 2)],
                                         lambda address, size: rows.get(address), frozenset(v["noreturn"]))
        self.assertEqual(spans, ((0x20E70, 0x20EF4),))
        table = b"".join(rows[a] for a in range(0x20E70, 0x20EF4, 4))
        rodata = [elf.Section(".rodata", 1, 0x20E70, len(table), table)]
        inside = symbols.code_addresses(rodata, 0x4654C, 0x4654C + 1392)
        self.assertEqual(inside, (0x4662C, 0x4664C, 0x466B4, 0x46890))
        self.assertEqual(symbols.code_addresses(rodata, 0x4654C, 0x4654C + 1392, spans), ())
        for build in ("asan", "asan-ubsan"):
            with self.subTest(build=build):
                offset = self.fixture["functions"]["1842185/" + build]["___interceptor_wcrtomb"]["address"] - 0x4654C
                stored = tuple(a + offset for a in inside)
                self.assertNotEqual(self.masked("3425050", build, "___interceptor_wcrtomb", stored=stored),
                                    self.masked("1842185", build, "___interceptor_wcrtomb", stored=stored))


class SymbolsModule(unittest.TestCase):
    """symbols.table, resolve, defines and reference: the one reading of what Symbols.v defines, which lint's
    contract-literals, contracts.py and prove.py share."""

    ROWS = [symbols.Sym("crc32_z.llvm.42", "func", 0x11300, 8, "1a" * 32, "2b" * 32, "-"),
            symbols.Sym("dummy", "func", 0x11310, 4, "3c" * 32, "4d" * 32, "-"),
            symbols.Sym("dummy", "func", 0x11320, 4, "5e" * 32, "6f" * 32, "-"),
            symbols.Sym(".got", "section", 0x14000, 16, "70" * 32, "-", "-")]

    def test_each_path_symbols_v_gives_a_row_resolves_to_it(self):
        tab = symbols.table(self.ROWS)
        crc, got = self.ROWS[0], self.ROWS[3]
        self.assertEqual(symbols.paths("s_crc32_z_llvm_42", False), ("s_crc32_z_llvm_42", "Size.s_crc32_z_llvm_42"))
        for path, want in (("s_crc32_z_llvm_42", (crc, False)), ("Size.s_crc32_z_llvm_42", (crc, True)),
                           ("Sec.s_got", (got, False)), ("Sec.Size.s_got", (got, True)),
                           # a name two rows share has no identifier; a path is never read as a name
                           ("s_dummy", (None, False)), ("crc32_z.llvm.42", (None, False)), ("s_got", (None, False)),
                           ("Size", (None, True)), ("", (None, False))):
            with self.subTest(path=path):
                self.assertEqual(symbols.resolve(tab, path), want)
        self.assertEqual(symbols.resolve(None, "s_crc32_z_llvm_42"), (None, False))

    def test_the_modules_a_build_defines(self):
        tab = symbols.table(self.ROWS)
        self.assertTrue(all(symbols.defines(tab, p) for p in ("Size", "Sec", "Sec.Size", "Sec.s_got")))
        self.assertFalse(symbols.defines(tab, "s_dummy"))
        no_sections = symbols.table(self.ROWS[:1])
        self.assertEqual([symbols.defines(no_sections, p) for p in ("Size", "Sec", "Sec.Size")], [True, False, False])

    def test_a_reference_is_read_as_rocq_reads_a_name(self):
        got = [symbols.reference(m.group()) for m in symbols.ROCQ_NAME.finditer(
            "Symbols .Plain\n  .Size.s_x Lib.Symbols.Ubsan.Sec.s_got Plain.M.loaded_segments Plain.s_y Symbols.Plain")]
        self.assertEqual(got, [("Plain", "Size.s_x"), ("Ubsan", "Sec.s_got"), None, ("Plain", "s_y"), ("Plain", "")])


class SymbolFacts(unittest.TestCase):
    """A symbol fact in a tree: `oft symbols` writes it beside harness.yaml, facts load it, and lint holds it to its
    path, to its format and to the binary harness.yaml pins for its build."""

    def oft_symbols(self, t, pin=None):
        """`oft symbols` for the fixture as zlib/checksum_fuzzer's plain build, with builds.plain.sha256 set to pin
        (default: the stand-in pin, kept): (exit status, what it printed)."""
        if pin is not None:
            rel = "projects/zlib/checksum_fuzzer/harness.yaml"
            t.write(rel, t.read(rel).replace(PLAIN_PIN, pin))
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = cli.main(["--root", t.root, "symbols", "--unstripped", UNSTRIPPED, "--stripped", STRIPPED,
                           "--lines", LINES, "--harness", UNIT, "--build", "plain"])
        return rc, out.getvalue()

    def test_oft_symbols_writes_the_fact_of_a_build(self):
        with tree(render=False) as t:
            rc, said = self.oft_symbols(t, pin=STRIPPED_SHA)
            self.assertEqual(rc, 0, said)
            self.assertEqual(symbols.load(t.path(FACT)), (STRIPPED_SHA, list(fixture().values())))
            self.assertIn(FACT, said)

    def test_oft_symbols_refuses_a_binary_harness_yaml_does_not_pin(self):
        with tree(render=False) as t:
            before = t.read(FACT)   # the fixture's stand-in fact, which a refusal leaves as it is
            rc, said = self.oft_symbols(t)
            self.assertEqual(rc, 1)
            self.assertIn(STRIPPED_SHA, said)
            self.assertIn(PLAIN_PIN, said)
            self.assertEqual(t.read(FACT), before)

    def test_the_facts_load_the_symbol_fact_beside_harness_yaml(self):
        with tree(render=False) as t:
            self.assertEqual(self.oft_symbols(t, pin=STRIPPED_SHA)[0], 0)
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertEqual(h.symbols(), {"plain": (STRIPPED_SHA, list(fixture().values()))})

    def test_a_symbol_fact_of_the_pinned_binary_is_clean(self):
        with tree() as t:
            symbols.write(t.path(FACT), list(fixture().values()), PLAIN_PIN)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_symbol_fact_of_another_binary_is_refused(self):
        """A rebuild that changes the binary leaves its fact stale until oft symbols runs again."""
        with tree() as t:
            symbols.write(t.path(FACT), list(fixture().values()), STRIPPED_SHA)
            found = [str(f) for f in t.lint()]
            self.assertEqual(len(found), 1, found)
            self.assertTrue(found[0].startswith("schema %s: " % FACT), found)
            self.assertIn(STRIPPED_SHA, found[0])
            self.assertIn(PLAIN_PIN, found[0])

    def test_a_symbol_fact_that_does_not_parse_is_refused(self):
        with tree() as t:
            t.write(FACT, "# oss-fuzz-theorems/symbols/1 sha256=%s\nf\t0x11270\t108\n" % PLAIN_PIN)
            found = [str(f) for f in t.lint()]
            self.assertEqual(len(found), 1, found)
            self.assertTrue(found[0].startswith("schema %s: line 2: " % FACT), found)

    def test_a_symbol_fact_of_no_published_build_is_refused(self):
        """Its file name is a build its harness.yaml publishes: a withheld build shows no SHA-256."""
        with tree() as t:
            rel = "projects/zlib/checksum_fuzzer/symbols/fuzz.tsv"
            symbols.write(t.path(rel), list(fixture().values()), PLAIN_PIN)
            found = [str(f) for f in t.lint()]
            self.assertEqual(found, ["paths %s: 'fuzz' is no build zlib/checksum_fuzzer publishes" % rel])

    def test_a_symlinked_symbol_fact_is_not_followed(self):
        """A symbolic link is a paths finding, and no rule reads what it points at: here a stale fact outside the
        tree, which would be a schema finding if it were read."""
        with tree() as t:
            elsewhere = os.path.join(os.path.dirname(t.root), "elsewhere.tsv")
            symbols.write(elsewhere, list(fixture().values()), STRIPPED_SHA)
            os.remove(t.path(FACT))   # the fixture's stand-in fact
            os.symlink(elsewhere, t.path(FACT))
            self.assertEqual([str(f) for f in t.lint() if FACT in str(f)], ["paths %s: a symbolic link" % FACT])
            self.assertRaises(facts.BoundedFileError, symbols.load, t.path(FACT))
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertRaises(facts.BoundedFileError, h.symbols)

    def test_a_symbol_fact_over_its_cap_is_not_read(self):
        """A fact over the cap of its path is a paths finding and is read by no rule: here a stale one, which would
        be a schema finding if it were read.  The cap of its path is symbols.CAP, the most bytes symbols.load reads."""
        cap = facts.file_cap(FACT)
        self.assertEqual(cap, symbols.CAP)
        with tree() as t:
            symbols.write(t.path(FACT), list(fixture().values()), STRIPPED_SHA)
            row = t.read(FACT).splitlines()[1] + "\n"
            t.write(FACT, row * (cap // len(row) + 1), "a")
            size = os.path.getsize(t.path(FACT))
            self.assertGreater(size, cap)
            self.assertEqual([str(f) for f in t.lint() if FACT in str(f)],
                             ["paths %s: %d bytes, over the %d-byte cap" % (FACT, size, cap)])
            self.assertRaises(facts.BoundedFileError, symbols.load, t.path(FACT))


if __name__ == "__main__":
    unittest.main()
