"""contracts.py (oft plan --contracts): the work key of each contract file of a fuzz target, which says which contracts
need an agent after a change, and never a basis for verdict reuse."""
import io
import json
import os
import subprocess
import sys
import unittest

from oft import contracts, keys, layout, names, symbols
from oft.tests.helpers import NEW_NAMESPACE, rename_namespace, tree
from oft.tests.test_keys import CX_UNIT, TOOLS, UNIT, commit, repo


# the proof library of UNIT in the fixture's layout, and the module path its files are under
LIB = layout.proof_lib_dir("zlib", "checksum_fuzzer", layout.OLD)
# the fixture's namespace (its release.yaml names none) and the harness theory of UNIT in it
NAMESPACE = names.NAMESPACE_DEFAULT
HARNESS_THEORY = names.rocq_harness(NAMESPACE, "zlib", "checksum_fuzzer")
LIB_MODULE = names.rocq_proof(NAMESPACE, "zlib", "checksum_fuzzer", "lib")
# four contracts: entry and crc require Lib/Mem.v, which requires Lib/Deep.v (Deep names crc_table by its size);
# table requires nothing, and names nothing else, in a comment; state names what has no bytes: a function of size 0,
# an object and a section with no file contents.  Lib/Other.v no contract requires, and Lib/Old/Deep.v neither: Rocq
# loads the library whose path is the whole name, From prefix and all, when there is one
def contract_lib(namespace=NAMESPACE):
    """CONTRACT_LIB with its Require commands in namespace."""
    lib_module = names.rocq_proof(namespace, "zlib", "checksum_fuzzer", "lib")
    return {
        "Lib/Deep.v": "Definition TABLE_LEN := Symbols.Plain.Size.s_crc_table.\n",
        "Lib/Old/Deep.v": "Definition TABLE_LEN := 1024.\n",
        "Lib/Mem.v": "From %s.Lib Require Import Deep.\nDefinition cell := 8.\n" % lib_module,
        "Lib/Other.v": "Definition other := 1.\n",
        "Prog/entry_c.v": ("From %s.Lib Require Import\n  Mem.\n"
                           "Definition ENTRY : Z := Symbols.Plain.s_LLVMFuzzerTestOneInput.\n" % lib_module),
        # a partly qualified library under a From prefix, as `From Stdlib Require Import Lia` loads
        # Stdlib.micromega.Lia
        "Prog/crc_c.v": ("From %s Require Import Lib.Mem.\n" % namespace
                         + "Definition CRC : Z := Symbols.Plain.s_crc32_z_llvm_42.\n"
                         "Definition GOT : Z := Symbols.Plain.Sec.s_got.\n"),
        "Prog/table_c.v": ("(* From %s.Lib Require Import Other.  Symbols.Plain.s_LLVMFuzzerTestOneInput *)\n"
                           "Definition TABLE : Z := Symbols.Plain.s_crc_table.\n" % lib_module),
        "Prog/state_c.v": ("Definition START : Z := Symbols.Plain.s__start.\n"
                           "Definition LEN : Z := Symbols.Plain.s_g_file_len.\n"
                           "Definition BSS : Z := Symbols.Plain.Sec.s_bss.\n"),
    }


CONTRACT_LIB = contract_lib()
ENTRY, CRC, TABLE, STATE = ("%s/Prog/%s_c.v" % (LIB, n) for n in ("entry", "crc", "table", "state"))
FACT = layout.symbol_fact("zlib", "checksum_fuzzer", "plain")


def contract_repo(t, namespace=NAMESPACE):
    """t as repo() makes it, with contract_lib(namespace) in UNIT's proof library and the stand-in symbol fact of
    UNIT's plain build, with a data object in .bss (no file contents) and a function no contract names added: its first
    commit."""
    for rel, text in contract_lib(namespace).items():
        t.write("%s/%s" % (LIB, rel), text)
    pin, rows = symbols.load(t.path(FACT))
    rows += [symbols.Sym("g_file_len", "object", 0x15008, 8, "-", "-", "-", "-"),
             symbols.Sym("unused", "func", 0x11310, 8, "5f" * 32, "6e" * 32, "-", "-")]
    symbols.write(t.path(FACT), sorted(rows, key=lambda r: (r.address, r.name)), pin)
    return repo(t)


def put_row(t, name, **fields):
    """Rewrite the row of name in UNIT's plain symbol fact with fields changed; with no fields, remove it."""
    pin, rows = symbols.load(t.path(FACT))
    symbols.write(t.path(FACT), [r._replace(**fields) if r.name == name else r for r in rows
                                 if r.name != name or fields], pin)


def unchanged(*paths):
    return {p: "unchanged from the base" for p in paths}


def refs(row):
    """(build, written, name, status, kind) of each reference of a contract_keys row, in its order."""
    return [(r["build"], r["written"], r["name"], r["status"], r["kind"]) for r in row["references"]]


# the references of ENTRY: its own, and Lib/Deep.v's, which it requires through Lib/Mem.v
ENTRY_REFS = [("plain", "Size.s_crc_table", "crc_table", "resolved", "object"),
              ("plain", "s_LLVMFuzzerTestOneInput", "LLVMFuzzerTestOneInput", "resolved", "func")]


class ContractKeys(unittest.TestCase):
    """contracts.contract_keys: a work key, which says which contracts need an agent after a change; never a verdict
    key.  A contract's key is its file, the code of the files of the proof library and of the statement library it
    requires, the proof environment (theories/, toolchain/allowed-axioms.txt, the project's dune-project stanzas, the
    harness's statement folder but its source, its pins and its Rocq files), the masked bytes or the size of what it
    names from Symbols.v, the checker and the checker image; never an address, a comment or a file it does not read."""

    def keys(self, t, head, base):
        return contracts.contract_keys(t.root, UNIT, head, base=base)

    def whys(self, t, head, base):
        return {p: r["why"] for p, r in self.keys(t, head, base).items()}

    def test_a_moved_function_changes_no_key_but_its_address_component(self):
        """The function moved, so its pc-relative instructions changed: its exact bytes are other, its masked bytes
        the same, and Symbols.v, rendered again, gives it its new address.  A proof that names it from Symbols.v
        checks again with no edit, so no key changes: oft classify reports the move."""
        with tree() as t:
            base = contract_repo(t)
            before = self.keys(t, base, None)
            put_row(t, "LLVMFuzzerTestOneInput", address=0x11500, exact="1e" * 32)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("0x11500", t.read("projects/zlib/checksum_fuzzer/Symbols.v"))
            got = self.keys(t, commit(t), base)
            self.assertEqual(sorted(got), [CRC, ENTRY, STATE, TABLE])
            self.assertEqual({p: r["key"] for p, r in got.items()}, {p: r["key"] for p, r in before.items()})
            self.assertEqual({p: r["why"] for p, r in got.items()}, unchanged(CRC, ENTRY, STATE, TABLE))
            self.assertEqual(refs(got[ENTRY]), ENTRY_REFS)

    def test_a_function_with_other_masked_bytes_changes_the_keys_that_name_it(self):
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32)
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(CRC, STATE, TABLE), **{ENTRY: "changed: plain:LLVMFuzzerTestOneInput"}))

    def test_a_function_whose_targets_are_unresolved_has_no_key(self):
        """`?` targets say that the fact cannot tell what an address immediate of the function points at, so no key
        of it says that a call or a read of it changed: the contract that names it is unknown, never unchanged."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", targets="?")
            got = self.keys(t, commit(t), base)
            self.assertIsNone(got[ENTRY]["key"])
            self.assertEqual(got[ENTRY]["why"], "lib/Prog/entry_c.v:3: Symbols.Plain.s_LLVMFuzzerTestOneInput is a "
                             "function with an address immediate that the symbol fact of plain cannot resolve, so "
                             "no key says what it points at")
            self.assertEqual({p: r["why"] for p, r in got.items() if p != ENTRY}, unchanged(CRC, STATE, TABLE))

    def test_an_identical_function_and_contract_keep_the_key(self):
        """A change to a function no contract names and to library files no contract requires keeps every key."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "unused", exact="3e" * 32, masked="4d" * 32)
            t.write("%s/Lib/Other.v" % LIB, "Definition other := 2.\n")
            t.write("%s/Lib/Old/Deep.v" % LIB, "Definition TABLE_LEN := 2048.\n")
            t.write(ENTRY.replace("entry_c.v", "Unrelated.v"), "Definition unrelated := Symbols.Plain.s__start.\n")
            got = self.keys(t, commit(t), base)
            before = self.keys(t, base, None)
            self.assertEqual({p: r["key"] for p, r in got.items()}, {p: r["key"] for p, r in before.items()})
            self.assertEqual({r["why"] for r in got.values()}, {"unchanged from the base"})
            self.assertEqual({r["why"] for r in before.values()}, {"no base"})
            self.assertEqual({r["state"] for r in got.values()}, {"keyed"})
            self.assertEqual(refs(got[CRC]), [("plain", "Sec.s_got", ".got", "resolved", "section"),
                                              ("plain", "Size.s_crc_table", "crc_table", "resolved", "object"),
                                              ("plain", "s_crc32_z_llvm_42", "crc32_z.llvm.42", "resolved", "func")])
            self.assertEqual(refs(got[TABLE]), [("plain", "s_crc_table", "crc_table", "resolved", "object")])
            self.assertEqual(refs(got[STATE]), [("plain", "Sec.s_bss", ".bss", "resolved", "section"),
                                                ("plain", "s__start", "_start", "resolved", "func"),
                                                ("plain", "s_g_file_len", "g_file_len", "resolved", "object")])

    def test_an_address_alone_is_in_no_key(self):
        """A function, an object and a section at another address with the same bytes keep their contracts' keys."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "crc32_z.llvm.42", address=0x11400)
            put_row(t, "crc_table", address=0x13100)
            put_row(t, ".got", address=0x14100)
            put_row(t, "_start", address=0x11250)
            self.assertEqual(self.whys(t, commit(t), base), unchanged(CRC, ENTRY, STATE, TABLE))

    def test_a_changed_contract_file_changes_its_key_alone(self):
        with tree() as t:
            base = contract_repo(t)
            t.write(TABLE, CONTRACT_LIB["Prog/table_c.v"] + "Definition TABLE_END : Z := TABLE + 1.\n")
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(CRC, ENTRY, STATE), **{TABLE: "changed: contract"}))

    def test_a_changed_required_file_changes_every_key_that_requires_it(self):
        """Lib/Deep.v is required by Lib/Mem.v, which both entry and crc require: a change to it changes both keys
        and names it, by its path in the proofs folder."""
        with tree() as t:
            base = contract_repo(t)
            t.write("%s/Lib/Deep.v" % LIB, CONTRACT_LIB["Lib/Deep.v"] + "Definition deeper := 0.\n")
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(STATE, TABLE), **{p: "changed: lib/Lib/Deep.v" for p in (ENTRY, CRC)}))

    def test_each_part_of_the_proof_environment_is_in_every_key(self):
        """A proof is checked against the core theories, the axiom allowlist, the project's dune-project stanzas
        and its harness's statement library (its dune file): a change to any of them changes every key, with the
        contract files and the symbol facts as they were, and why names it as the build key does."""
        for component, path, text in (("theories", "theories/Extra.v", "Definition extra := 1.\n"),
                                      ("allowed-axioms", "toolchain/allowed-axioms.txt", "Corelib.Init.Other.prim\n"),
                                      ("harness", "projects/zlib/checksum_fuzzer/dune", None),
                                      ("dune-project", "dune-project", None)):
            with self.subTest(component=component), tree() as t:
                base = contract_repo(t)
                if component == "harness":
                    text = t.read(path).replace("(theories Stdlib", "(theories Stdlib Extra")
                elif component == "dune-project":
                    text = t.read(path) + "(generate_opam_files false)\n"
                t.write(path, text)
                self.assertEqual(set(self.whys(t, commit(t), base).values()), {"changed: " + component})

    def test_the_image_pins_and_addresses_are_in_no_key(self):
        """harness.yaml (its pins name the image, its statement fields reach Statements.v), images/ (the rules that
        build the image from the pinned binary), Symbols.v (the addresses) and README.md are left out of the harness
        component: the work key leaves the image out on purpose, and the symbol fact enters per reference."""
        with tree() as t:
            base = contract_repo(t)
            for rel in ("harness.yaml", "images/dune", "Symbols.v", "README.md"):
                path = "projects/zlib/checksum_fuzzer/" + rel
                t.write(path, (t.read(path) if os.path.exists(t.path(path)) else "") + "# changed\n")
            self.assertEqual(self.whys(t, commit(t), base), unchanged(CRC, ENTRY, STATE, TABLE))

    def test_what_no_contract_reads_of_the_statement_folder_is_in_no_key(self):
        """The fuzz target's source (source/, which no Rocq file reads), a field of harness.yaml with no pin in it,
        and the statement library's files (Statements.v, Images.v, Characterise.v, Distribution.v), which no contract
        here requires: a change to them all keeps every key, as a pull request that rebuilds the harness changes them
        (the proof repair of libreac's pull request 35)."""
        with tree() as t:
            base = contract_repo(t)
            folder = "projects/zlib/checksum_fuzzer/"
            t.write(folder + "source/checksum_fuzzer.c", t.read(folder + "source/checksum_fuzzer.c") + "/* x */\n")
            y = t.yaml(folder + "harness.yaml")
            y["checks"][0]["what"] += " Again."
            t.put_yaml(folder + "harness.yaml", y)
            for rel in ("Statements.v", "Images.v", "Characterise.v", "Distribution.v"):
                t.write(folder + rel, t.read(folder + rel) + "Definition extra_%s := 0.\n" % rel[:-2])
            self.assertEqual(self.whys(t, commit(t), base), unchanged(CRC, ENTRY, STATE, TABLE))

    def test_a_statement_library_file_changes_the_keys_of_the_contracts_that_require_it(self):
        """table requires Statements.v of the statement library, which requires Images.v and Distribution.v: a
        change to the code of any of them changes table's key alone and names the file as harness/<file>; the
        others require none of them."""
        statement = "From %s Require Statements.\n" % HARNESS_THEORY
        for rel in ("Statements.v", "Images.v", "Distribution.v"):
            with self.subTest(file=rel), tree() as t:
                contract_repo(t)
                t.write(TABLE, statement + CONTRACT_LIB["Prog/table_c.v"])
                base = commit(t)
                path = "projects/zlib/checksum_fuzzer/" + rel
                t.write(path, t.read(path) + "Definition extra := 0.\n")
                got = self.keys(t, commit(t), base)
                self.assertEqual({p: r["why"] for p, r in got.items()},
                                 dict(unchanged(CRC, ENTRY, STATE), **{TABLE: "changed: harness/" + rel}))
                self.assertEqual(got[TABLE]["changed"][0]["type"], "library")

    def test_a_comment_or_layout_change_to_a_required_file_changes_no_key(self):
        """Rocq reads no comment and no layout: a required file of the proof library (Lib/Deep.v) or of the statement
        library (Statements.v) with another comment, another blank run and another line break keeps every key; a
        changed string literal is code and changes the keys that require the file."""
        deep = "%s/Lib/Deep.v" % LIB
        statement = "From %s Require Statements.\n" % HARNESS_THEORY
        with tree() as t:
            contract_repo(t)
            t.write(TABLE, statement + CONTRACT_LIB["Prog/table_c.v"])
            t.write("%s/Lib/Note.v" % LIB, 'Definition note := "a b".\n')
            t.write(ENTRY, CONTRACT_LIB["Prog/entry_c.v"] + "From %s.Lib Require Note.\n" % LIB_MODULE)
            base = commit(t)
            t.write(deep, "(* the table's length, read by Mem *)\nDefinition   TABLE_LEN :=\n"
                          "  Symbols.Plain.Size.s_crc_table. (* end *)\n")
            statements = "projects/zlib/checksum_fuzzer/Statements.v"
            t.write(statements, "(* a statement's text changed *)\n" + t.read(statements))
            self.assertEqual(self.whys(t, commit(t), base), unchanged(CRC, ENTRY, STATE, TABLE))
            t.write("%s/Lib/Note.v" % LIB, 'Definition note := "a  b".\n')
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(CRC, STATE, TABLE), **{ENTRY: "changed: lib/Lib/Note.v"}))

    def test_a_section_is_keyed_by_its_bytes(self):
        with tree() as t:
            base = contract_repo(t)
            put_row(t, ".got", exact="6b" * 32)
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(ENTRY, STATE, TABLE), **{CRC: "changed: plain:.got"}))

    def test_a_size_reference_is_keyed_by_the_size(self):
        """Deep.v names crc_table's size (Size.s_crc_table), so entry and crc, which require it, change with the
        size; table names only its address and bytes."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "crc_table", size=2048)
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(STATE, TABLE), **{p: "changed: plain:crc_table" for p in (ENTRY, CRC)}))

    def test_what_has_no_bytes_is_keyed_by_its_size(self):
        for name, size in (("g_file_len", 16), (".bss", 128)):
            with self.subTest(name=name), tree() as t:
                base = contract_repo(t)
                put_row(t, name, size=size)
                self.assertEqual(self.whys(t, commit(t), base),
                                 dict(unchanged(CRC, ENTRY, TABLE), **{STATE: "changed: plain:" + name}))

    def test_a_function_of_size_0_is_keyed_by_its_kind(self):
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "_start", kind="object", size=8)
            self.assertEqual(self.whys(t, commit(t), base),
                             dict(unchanged(CRC, ENTRY, TABLE), **{STATE: "changed: plain:_start"}))

    def test_a_reference_that_cannot_be_resolved_is_unknown(self):
        """A reference to a build with no symbol fact, to a name the fact lacks (gone from the build, or shared by
        two or more of its rows, so that Symbols.v defines no identifier for it), is no part of a key: the contract,
        and each contract that requires the file, has no key, and why says where."""
        no_fact = "cannot be resolved: ubsan has no symbol fact"
        cases = (
            ("a build with no symbol fact", "Prog/u_c.v", "Definition T : Z := Symbols.Ubsan.s_crc_table.\n", None,
             "lib/Prog/u_c.v:1: Symbols.Ubsan.s_crc_table " + no_fact),
            ("a name the fact lacks", "Prog/gone_c.v", "(* x *)\nDefinition G : Z := Symbols.Plain.s_gone.\n", None,
             "lib/Prog/gone_c.v:2: Symbols.Plain.s_gone cannot be resolved: the symbol fact of plain has no row that "
             "Symbols.v names s_gone"),
            ("a section the fact lacks", "Prog/sec_c.v", "Definition G : Z := Symbols.Plain.Sec.Size.s_data.\n", None,
             "lib/Prog/sec_c.v:1: Symbols.Plain.Sec.Size.s_data cannot be resolved: the symbol fact of plain has no "
             "row that Symbols.v names Sec.Size.s_data"),
            ("a name two rows share", "Prog/dup_c.v", "Definition D : Z := Symbols.Plain.s_dummy.\n", "dummy",
             "lib/Prog/dup_c.v:1: Symbols.Plain.s_dummy cannot be resolved: the symbol fact of plain has no row that "
             "Symbols.v names s_dummy"),
            ("in a required file", "Lib/Mem.v", CONTRACT_LIB["Lib/Mem.v"] + "Definition U := Symbols.Ubsan.s_x.\n",
             None, "lib/Lib/Mem.v:3: Symbols.Ubsan.s_x " + no_fact))
        for what, rel, text, shared, reason in cases:
            with self.subTest(what), tree() as t:
                base = contract_repo(t)
                if shared:
                    pin, rows = symbols.load(t.path(FACT))
                    rows += [symbols.Sym(shared, "func", a, 4, "7a" * 32, "7b" * 32, "-", "-")
                             for a in (0x11320, 0x11330)]
                    symbols.write(t.path(FACT), sorted(rows, key=lambda r: (r.address, r.name)), pin)
                t.write("%s/%s" % (LIB, rel), text)
                got = self.keys(t, commit(t), base)
                want = [ENTRY, CRC] if rel == "Lib/Mem.v" else ["%s/%s" % (LIB, rel)]
                self.assertEqual({p: (r["state"], r["key"], r["why"]) for p, r in got.items() if p in want},
                                 {p: ("unknown", None, reason) for p in want})
                self.assertEqual({r["state"] for p, r in got.items() if p not in want}, {"keyed"})
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "_start")
            reason = ("lib/Prog/state_c.v:1: Symbols.Plain.s__start cannot be resolved: the symbol fact of plain has "
                      "no row that Symbols.v names s__start")
            self.assertEqual(self.keys(t, commit(t), base)[STATE],
                             {"state": "unknown", "key": None,
                              "references": [{"build": "plain", "written": "Sec.s_bss", "name": ".bss",
                                              "status": "resolved", "kind": "section"},
                                             {"build": "plain", "written": "s__start", "name": None,
                                              "status": "unresolved", "kind": None},
                                             {"build": "plain", "written": "s_g_file_len", "name": "g_file_len",
                                              "status": "resolved", "kind": "object"}],
                              "unknown": reason, "base": "keyed at the base", "base_unknown": None, "changed": None,
                              "why": reason})

    def test_a_contract_not_at_the_base_says_so(self):
        with tree() as t:
            base = contract_repo(t)
            t.write("%s/U/Prog/table_c.v" % LIB, "Definition T : Z := Symbols.Plain.s_crc_table.\n")
            got = self.keys(t, commit(t), base)
            row = got["%s/U/Prog/table_c.v" % LIB]
            self.assertEqual((row["state"], refs(row), row["base"], row["changed"], row["why"]),
                             ("keyed", [("plain", "s_crc_table", "crc_table", "resolved", "object")], "not at the base",
                              None, "not at the base"))
            self.assertRegex(row["key"], "^[0-9a-f]{64}$")

    def test_a_contract_that_uses_a_module_of_symbols_as_a_whole_is_unknown(self):
        """Names a module of Symbols.v brings into scope (an Import, then a bare s_x; a module alias, then S.s_x)
        cannot be read, so such a contract gets no key that looks complete, in itself or through a file it requires;
        a contract keyed at the head and unknown at the base says so."""
        alias = "lib/Prog/alias_c.v"
        cases = (
            ("Import", "Prog/import_c.v", "Import Symbols.Plain.\nDefinition E : Z := s_LLVMFuzzerTestOneInput.\n",
             "lib/Prog/import_c.v:1: Symbols.Plain is used as a module"),
            # Rocq reads `Symbols .Plain` as Symbols.Plain (a blank may stand before each .field)
            ("alias", "Prog/alias_c.v", "Module S := Symbols\n  .Plain.\nDefinition E : Z := S.s_crc_table.\n",
             alias + ":1: Symbols .Plain is used as a module"),
            ("a submodule", "Prog/sec_c.v", "Import Symbols.Plain.Sec.\nDefinition G : Z := s_got.\n",
             "lib/Prog/sec_c.v:1: Symbols.Plain.Sec is used as a module"),
            # after `Require Import Symbols`, Plain is Symbols.Plain (or an image module of the same name)
            ("Import after Require Import Symbols", "Prog/bare_c.v",
             "From " + HARNESS_THEORY + " Require Import Symbols.\n(* c *) Import Plain.\n"
             "Definition G : Z := Sec.s_got.\n", "lib/Prog/bare_c.v:2: Plain is used as a module"),
            ("in a required file", "Lib/Mem.v", CONTRACT_LIB["Lib/Mem.v"] + "Module S := Symbols.Ubsan.Size.\n",
             "lib/Lib/Mem.v:3: Symbols.Ubsan.Size is used as a module"),
            # the root module: `Require Symbols` then `Import Symbols` is `Require Import Symbols`, and an alias of it
            # makes S.Plain.s_x, which no reference shows
            ("an Import of the root module", "Prog/root_c.v",
             "From " + HARNESS_THEORY + " Require Symbols.\nImport Symbols.\nImport Plain.\n"
             "Definition E : Z := s_LLVMFuzzerTestOneInput.\n", "lib/Prog/root_c.v:2: Symbols is used as a module"),
            ("an alias of the root module", "Prog/root_alias_c.v",
             "From " + HARNESS_THEORY + " Require Symbols.\nModule S := Symbols.\n"
             "Definition E : Z := S.Plain.s_crc_table.\n", "lib/Prog/root_alias_c.v:2: Symbols is used as a module"),
            ("a qualified Import of the root module", "Prog/root_q_c.v",
             "From " + HARNESS_THEORY + " Require Symbols.\nExport " + NAMESPACE + ".zlib\n"
             "  .checksum_fuzzer.Symbols.\nDefinition E : Z := Plain.s_crc_table.\n",
             "lib/Prog/root_q_c.v:2: " + NAMESPACE + ".zlib .checksum_fuzzer.Symbols is used as a module"),
            ("the root module in a required file", "Lib/Deep.v",
             "From " + HARNESS_THEORY + " Require Symbols.\nInclude Symbols.\n"
             + CONTRACT_LIB["Lib/Deep.v"], "lib/Lib/Deep.v:2: Symbols is used as a module"))
        for what, rel, text, reason in cases:
            with self.subTest(what), tree() as t:
                base = contract_repo(t)
                t.write("%s/%s" % (LIB, rel), text)
                got = self.keys(t, commit(t), base)
                unknown = {p: (r["key"], r["why"]) for p, r in got.items() if r["state"] == "unknown"}
                full = reason + ", so the names it brings into scope cannot be read"
                want = [ENTRY, CRC] if rel.startswith("Lib/") else ["%s/%s" % (LIB, rel)]
                self.assertEqual(unknown, {p: (None, full) for p in want})
                self.assertEqual({r["state"] for p, r in got.items() if p not in want}, {"keyed"})
        with tree() as t:
            t.write("%s/%s" % (LIB, cases[1][1]), cases[1][2])
            base = contract_repo(t)
            t.write("%s/%s" % (LIB, cases[1][1]), "Definition E : Z := Symbols.Plain.s_crc_table.\n")
            self.assertEqual(self.whys(t, commit(t), base)["%s/%s" % (LIB, cases[1][1])], "unknown at the base")

    def test_an_image_module_imported_whole_keeps_the_key(self):
        """A fuzz target's image modules have the build modules' names (Plain): with no Require Import of Symbols, a
        bare Plain is the image module, and the contract is keyed, as `Require Symbols` with qualified names is."""
        with tree() as t:
            base = contract_repo(t)
            image = "%s/Prog/image_c.v" % LIB
            t.write(image, "From " + HARNESS_THEORY + ".images Require Import Plain.\nImport Plain.\n"
                           "From " + HARNESS_THEORY + " Require Symbols.\n"
                           "Definition E : Z := Symbols.Plain.s_LLVMFuzzerTestOneInput.\n")
            row = self.keys(t, commit(t), base)[image]
            self.assertEqual((row["state"], refs(row), row["why"]),
                             ("keyed", [ENTRY_REFS[1]], "not at the base"))

    def test_a_release_naming_a_namespace_keys_the_same_files_and_references(self):
        """With release.yaml naming another namespace and opam stem (OSSV-162), the proof library's modules have the
        new namespace: each contract requires the same files and reads the same symbols as under the default; and the
        dune-project component holds the project's stanza of the new stem, so a change to it changes every key."""
        with tree() as t:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            base = contract_repo(t, NEW_NAMESPACE)
            got = self.keys(t, base, None)
            self.assertEqual(sorted(got), [CRC, ENTRY, STATE, TABLE])
            self.assertEqual({r["state"] for r in got.values()}, {"keyed"})
            self.assertEqual(refs(got[ENTRY]), ENTRY_REFS)
            self.assertEqual(refs(got[CRC]), [("plain", "Sec.s_got", ".got", "resolved", "section"),
                                              ("plain", "Size.s_crc_table", "crc_table", "resolved", "object"),
                                              ("plain", "s_crc32_z_llvm_42", "crc32_z.llvm.42", "resolved", "func")])
            text = t.read("dune-project")
            self.assertIn("(name rocq-oss-verify-zlib)", text)
            t.write("dune-project", text.replace("(name rocq-oss-verify-zlib)",
                                                 "(name rocq-oss-verify-zlib)\n (tags (z))"))
            self.assertEqual(self.whys(t, commit(t), base),
                             {p: "changed: dune-project" for p in (CRC, ENTRY, STATE, TABLE)})

    def test_the_references_and_the_components_that_differ_are_data(self):
        """Each reference with its build, its path in the build's module as written, the symbol it resolves to, if
        any, and that symbol's kind; each component whose id differs from the base's with its type, and for a symbol
        its build, its name and its kind and size at each commit; how the base compared, with why the base's key is
        unknown; and why written from them."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, ".got", exact="6b" * 32)
            put_row(t, "crc_table", size=2048)
            t.write("%s/Lib/Deep.v" % LIB, CONTRACT_LIB["Lib/Deep.v"] + "Definition deeper := 0.\n")
            t.write(TABLE, CONTRACT_LIB["Prog/table_c.v"] + "(* changed *)\n")
            t.write("theories/Extra.v", "Definition extra := 1.\n")
            got = self.keys(t, commit(t), base)

            def other(component, kind):
                return {"component": component, "type": kind, "build": None, "name": None, "before": None,
                        "after": None}

            def sym(name, kind, before, after):
                return {"component": "plain:" + name, "type": "symbol", "build": "plain", "name": name,
                        "before": {"kind": kind, "size": before}, "after": {"kind": kind, "size": after}}

            self.assertEqual({p: (r["base"], r["base_unknown"], r["unknown"], r["changed"]) for p, r in got.items()
                              if p in (CRC, TABLE)},
                             {CRC: ("keyed at the base", None, None,
                                    [other("lib/Lib/Deep.v", "library"), sym(".got", "section", 16, 16),
                                     sym("crc_table", "object", 1024, 2048), other("theories", "environment")]),
                              TABLE: ("keyed at the base", None, None,
                                      [other("contract", "contract"), other("theories", "environment")])})
            self.assertEqual((got[CRC]["why"], got[TABLE]["why"]),
                             ("changed: lib/Lib/Deep.v, plain:.got, plain:crc_table, theories",
                              "changed: contract, theories"))
        with tree() as t:
            obj = "%s/Prog/obj_c.v" % LIB
            t.write(obj, "Definition O : Z := Symbols.Plain.s_g_new.\n")
            base = contract_repo(t)
            pin, rows = symbols.load(t.path(FACT))
            symbols.write(t.path(FACT), sorted(rows + [symbols.Sym("g_new", "object", 0x15010, 8, "-", "-", "-",
                                                                   "-")],
                                               key=lambda r: (r.address, r.name)), pin)
            row = self.keys(t, commit(t), base)[obj]
            self.assertEqual((row["state"], row["base"], row["base_unknown"], row["changed"], row["why"]),
                             ("keyed", "unknown at the base", "lib/Prog/obj_c.v:1: Symbols.Plain.s_g_new cannot be "
                              "resolved: the symbol fact of plain has no row that Symbols.v names s_g_new", None,
                              "unknown at the base"))

    def test_oft_plan_contracts_prints_each_contract_as_json(self):
        with tree() as t:
            base = contract_repo(t)
            t.write(TABLE, CONTRACT_LIB["Prog/table_c.v"] + "(* changed *)\n")
            head = commit(t)
            buf = io.StringIO()
            self.assertEqual(contracts.run(t.root, UNIT, change=head, base=base, out=buf), 0)
            self.assertEqual(json.loads(buf.getvalue()), self.keys(t, head, base))
            buf = io.StringIO()
            self.assertEqual(contracts.run(t.root, CX_UNIT, change=head, out=buf), 1)
            self.assertEqual(buf.getvalue(), "%s: no contract file at %s\n" % (CX_UNIT, head))

    def test_oft_plan_contracts_on_the_command_line_refuses_a_verdict_store(self):
        """`oft plan --contracts` prints contract_keys.  A contract key is a work key, never a basis for reusing a
        verdict, so --store is refused; so is every other option of the parts' plan (--tools, --units, --pr-kind,
        --rocqchk), which no contract key reads."""
        with tree() as t:
            base = contract_repo(t)
            t.write(TABLE, CONTRACT_LIB["Prog/table_c.v"] + "(* changed *)\n")
            head = commit(t)
            oft = [sys.executable, "-B", "-m", "oft", "--root", t.root, "plan", "--contracts", UNIT]
            env = dict(os.environ, PYTHONPATH=TOOLS)
            done = subprocess.run(oft + ["--change", head, "--base", base], capture_output=True, text=True, env=env)
            self.assertEqual((done.returncode, json.loads(done.stdout)), (0, self.keys(t, head, base)), done.stderr)
            for extra, named in ((["--store", head], "--store"),
                                 (["--store", head, "--pr-kind", "maintainer"], "--pr-kind, --store")):
                done = subprocess.run(oft + extra, capture_output=True, text=True, env=env)
                self.assertEqual((done.returncode, done.stdout, done.stderr),
                                 (2, "", "oft plan: --contracts reads only --change and --base, not %s\n" % named))

    def test_contracts_is_not_the_checker(self):
        """keys.NOT_THE_CHECKER names contracts.py, so a change to it re-checks no fuzz target; that holds only while
        a check opens it not, so oft.check, with oft.facts and oft.fetch, does not import it."""
        self.assertTrue(keys.not_the_checker("tools/oft/contracts.py"))
        done = subprocess.run([sys.executable, "-c", "import sys, oft.check, oft.facts, oft.fetch; "
                               "print('oft.contracts' in sys.modules)"],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=TOOLS))
        self.assertEqual((done.returncode, done.stdout), (0, "False\n"), done.stderr)

