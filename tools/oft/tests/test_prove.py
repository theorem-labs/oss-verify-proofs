"""prove.py (oft prove, ./theorem prove): between a base and a head commit of one fuzz target, the class of each
function of each build, each contract's state, and the source lines of each function that changed, in one report."""
import io
import json
import os
import subprocess
import sys
import unittest

from oft import prove, symbols
from oft.tests.helpers import REPO, tree
from oft.tests.test_contracts import CONTRACT_LIB, CRC, ENTRY, FACT, LIB, STATE, TABLE, contract_repo, put_row
from oft.tests.test_keys import TOOLS, UNIT, commit

LLVM = "plain:LLVMFuzzerTestOneInput"


def add_row(t, sym):
    """Add sym to UNIT's plain symbol fact."""
    pin, rows = symbols.load(t.path(FACT))
    symbols.write(t.path(FACT), sorted(rows + [sym], key=lambda r: (r.address, r.name)), pin)


def func(name, address, label, lines="-"):
    """A stand-in function of 8 bytes: label marks its exact and its masked bytes."""
    return symbols.Sym(name, "func", address, 8, label * 32, label[::-1] * 32, lines)


def contract(r, path):
    return next(c for c in r.contracts if c["file"] == path)


def states(r):
    return {c["file"]: c["state"] for c in r.contracts}


def unchanged(*paths):
    return {p: "unchanged" for p in paths}


def fn(name, cls, lines="-"):
    """A function of the plain build as a contract's row of the report lists it."""
    return {"build": "plain", "name": name, "class": cls, "lines": lines}


def components(row):
    """The names of the work-key components of a contract's row that differ from the base's, or None."""
    return None if row["changed"] is None else [c["component"] for c in row["changed"]]


class Prove(unittest.TestCase):
    """The fixture: test_contracts.contract_repo, four contracts of zlib/checksum_fuzzer (entry names
    LLVMFuzzerTestOneInput, crc names crc32_z.llvm.42 and .got, table names crc_table, state names _start, g_file_len
    and .bss) and the plain build's stand-in symbol fact, at a base commit and at a head commit."""

    def report(self, t, base, head):
        return prove.report(t.root, UNIT, base, head)

    def test_a_changed_function_marks_its_contract_needs_work(self):
        """A function a contract names whose instructions are other (changed), new (added) or gone (removed): the
        contract needs work, and why names the function and its class.  A contract that names a function the head
        lacks has no work key there; the function is the one the base's symbol fact gives that name."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32, lines="fuzz/checksum.c:3-9")
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, STATE, TABLE), **{ENTRY: "needs work"}))
            entry = contract(r, ENTRY)
            self.assertEqual((entry["why"], components(entry), entry["functions"]),
                             (LLVM + " changed", [LLVM],
                              [fn("LLVMFuzzerTestOneInput", "changed", "fuzz/checksum.c:3-9")]))
        with tree() as t:
            gone = "%s/Prog/gone_c.v" % LIB
            t.write(gone, "Definition G : Z := Symbols.Plain.s_unused.\n")
            base = contract_repo(t)
            put_row(t, "unused")
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, STATE, TABLE), **{gone: "needs work"}))
            row = contract(r, gone)
            self.assertEqual((row["why"], row["functions"]),
                             ("plain:unused removed; lib/Prog/gone_c.v:1: Symbols.Plain.s_unused cannot be resolved: "
                              "the symbol fact of plain has no row that Symbols.v names s_unused",
                              [fn("unused", "removed")]))
        with tree() as t:
            new = "%s/Prog/new_c.v" % LIB
            t.write(new, "Definition N : Z := Symbols.Plain.s_newfn.\n")
            base = contract_repo(t)
            add_row(t, func("newfn", 0x11320, "7a", "zlib/new.c:1-4"))
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, STATE, TABLE), **{new: "needs work"}))
            self.assertEqual(contract(r, new)["why"],
                             "plain:newfn added; at the base: lib/Prog/new_c.v:1: Symbols.Plain.s_newfn cannot be "
                             "resolved: the symbol fact of plain has no row that Symbols.v names s_newfn")
            self.assertEqual(contract(r, new)["functions"], [fn("newfn", "added", "zlib/new.c:1-4")])

    def test_an_identifier_the_head_cannot_resolve_is_never_read_as_a_name(self):
        """A contract names Symbols.Plain.s_unused, the identifier of the function unused (a function named s_unused
        has the identifier s_s_unused).  The head removes unused alone: the reference is resolved through the base's
        identifiers to unused, removed, and is never read as the name of the function s_unused, identical."""
        with tree() as t:
            add_row(t, func("s_unused", 0x11320, "7a"))
            gone = "%s/Prog/gone_c.v" % LIB
            t.write(gone, "Definition G : Z := Symbols.Plain.s_unused.\n")
            base = contract_repo(t)
            put_row(t, "unused")
            r = self.report(t, base, commit(t))
            self.assertEqual([(b, row.cls) for b, row in r.rows if row.names == ("s_unused",)],
                             [("plain", "identical")])
            row = contract(r, gone)
            self.assertEqual((row["state"], row["functions"]), ("needs work", [fn("unused", "removed")]))
            self.assertEqual(row["why"], "plain:unused removed; lib/Prog/gone_c.v:1: Symbols.Plain.s_unused cannot be "
                                         "resolved: the symbol fact of plain has no row that Symbols.v names s_unused")

    def test_a_symbol_name_with_a_comma_is_one_name(self):
        """A symbol's name holds no blank, and may hold a comma: `oft prove --json` names the function whole."""
        with tree() as t:
            add_row(t, func("comma,name", 0x11320, "7a", "zlib/comma.c:1-2"))
            comma = "%s/Prog/comma_c.v" % LIB
            t.write(comma, "Definition C : Z := Symbols.Plain.s_comma_name.\n")
            base = contract_repo(t)
            put_row(t, "comma,name", exact="1e" * 32, masked="2d" * 32)
            head = commit(t)
            done = subprocess.run([sys.executable, "-B", "-m", "oft", "--root", t.root, "prove", UNIT, "--base", base,
                                   "--head", head, "--json"], capture_output=True, text=True,
                                  env=dict(os.environ, PYTHONPATH=TOOLS))
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            row = next(c for c in json.loads(done.stdout)["contracts"] if c["file"] == comma)
            self.assertEqual((row["state"], row["why"], row["functions"], row["references"]),
                             ("needs work", "plain:comma,name changed",
                              [fn("comma,name", "changed", "zlib/comma.c:1-2")],
                              [{"build": "plain", "written": "s_comma_name", "name": "comma,name", "status": "resolved",
                                "kind": "func"}]))

    def test_a_changed_contract_file_is_a_changed_contract(self):
        """A contract whose own file changed, or is new, is a changed contract, whatever else changed with it: also one
        with no work key, and one whose checkout attributes alone changed (its key's contract component)."""
        with tree() as t:
            base = contract_repo(t)
            t.write(TABLE, CONTRACT_LIB["Prog/table_c.v"] + "Definition TABLE_END : Z := TABLE + 1.\n")
            t.write(ENTRY, CONTRACT_LIB["Prog/entry_c.v"] + "(* the entry's contract, changed *)\n")
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32)
            added = "%s/Prog/added_c.v" % LIB
            t.write(added, "Definition A : Z := Symbols.Plain.s_crc_table.\n")
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, STATE),
                                             **{p: "changed contract" for p in (TABLE, ENTRY, added)}))
            self.assertEqual({p: contract(r, p)["why"] for p in (TABLE, ENTRY, added)},
                             {TABLE: "the contract file changed",
                              ENTRY: "the contract file changed; %s changed" % LLVM,
                              added: "the contract file is new"})
            self.assertEqual(contract(r, added)["changed"], None)
        with tree() as t:
            whole = "%s/Prog/import_c.v" % LIB
            t.write(whole, "Import Symbols.Plain.\nDefinition E : Z := s_LLVMFuzzerTestOneInput.\n")
            base = contract_repo(t)
            t.write(whole, "Import Symbols.Plain.\nDefinition E : Z := s_crc32_z_llvm_42.\n")
            t.write(".gitattributes", t.read(".gitattributes") + "%s eol=crlf\n" % STATE)
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, TABLE),
                                             **{whole: "changed contract", STATE: "changed contract"}))
            self.assertEqual({p: (contract(r, p)["why"], components(contract(r, p))) for p in (whole, STATE)},
                             {whole: ("the contract file changed; lib/Prog/import_c.v:1: Symbols.Plain is used as a "
                                      "module, so the names it brings into scope cannot be read", None),
                              STATE: ("the contract file changed", ["contract"])})

    def test_a_name_is_the_function_the_head_gives_it(self):
        """Two static functions named dummy at the base, one of them gone at the head: a contract that names dummy at
        the head names the one the head kept (identical), not the removed one; its key is unknown at the base, where
        Symbols.v gives the shared name no identifier."""
        with tree() as t:
            add_row(t, func("dummy", 0x11320, "7a"))
            add_row(t, func("dummy", 0x11330, "8b"))
            dummy = "%s/Prog/dummy_c.v" % LIB
            t.write(dummy, "Definition D : Z := Symbols.Plain.s_dummy.\n")
            base = contract_repo(t)
            pin, rows = symbols.load(t.path(FACT))
            symbols.write(t.path(FACT), [s for s in rows if (s.name, s.address) != ("dummy", 0x11320)], pin)
            r = self.report(t, base, commit(t))
            self.assertEqual(sorted((row.cls, row.base.address) for b, row in r.rows if row.names == ("dummy",)),
                             [("identical", 0x11330), ("removed", 0x11320)])
            row = contract(r, dummy)
            self.assertEqual((row["state"], row["functions"]), ("unknown", [fn("dummy", "identical")]))
            self.assertTrue(row["why"].startswith("at the base: lib/Prog/dummy_c.v:1: Symbols.Plain.s_dummy cannot be "
                                                  "resolved"), row["why"])

    def test_a_key_that_differs_for_another_reason_needs_work(self):
        """A contract whose work key differs from the base's with every function it names as it was: why names the
        components that differ (a section's bytes; a file of the proof library it requires)."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, ".got", exact="6b" * 32)
            t.write("%s/Lib/Deep.v" % LIB, CONTRACT_LIB["Lib/Deep.v"] + "Definition deeper := 0.\n")
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(STATE, TABLE), **{ENTRY: "needs work", CRC: "needs work"}))
            self.assertEqual({p: (contract(r, p)["why"], components(contract(r, p))) for p in (ENTRY, CRC)},
                             {ENTRY: ("changed: lib/Lib/Deep.v", ["lib/Lib/Deep.v"]),
                              CRC: ("changed: lib/Lib/Deep.v, plain:.got", ["lib/Lib/Deep.v", "plain:.got"])})

    def test_a_contract_whose_data_alone_changed_is_data_changed(self):
        """Ruling 22: a contract whose work key differs only in the bytes of data objects or sections it names, each
        of the same kind and size at both commits, is data changed: Rocq decides, and no agent is predicted.  A data
        symbol whose size changed still needs work."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, ".got", exact="6b" * 32)
            put_row(t, "crc_table", exact="7c" * 32)
            put_row(t, "g_file_len", size=16)
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), {CRC: "data changed", ENTRY: "data changed", TABLE: "data changed",
                                         STATE: "needs work"})
            self.assertEqual({p: contract(r, p)["why"] for p in (CRC, ENTRY, TABLE, STATE)},
                             {CRC: "changed: plain:.got, plain:crc_table", ENTRY: "changed: plain:crc_table",
                              TABLE: "changed: plain:crc_table", STATE: "changed: plain:g_file_len"})

    def test_a_rebuild_that_edits_no_proof_predicts_no_work(self):
        """As the proof repair of libreac's pull request 35 rebuilt its harness: harness.yaml with other pins and
        another check, the source with another line, Statements.v with another comment and a statement no contract
        requires, a file of the proof library with another comment, and a section's bytes moved by the relink.  No
        contract file changed and no agent is predicted: crc, which names the section, is data changed, and every
        other contract is unchanged."""
        with tree() as t:
            base = contract_repo(t)
            folder = "projects/zlib/checksum_fuzzer/"
            y = t.yaml(folder + "harness.yaml")
            y["builds"]["plain"]["sha256"] = "5a" * 32
            y["checks"][0]["what"] += " Again."
            t.put_yaml(folder + "harness.yaml", y)
            t.write(folder + "source/checksum_fuzzer.c", t.read(folder + "source/checksum_fuzzer.c") + "/* x */\n")
            t.write(folder + "Statements.v", "(* another subject *)\n" + t.read(folder + "Statements.v")
                    + "Definition another := 0.\n")
            t.write("%s/Lib/Deep.v" % LIB, "(* the table's length *)\n" + CONTRACT_LIB["Lib/Deep.v"])
            put_row(t, ".got", exact="6b" * 32)
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(ENTRY, STATE, TABLE), **{CRC: "data changed"}))
            self.assertEqual(contract(r, CRC)["why"], "changed: plain:.got")

    def test_a_contract_file_deleted_at_the_head_is_removed(self):
        with tree() as t:
            base = contract_repo(t)
            os.remove(t.path(TABLE))
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, STATE), **{TABLE: "removed"}))
            row = contract(r, TABLE)
            self.assertEqual((row["why"], row["base"], row["changed"], row["references"], row["functions"]),
                             ("the contract file is gone", None, None, [], []))
            self.assertIn("| `Prog/table_c.v` | removed | the contract file is gone |", prove.markdown(r))

    def test_a_moved_function_leaves_its_contract_unchanged(self):
        """crc32_z.llvm.42 at another address with other exact bytes and the same masked bytes: its proof checks
        again with no edit."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "crc32_z.llvm.42", address=0x11400, exact="1e" * 32)
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), unchanged(CRC, ENTRY, STATE, TABLE))
            self.assertEqual(contract(r, CRC)["functions"], [fn("crc32_z.llvm.42", "moved")])
            self.assertEqual(contract(r, CRC)["why"], "unchanged from the base")

    def test_a_contract_with_no_work_key_is_unknown(self):
        """No function it names changed, and its work key cannot be computed at the head, or at the base: why carries
        the reason."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "_start")
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, TABLE), **{STATE: "unknown"}))
            self.assertEqual(contract(r, STATE)["why"], "lib/Prog/state_c.v:1: Symbols.Plain.s__start cannot be "
                                                        "resolved: the symbol fact of plain has no row that Symbols.v "
                                                        "names s__start")
        with tree() as t:
            obj = "%s/Prog/obj_c.v" % LIB
            t.write(obj, "Definition O : Z := Symbols.Plain.s_g_new.\n")
            base = contract_repo(t)
            add_row(t, symbols.Sym("g_new", "object", 0x15010, 8, "-", "-", "-"))
            r = self.report(t, base, commit(t))
            self.assertEqual(states(r), dict(unchanged(CRC, ENTRY, STATE, TABLE), **{obj: "unknown"}))
            self.assertEqual(contract(r, obj)["why"], "at the base: lib/Prog/obj_c.v:1: Symbols.Plain.s_g_new cannot "
                                                      "be resolved: the symbol fact of plain has no row that "
                                                      "Symbols.v names s_g_new")

    def test_counts_are_per_class(self):
        """One function of each class; data objects, sections and functions of size 0 are not counted."""
        with tree() as t:
            add_row(t, func("kept", 0x11318, "4f"))
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32)
            put_row(t, "crc32_z.llvm.42", address=0x11400, exact="1e" * 32)
            put_row(t, "unused")
            add_row(t, func("newfn", 0x11320, "7a"))
            put_row(t, ".got", exact="6b" * 32)
            put_row(t, "g_file_len", size=16)
            r = self.report(t, base, commit(t))
            self.assertEqual(r.counts, {"identical": 1, "moved": 1, "changed": 1, "added": 1, "removed": 1})
            self.assertEqual(sorted((b, row.cls, row.names) for b, row in r.rows),
                             [("plain", "added", ("newfn",)), ("plain", "changed", ("LLVMFuzzerTestOneInput",)),
                              ("plain", "identical", ("kept",)), ("plain", "moved", ("crc32_z.llvm.42",)),
                              ("plain", "removed", ("unused",))])

    def test_the_markdown_names_each_changed_function_with_its_lines(self):
        """Each changed, added or removed function, on a line with its build, its class and its source lines (a
        removed function's from the base); no moved or identical function is named."""
        with tree() as t:
            contract_repo(t)
            put_row(t, "unused", lines="zlib/unused.c:5-8")
            base = commit(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32,
                    lines="fuzz/checksum.c:3-9,zlib/crc32.c:10-12")
            put_row(t, "crc32_z.llvm.42", address=0x11400, exact="1e" * 32)
            put_row(t, "unused")
            add_row(t, func("newfn", 0x11320, "7a", "zlib/new.c:1-4"))
            md = prove.markdown(self.report(t, base, commit(t)))
            for name, cls, lines in (("LLVMFuzzerTestOneInput", "changed",
                                      ("fuzz/checksum.c:3-9", "zlib/crc32.c:10-12")),
                                     ("newfn", "added", ("zlib/new.c:1-4",)),
                                     ("unused", "removed", ("zlib/unused.c:5-8",))):
                with self.subTest(name=name):
                    line = [l for l in md.splitlines() if "`%s`" % name in l and "plain" in l and cls in l]
                    self.assertEqual(len(line), 1, md)
                    for span in lines:
                        self.assertIn(span, line[0])
            self.assertNotIn("crc32_z.llvm.42", md)
            self.assertIn("| `Prog/entry_c.v` | needs work | %s changed |" % LLVM, md)

    def test_the_same_commit_as_base_and_head_changes_nothing(self):
        with tree() as t:
            head = contract_repo(t)
            r = self.report(t, "HEAD", "HEAD")
            self.assertEqual((r.base, r.head), (head, head))
            self.assertEqual({c: n for c, n in r.counts.items() if n}, {"identical": 3})
            self.assertEqual(set(states(r).values()), {"unchanged"})
            self.assertIn("No function changed, was added or was removed.", prove.markdown(r))

    def test_oft_prove_json_holds_each_contract_s_state_and_why_and_each_function_s_class(self):
        """The change ledger reads it: the predicted state of each contract with what made it, and every function's
        class in every build."""
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32, lines="fuzz/checksum.c:3-9")
            head = commit(t)
            done = subprocess.run([sys.executable, "-B", "-m", "oft", "--root", t.root, "prove", UNIT, "--base", base,
                                   "--head", head, "--json"], capture_output=True, text=True,
                                  env=dict(os.environ, PYTHONPATH=TOOLS))
            self.assertEqual(done.returncode, 0, done.stderr)
            got = json.loads(done.stdout)
            r = self.report(t, base, head)
            self.assertEqual((got["unit"], got["base"], got["head"], got["counts"], got["contracts"]),
                             (UNIT, base, head, r.counts, r.contracts))
            self.assertIn({"build": "plain", "class": "changed", "names": ["LLVMFuzzerTestOneInput"],
                           "lines": "fuzz/checksum.c:3-9", "base": {"address": "0x11270", "size": 108},
                           "head": {"address": "0x11270", "size": 108}}, got["functions"])
            self.assertEqual(len(got["functions"]), len(r.rows))

    def test_theorem_passes_its_arguments_to_oft(self):
        with tree() as t:
            base = contract_repo(t)
            put_row(t, "LLVMFuzzerTestOneInput", exact="1e" * 32, masked="2d" * 32, lines="fuzz/checksum.c:3-9")
            head = commit(t)
            done = subprocess.run([os.path.join(REPO, "theorem"), "--root", t.root, "prove", UNIT, "--base", base,
                                   "--head", head], capture_output=True, text=True)
            self.assertEqual((done.returncode, done.stderr), (0, ""))
            self.assertEqual(done.stdout, prove.markdown(self.report(t, base, head)))

    def test_a_unit_or_a_commit_that_does_not_exist_fails(self):
        with tree() as t:
            head = contract_repo(t)
            for unit, ref, says in (("zlib/nothing", head, "zlib/nothing has no symbol fact and no contract file at "
                                                          "%s or %s" % (head, head)),
                                    ("zlib", head, "a unit is <project>/<harness>, not 'zlib'"),
                                    (UNIT, "no-such-ref", "no commit 'no-such-ref'")):
                with self.subTest(unit=unit, ref=ref):
                    out = io.StringIO()
                    self.assertIsNone(prove.run(t.root, unit, ref, head, False, out))
                    self.assertEqual(out.getvalue(), "FAIL oft prove: %s\n" % says)


class WithSymbolFacts(unittest.TestCase):
    """prove.with_symbol_facts: whether each unit has a symbol fact at the base or at the head.  pr.yml's prove job
    reports and posts only on a unit that has one."""

    def test_a_symbol_fact_at_either_commit_counts(self):
        with tree() as t:
            with_fact = contract_repo(t)
            os.remove(t.path(FACT))
            without = commit(t)
            for base, head in ((with_fact, without), (without, with_fact), (with_fact, with_fact)):
                with self.subTest(base=base, head=head):
                    self.assertEqual(prove.with_symbol_facts(t.root, [UNIT, "json/fuzzer-parse_bjdata"], base, head),
                                     [(UNIT, True), ("json/fuzzer-parse_bjdata", False)])
            self.assertEqual(prove.with_symbol_facts(t.root, [UNIT], without, without), [(UNIT, False)])
            self.assertEqual(prove.with_symbol_facts(t.root, [], without, without), [])

    def test_a_unit_or_a_commit_that_does_not_exist_is_refused(self):
        with tree() as t:
            head = contract_repo(t)
            with self.assertRaises(prove.keys.NoKey):
                prove.with_symbol_facts(t.root, [UNIT], "no-such-ref", head)
            for unit in ("zlib", "zlib/a/b", "../x", "zlib/.."):
                with self.subTest(unit=unit), self.assertRaises(ValueError):
                    prove.with_symbol_facts(t.root, [unit], head, head)


if __name__ == "__main__":
    unittest.main()
