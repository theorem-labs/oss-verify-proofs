#!/usr/bin/env python3
"""mk_manifest.py [--dir DIR] [--out FILE] -- write the MANIFEST of evidence/gates-Y from the role table below.

One line per file: `<path relative to DIR> <kind> <sha256> <role>`. kind: script = script of record; table = per-value
table; gate = gate record; input = input a script reads. The sha256 is measured on the file in DIR at run time. Refuses
(exit 1, nothing written) when a file in DIR has no role here, or a role names a file DIR does not hold.
Default DIR: this script's directory; default FILE: DIR/MANIFEST.
"""
import argparse
import hashlib
import os
import sys

HEADER = """\
# evidence/gates-Y: gate records re-run on the series base b1afc3e80791 against the image B pin (fuzz_disco.asan-ubsan,
# sha256 cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146): lib/Reusable/Y* (and the start-up files
# YB01 YB03 YB05 YB12 YD1k YD2i YD2j YF0m YCej YB13 YB1q YF0l), lib/Y and lib/B. Proves no function (kind: measurement).
# These records carry the values of the image B files no script reproduces. Each gate record gives the command with
# every argument (host paths as the variables run.sh names), the tool's full sha256, the verdict, the counts, and a
# planted control that fired. Tools that only check are cited by name and sha256 and are not copied. G7-G9 add the
# address checker of record 3d2eee813cce, roundconst v2 (kept donor geometry by value) and the count recompute; G10
# adds the address checker 0d24592683b6 (installed 2026-10-30 23:46Z) beside G7; G11 adds 205a90fd19b8 (installed
# 2026-10-31 08:00Z), run with 0d24592683b6 on the series tree d57e4e79e469 (the base with the unit's later fixes).
# One line per file: path (relative to this directory), kind, sha256, role.
# kind: script = script of record; table = per-value table; gate = gate record; input = input a script reads.
"""

PAC_LIMITS = (
    "Registered limits of port_addr_check (classes that can read EQUAL where the meaning differs): SAME-CONTENT across "
    "two different symbols whose strings agree up to the NUL; INSN-SAME on a jal / auipc / lui word compares opcode + rd "
    "only; ROUND-CONSTANT-SAME passes a page-multiple value without reading it (G8 reads it by value); predict mode's "
    "MAPS-STRING maps by string content alone; the named-symbol rule depends on the donor's recovered symbols")

PAC0D_LIMITS = (
    "Limits of port_addr_check 0d24592683b6 as its owner lists them (its version record: the Limits section and the "
    "0d24592683b6 entry): the named-symbol rule is absolute only where the target's symbols are the image's own (an "
    "unstripped twin); with recovered symbols (stripped pins, G10's command (1)) the donor must still corroborate, so a "
    "value the donor already had wrong passes (command (2), PIN:TWIN, lifts it); SAME-CONTENT and predict mode's "
    "MAPS-STRING still decide by string content where neither side names a symbol; a jal / auipc / lui word is compared "
    "modulo relocation immediates and is not re-decoded against the target image (a jal re-pointed where no fetch pc "
    "places it is INSN-CHANGED only when the two words differ); ROUND-CONSTANT-SAME still passes a page-multiple value "
    "in no geometry slot and inside no named symbol (G8, roundconst v2, reads it by value); address versus size is "
    "decided by name and context, a NON-ADDRESS numeral is compared by value only, and an in-range decimal is an "
    "address only as a symbol start, boundary, GOT slot, xref, jump-table cell, call return site or decimal copy of a "
    "hex code address of the same file; a donor object no symbolised build carries, or an END whose preceding object "
    "the donors cannot name, is UNRESOLVED; SLID-TO-NEIGHBOUR covers single cells and windows of at most 0x100 bytes; "
    "--assign auto marks a tie between the two ASan images AMBIGUOUS; run from its read-only version directory it "
    "needs --cache (every command here passes one)")

PAC205_LIMITS = (
    "Limits of port_addr_check 205a90fd19b8 as its owner lists them (its version record: the 205a90fd19b8 entry and "
    "Limits): a SAME-SYMBOL match on an anonymous or local symbol or a bare section offset checks no target bytes (3 "
    "rows here, hand-off state words of YB01 / YB03); GENERATOR-FILL can report a checkable cell as fill (115 rows "
    "here); the addend of q * G + G is in no size-role slot; FAIL-OPEN: a cell naming another function than the one at "
    "its value passes SAME-SYMBOL when one name contains the other (0 rows move to SAME-SYMBOL here); the size slots "
    "miss round_up-like granule arguments and camel-case size names (measured: the rf-name plant at kUserMapSize "
    "passes on image B); the list of 9873fe3cf51b stands (a relocated quotient in change .. with N can pass "
    "SAME-SYMBOL, lost pairings, a non-deterministic auto image choice elsewhere, no donor-on-donor harness control, "
    "start read as the previous end, a kept donor count not caught, a code-pointer cell accepting another symbol when "
    "the value equals the pin word, moves by address caught only inside .got, SAME-CONTENT where neither side names a "
    "symbol, the named-symbol rule absolute only against the image's own .symtab, mmap flags outside a flag slot, a "
    "13-bit branch immediate read as a .got quantity, the AT_HWCAP range); address versus size is decided by name and "
    "context and a NON-ADDRESS numeral is compared by value only; UNRESOLVED, SLID-TO-NEIGHBOUR (0x100), instruction "
    "words modulo relocation immediates and AMBIGUOUS as for 0d24592683b6. Measured here, not in its list: a geometry "
    "quantity in a bound or size-name slot is compared with the donor's value, so the target's right value flags "
    "(YB13.v:150, YD1g.v:1277) and a kept donor value passes")

ROLES = [
    ("run.sh", "script",
     "re-runs every gate of this directory (g1-g11) on the series base (g11 on the series tree) against the image B "
     "pin; every input is an environment variable it names (no host path); checks the sha256 of each tool and pin "
     "before it runs; writes to $WORK only, and compares the donordec/ tables, G1-flagged-rows.tsv, G8-rows.tsv, "
     "G9-counts.tsv, G10-rows.tsv, G11-rows.tsv and this MANIFEST with the shipped bytes (cmp)"),
    ("mk_manifest.py", "script", "writes this MANIFEST from its role table and the measured sha256 of each file"),
    ("G1-address-check.md", "gate",
     "address checker port_addr_check efa19b81e92b (images keyed A / B / P / U, --fail-on-flags) over the cgif donor lib "
     "c8557374ad2e paired with lib/Reusable/Y*: command, counts, verdict, planted control; lib/Y and lib/B have no cgif "
     "counterpart file (stated with counts). " + PAC_LIMITS),
    ("G1-flagged-rows.tsv", "gate",
     "per-row triage of all 27544 rows G1-address-check.md flags (verdict, image, file:line, values, rule, measured "
     "detail): 0 untriaged, 0 defects; written by g1_triage.py from the checker's output, re-derived by run.sh (cmp)"),
    ("g1_triage.py", "script",
     "writes G1-flagged-rows.tsv: the first rule that holds for each flagged row, measuring on the pins and twins (the "
     "listing's words, the symbol table, string contents, PT_LOADs, the start-up shadow); every path an argument; exit "
     "0 only when every row has a rule and none is a defect"),
    ("G2-donor-decimals.md", "gate",
     "by-value donor-stale numeral check (donordec/donor_decimals.py) over lib/Reusable, lib/Y and lib/B at the base: "
     "old-version equality, negative and positive controls, funnel, triage of every unexplained row"),
    ("donordec/donor_decimals.py", "script",
     "decimal literals that are a cgif address and not the same object in fuzz_disco; every path an argument; "
     "byte-identical to gates-A/donordec/donor_decimals.py; its rows equal the earlier version's (sha256 e7d879e2ed9c) "
     "on the same inputs (G2-donor-decimals.md)"),
    ("donordec/funnel.py", "script",
     "classifies donor_decimals.py rows (NOT-IN-DONOR, SIZE, ODD-IN-CODE, INSN-IMM, LABEL, DISCO-POINTER, UNEXPLAINED); "
     "every path an argument; byte-identical to gates-A/donordec/funnel.py"),
    ("donordec/scan_Y.tsv", "table",
     "donor_decimals.py output on the base, lib/Reusable + lib/Y + lib/B, against the image B pin (and the image A pin "
     "for the files both ASan builds read); re-derived by run.sh (cmp)"),
    ("donordec/funnel_Y.txt", "table", "funnel.py output on donordec/scan_Y.tsv; re-derived by run.sh (cmp)"),
    ("donordec/control_neg.tsv", "table",
     "negative control: donor_decimals.py with cgif as the target over cgif's own lib c8557374ad2e: 0 rows; "
     "re-derived by run.sh (cmp)"),
    ("donordec/control_pos_AE23.tsv", "table",
     "positive control: cgif's lib/A/AE23.v line 471 planted as a fuzz_disco lib/A file: 1 row; re-derived by run.sh (cmp)"),
    ("donordec/control_pos_YE23.tsv", "table",
     "positive control on image B: a copy of lib/Reusable/YE23.v with line 474's 6277920 (fuzz_disco buf+0x8) replaced "
     "by cgif's 6265120 (cgif buf+0x8): 1 row; re-derived by run.sh (cmp)"),
    ("G3-codeptr.md", "gate",
     "codeptr 12348302dfd2 of the start-up set of record 2026-10-30d on the 12 image B start-up files, per-file "
     "declarations read from each file, the control of record (codeptr-controls.sh), planted control. Registered limit "
     "of codeptr: a literal in the same slot as a donor address passes when both images hold the same file bytes there, "
     "so a CELL naming a different symbol passes when its value equals the pin word"),
    ("G4-ifchk.md", "gate",
     "ifchk f5cde600cc18 (start-up set 2026-10-30d): YF0m cells x the 50 YB01 hand-off states against the image B pin, "
     "planted control"),
    ("G5-cells.md", "gate",
     "cellcheck cc60c6705e6f, ownedcheck b663903ddda1, shadowcheck e04173f5a5a5 and covcheck 595119b27d0c on "
     "lib/Reusable/YF0m.v, IMG_TOP 0x5fe000 from the pin's PT_LOADs, one planted control each"),
    ("G6-kimg-overlap.md", "gate",
     "kimg_overlap 5db341e3cd62 (FROZEN) on YB05 / YF0m / YD1k: VOID (the tool reads no entity in these files; the "
     "planted control does not fire); the same tool on YB01 / YB03 / YD2j, which hold the forms it reads, with controls"),
    ("G7-address-check-3d2e.md", "gate",
     "port_addr_check 3d2eee813cce, the address checker of record now, with G1's command and file set (fresh cache): "
     "FLAGGED 27544 in 13 classes as G1; the row diff from G1's table: 0 rows (byte-equal rows); g1_triage.py on its "
     "table reproduces G1-flagged-rows.tsv (cmp, 0 untriaged, 0 defects); the PIN:TWIN variant measured; planted "
     "control fired; covers the same proofs/libreac/fuzz_disco/lib/Reusable/Y*.v files as G1. " + PAC_LIMITS),
    ("G8-roundconst.md", "gate",
     "roundconst v2 32b39f3b34e9 (kept donor image geometry, by value) on G7's full table, four builds keyed against the "
     "four pins and their twins: 239221 kept rows selected, 3502 not SAME (MISMATCH 1354, MIXED 2144, NO-COUNTERPART 4); "
     "its README's controls (donor on donor 0 non-SAME; a kept donor PT_LOAD length, word count and small table length "
     "planted in copies of image B files, each one MISMATCH more; the gap control SAME); every non-SAME row triaged "
     "(G8-rows.tsv: 0 untriaged, 0 DEFECT); covers proofs/libreac/fuzz_disco/lib/Reusable/Y*.v. Registered limits of "
     "roundconst v2 (its README's named gaps): a small kept donor quantity whose value is also a right target quantity "
     "reads SAME (shown by the gap control); an unnamed run that does not pair is not gated at any size; function sizes "
     "and extents, and quantities of non-allocated sections, are not quantities of it (G9 recomputes the counts these "
     "leave)"),
    ("G8-rows.tsv", "gate",
     "per-row triage of all 3502 non-SAME rows of G8 (class, rule, status, key, file:line, value, roundconst class, the "
     "measured fact, the text read): GENERATED 349, ROLE 3153, DEFECT 0, UNTRIAGED 0; written by rc_triage.py from "
     "roundconst's output, re-derived by run.sh (cmp)"),
    ("rc_triage.py", "script",
     "writes G8-rows.tsv: for each non-SAME roundconst row the first stated rule that holds (generated start-up file, or "
     "the numeral's role read from its sentence), measuring on the pins and twins where the rule names an image fact "
     "(pin words, decoded immediates, function and object extents, frame sizes, p_align, `addi a7` syscall numbers, "
     "__malloc_size_classes); reads roundconst's own quantity names; every path an argument; exit 0 only when every row "
     "has a rule and none is a defect"),
    ("G9-counts.md", "gate",
     "every image-derived count of lib/Reusable/Y*.v (1364: code range and build_table word counts, table lengths, "
     "sizes, slices, segment spans, extents) recomputed from the four pins and their twins by a stated rule, with cgif's "
     "own count beside it: MEASURED TRUE 494, NOT-A-COUNT 868, DIFFERS 2 (lib/Reusable/YE34.v:24 38 -> 36 and :20 435 "
     "-> 383: donor code-range counts kept, ruled defects by the unit owner, fixed in the series commit b0078622dec, "
     "build check pending); YB1v.v:10 16102 MEASURED TRUE; YB1t.v:28 (0x64c74, 30) ruled KEEP; planted control fired; "
     "covers what roundconst v2's gaps leave (small kept counts, unnamed runs, function sizes) for "
     "proofs/libreac/fuzz_disco/lib/Reusable/Y*.v"),
    ("G9-counts.tsv", "gate",
     "one row per count of G9 (key, form, name / call, shipped, rule, recomputed, measurement, images, donor shipped, "
     "donor recomputed, verdict, status, note, accept = the unit owner's ruling); written by count_recompute.py, "
     "re-derived by run.sh (cmp)"),
    ("count_recompute.py", "script",
     "finds every count of lib/Reusable/Y*.v by fixed text patterns and recomputes it from the pin and twin of the build "
     "the file is read against (and the donor's from cgif's pin and twin) by the rule its docstring states; rulings are "
     "--accept arguments; every path an argument; exit 0 only when every DIFFERS row is ruled; writes G9-counts.tsv"),
    ("G10-address-check-0d24.md", "gate",
     "port_addr_check 0d24592683b6 (installed 2026-10-30 23:46Z) with G1's command and file set, fresh cache: FLAGGED "
     "27572 in 14 classes (G7: 27544 in 13); the row diff from G7's table: 129 rows, 91 in the note only and 38 in the "
     "verdict (28 passes become findings: KIND-CHANGED 12, STALE-DONOR-CODE-POINTER 11, SAME-VALUE-DIFFERENT-OBJECT 4, "
     "INSN-CHANGED 1; 10 passes stay passes); the PIN:TWIN form against 3d2eee813cce's: 130 rows (the same and "
     "YH03.v:18); g1_triage.py keeps G1's rule for every row G7 flags; every changed row triaged (G10-rows.tsv: 0 "
     "untriaged, 0 defects); planted control fired; covers the proofs/libreac/fuzz_disco/lib/Reusable/Y*.v files of "
     "G1. G7 and G1 stand beside it. " + PAC0D_LIMITS),
    ("G10-rows.tsv", "gate",
     "one row per row G10's two runs change against 3d2eee813cce (run, old and new verdict, image, file:line, sentence, "
     "idx, values, rule, measured detail): NOTE-ONLY 182, and the 77 verdict moves each by a measured rule "
     "(ALLOC-MAP-SIZE, CAPACITY-DOUBLING, FOOTPRINT-LENGTH, FAKESTACK-OFFSET, LOOSE-ENTRY-BOUND, JAL-SAME-CALLEE, "
     "STARTUP-CELL-VALUE, RUNTIME-BLOCK-SIZE, ABORTED-GOAL, SIZE0-END-NEXT-CELL); UNTRIAGED 0; written by "
     "g10_triage.py, re-derived by run.sh (cmp)"),
    ("g10_triage.py", "script",
     "writes G10-rows.tsv: diffs two port_addr_check tables row by row (same keys required), and gives each row whose "
     "verdict moved the first stated rule that holds, measuring on the pins and twins (lui immediates inside named "
     "allocator and stack-depot functions, ecall words, jal targets, symbol sizes) and the lib trees (kernel-checked "
     "lemma statements, table extents, readers of a cell); checks that every row g1_triage.py leaves untriaged is one "
     "of them; every path an argument; exit 0 only when no row is untriaged"),
    ("G11-address-check-205a.md", "gate",
     "port_addr_check 205a90fd19b8 (installed 2026-10-31 08:00Z) with G1's command and file set on the series tree "
     "d57e4e79e469, fresh caches, and 0d24592683b6 run again on the same tree: FLAGGED 27574 in 14 classes against "
     "27583 (PIN:TWIN 27575 against 27584); the row diff: 715 rows, 98 in the note only and 617 in the verdict (599 "
     "passes stay passes, 11 findings become passes by G10's rules, 5 findings change class, 2 passes become "
     "NON-ADDRESS-CHANGED findings at YB13.v:150 and YD1g.v:1277, which hold the target's own measured geometry); 0 rows "
     "move from DIFFERENT-SYMBOL or UNMEASURED-NAME to SAME-SYMBOL; every changed row and every flagged row "
     "g1_triage.py leaves untriaged triaged (G11-rows.tsv: 0 untriaged, 0 defects); G1's planted control fired; the "
     "owner's granule plant fires in the syscall-arg and arith-operand slots and passes 0d24592683b6, and passes both "
     "at kUserMapSize on image B; kept donor geometry passes both; covers the proofs/libreac/fuzz_disco/lib/Reusable/"
     "Y*.v files of G1. G10, G7 and G1 stand beside it. " + PAC205_LIMITS),
    ("G11-rows.tsv", "gate",
     "one row per row G11's two pairs of runs change (part diff) and per flagged row g1_triage.py leaves untriaged "
     "(part flagged): run, part, old and new verdict, image, file:line, sentence, idx, values, rule, measured detail; "
     "NOTE-ONLY 196, UNCHANGED-PASS 1190 (with the numeral's role read from its line), ALLOC-MAP-SIZE 40, "
     "CAPACITY-DOUBLING 12, FAKESTACK-OFFSET 4, LOOSE-ENTRY-BOUND 4, SAME-G1-RULE 10, TARGET-GEOMETRY 4, "
     "FOOTPRINT-LENGTH 2, JAL-SAME-CALLEE 2, SIZE0-END-NEXT-CELL 1; UNTRIAGED 0; written by g11_triage.py, re-derived "
     "by run.sh (cmp)"),
    ("g11_triage.py", "script",
     "writes G11-rows.tsv: diffs the tables of 0d24592683b6 and 205a90fd19b8 on one tree row by row (same keys "
     "required) and gives each row whose verdict moved the first stated rule that holds (g10_triage.py's rules, the "
     "rule g1_triage.py gives on both tables, the PT_LOAD quantities of the fuzz_disco and cgif pins), and each flagged "
     "row g1_triage.py leaves untriaged a g10_triage.py rule; a row that moves from DIFFERENT-SYMBOL or UNMEASURED-NAME "
     "to SAME-SYMBOL gets no rule; every path an argument; exit 0 only when no row is untriaged"),
]


def sha256(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=os.path.dirname(os.path.abspath(__file__)))
    ap.add_argument("--out")
    a = ap.parse_args()
    out = a.out or os.path.join(a.dir, "MANIFEST")
    have = set()
    for d, _, fs in os.walk(a.dir):
        for f in fs:
            rel = os.path.relpath(os.path.join(d, f), a.dir)
            if rel != "MANIFEST" and not rel.endswith(".pyc") and "__pycache__" not in rel:
                have.add(rel)
    named = [r for r, _, _ in ROLES]
    bad = sorted(have - set(named)) + sorted(set(named) - have)
    if bad or len(named) != len(set(named)):
        sys.exit("mk_manifest: REFUSED: no role for, or no file for: %s" % ", ".join(bad or ["a repeated role"]))
    lines = [HEADER.rstrip("\n")]
    for rel, kind, role in ROLES:
        assert kind in ("script", "table", "gate", "input") and " " not in rel
        lines.append("%s %s %s %s" % (rel, kind, sha256(os.path.join(a.dir, rel)), role))
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("mk_manifest: %d entries -> %s" % (len(ROLES), os.path.relpath(out, a.dir) if out.startswith(a.dir) else out))


if __name__ == "__main__":
    main()
