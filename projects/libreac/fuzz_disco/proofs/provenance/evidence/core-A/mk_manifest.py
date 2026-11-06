#!/usr/bin/env python3
"""mk_manifest.py [DIR] -- writes DIR/MANIFEST (default: this script's directory).

One line per file under DIR except MANIFEST: `<path relative to DIR> <kind> <sha256> <role>`, kind = script | input |
table | gate, sorted by path. The kind and role of each file are in ROLES below; the script stops if a file has no
role or a role names a file that does not exist, so the MANIFEST always names exactly the files of the directory.
"""
import hashlib, os, sys

L = 'proofs/libreac/fuzz_disco/lib/A/'
HEADER = """\
# evidence/core-A: relocated runtime and allocator core, image A (fuzz_disco.asan, the released asan pin).
# One line per file: path (relative to this directory), kind, sha256, role.
# kind: script = script of record; table = per-value table; gate = gate record; input = input a script reads.
# run.sh REPO A_PIN B_PIN DONOR_PIN DONOR_B_PIN GATE_SCRIPT GATE_DONORS GATE_CACHE A_TWIN D9E0_DIR OUTDIR re-runs every
# script here and compares each output with the shipped file or table; it exits 0 only if all are equal. Re-derived byte
# for byte: AB1w.v (ab1w/), AE3i.v (ae3i/), the generated blocks of AF0m.v (af0m/), and the 13 runtime memory walks
# AE2q, AE2r, AE6l..AE6v except their line 4, a provenance comment set by hand at landing (memwalks13/). d9e0check/
# re-runs the 13 walks with port_core d9e0589898fd (best available, not of record) and records the per-file
# classification and its four checks. The other relocated core values have no script: tables/ holds their per-value
# tables and the gate tables that checked each one against the released image; the gates-A directory re-runs those
# checks on the series base, and the pin-keyed address checks of gates-A / gates-Y (port_addr_check efa19b81e92b) cover
# the relocated core as a whole.
# No binary is shipped: the unstripped twin of the asan image is read only through twin/ (a text extract checked
# against the released pin), and the pins are arguments (their sha256 are in projects/*/harness.yaml).
"""

ROLES = {
    'mk_manifest.py': ('script', 'Writes this MANIFEST from the files of this directory and their roles.'),
    # twin/
    'twin/extract_twin.py': ('script', 'Writes the text extract of an unstripped twin (section headers, symbol table) after it checks that PT_LOAD 2..4 of the twin and the released pin are byte-equal.'),
    'twin/fuzz_disco.asan.twin.txt': ('input', 'Section headers and symbol table of the unstripped twin of the released asan pin (extract_twin.py output; its header names the twin and pin sha256). Read by ab1w/ and memwalks13/ instead of the twin binary.'),
    'twin/twin_syms.py': ('script', 'Reads the twin extract with the pyelftools calls the scripts here use on an unstripped twin (sections by name, symbols).'),
    # kit/
    'kit/rvelf.py': ('script', 'ELF64 reader and RV64GC decoder used by the relocation and function-pairing scripts (instruction lengths, pc-relative and auipc-paired immediates); the tool of record with neutral tool names in its docstring.'),
    # inputs/
    'inputs/mk_donor_syms.py': ('script', 'Writes inputs/cgif_file_fuzzer.asan.syms.txt from the address checker\'s symbol recovery of the donor image: the data lines unchanged, one neutral header line naming the donor pin sha256.'),
    'inputs/cgif_file_fuzzer.asan.syms.txt': ('input', 'Symbols (name, address, size) recovered for the stripped donor asan image of cgif_file_fuzzer (sha256 7093581aab04...), read by ab1w/gen_symtab.py, ab1w/resolve_code.py and memwalks13/ as the donor symbols.'),
    # tables/
    'tables/project.py': ('script', 'Writes a shipped table from its working table without changing a value: drops comment lines, a column of people\'s names, or attribution clauses in free text. Applied to overrides-718254b3f4dd.tsv, code-repair.tsv, decide-AEAF.tsv, G5-verdicts.tsv, declared-c0ce.tsv.'),
    'run.sh': ('script', 'run.sh REPO A_PIN B_PIN DONOR_PIN DONOR_B_PIN GATE_SCRIPT GATE_DONORS GATE_CACHE A_TWIN D9E0_DIR OUTDIR: runs ab1w/, ae3i/, af0m/, memwalks13/ and d9e0check/ run.sh and exits 0 only if each reports every output equal to the shipped file or table.'),
    # d9e0check/
    'd9e0check/run.sh': ('script', 'The port_core d9e0589898fd command: run.sh REPO A_PIN B_PIN CGIF_ASAN CGIF_ASAN_UBSAN A_TWIN D9E0_DIR GATE_DONORS GATE_CACHE ABFD_WORK OUTDIR checks the sha256 of the pins, the twin and port_core.py (d9e0589898fd12f83fd76e086a3d7ddf3d1a43a7008dd59a73f442bff30388aa; tag directory tools/pg-reloc/d9e0589898fd, its own symbol gate gate/port_addr_check.py 309d2e5f7e01bb114fcb60339a9069fd765eae0b265f3f8ebffd17697f932349; a check tool here, cited, not copied), runs it once, check only (no --apply), on the same inputs as memwalks13/ (files13.txt, the override row and the patch; the twin binary for --target-syms), then classify.py and checks.py, and compares their outputs with the two shipped tables. port_core d9e0589898fd exits 0 with its symbol gate PASS.'),
    'd9e0check/classify.py': ('script', 'Compares each of the 13 stage-out files of the d9e0589898fd run with the abfd17f8b3d2 stage-out of memwalks13/ and with the shipped file by sha256, and classifies each file that differs as provenance-only (line 4), patched (a line the override row or the patch sets) or VALUE; exit 1 on a VALUE file.'),
    'd9e0check/classes.tsv': ('gate', 'classify.py output: per file the sha256 of the d9e0589898fd output, of the abfd17f8b3d2 output and of the shipped file, the class and the comparison with the shipped file. Result: all 13 files byte-equal to the abfd17f8b3d2 output (equal 13, provenance-only 0, patched 0, VALUE 0); each differs from the shipped file at line 4 only (the provenance comment).'),
    'd9e0check/checks.py': ('script', 'The four checks every d9e0589898fd output needs (its registry entry: 57 silent wrong rows on the relocation plant set), over the run\'s own symbol-gate table, every value recomputed from the images: (1) kept image-derived counts against the donor and target headers and symbol sizes, with /4, /8, /4096 quotients (floor 0x100 as the registered by-value gate; the hits below it are listed by value); (2) every numeral in the donor .got, GOT[0] included, ported to the same offset of the target .got; (3) shadow offsets and ASan mapping constants by role, with the shadow offset measured in both images\' code; (4) every \'no twin\' drop looked up in the target symbol table.'),
    'd9e0check/checks.txt': ('gate', 'checks.py output on the d9e0589898fd run: (1) 0 kept numerals >= 0x100 equal a donor quantity that differs in the target (the small-integer hits below 0x100 listed by value); (2) 0 numerals in the donor .got; (3) shadow offset 0x7fff8000 in the same two functions of both images, every mapping constant and shadow-range numeral kept (406 rows), 10 negative immediates kept; (4) 0 no-twin drops. All four PASS.'),
    'kit/elf_symbols.py': ('script', 'Aligns two builds of the same statically linked RV64GC program and writes the old to new address map that the relocation tool reads; the kit tool of record with a neutral name (its map\'s "tool" field and messages renamed with it).'),
    'kit/numeral_map.py': ('script', 'Classifies every numeral of Rocq files against the donor image and moves it with the address map; the kit tool of record with a neutral name (comments and messages naming the old names rewritten).'),
    # memwalks13/
    'memwalks13/tool/port_core.py': ('script', 'The relocation tool tag abfd17f8b3d2, every input an argument, the twin read through ../twin: relocates the 13 runtime memcpy / memset walk files AE2q, AE2r, AE6l..AE6v of ' + L + ' from the released cgif_file_fuzzer lib/A onto the asan image, check-only, and writes their stage-out and the tables below.'),
    'memwalks13/tool/resolve_code.py': ('script', 'Function-pairing module of the same tag, reading target symbols from the twin extract.'),
    'memwalks13/tool/deluse.py': ('script', 'Module of the same tag that port_core.py imports, unchanged.'),
    'memwalks13/run.sh': ('script', 'run.sh REPO A_PIN B_PIN DONOR_PIN DONOR_B_PIN GATE_SCRIPT GATE_DONORS GATE_CACHE OUTDIR: checks the sha256 of the pins and of the address checker, runs port_core.py with the inputs below and the checker (with its saved symbol recoveries) as symbol gate, and compares each of the 13 stage-out files with the shipped file: every line but line 4 by cmp, and line 4 exactly in its two forms. Line 4 is the provenance comment: the tool writes it with the donor image sha256; the shipped files carry the core\'s header form, a hand change of the landing, so line 4 is not re-derived. Then it compares the four tables by cmp.'),
    'memwalks13/inputs/files13.txt': ('input', 'The 13 donor-relative walk files given to the relocation tool (--files).'),
    'memwalks13/inputs/overrides-abfd17f8b3d2.tsv': ('input', 'The one hand value of the 13 walk files as an --override row: AE6t.v line 395, donor name tfib_A_musl_memset -> tfib_A_memset_libc (the retired-name rule of AB1w.v); comment lines dropped by ../tables/project.py (the tool skips them).'),
    'memwalks13/inputs/patch-abfd17f8b3d2.diff': ('input', 'The structural patch of the 13 walk files (the Zify hook line in AE2r, AE6o, AE6s, AE6t) as a --patch file.'),
    'memwalks13/tables/check.tsv': ('table', 'Every moved numeral of the 13 walk files with its rule and target symbol (79 rows), as the run writes it.'),
    'memwalks13/tables/fixed.tsv': ('table', 'The 48 values of the 13 walk files the tool set by function pairing over the kit map, as the run writes it.'),
    'memwalks13/tables/decimals.tsv': ('table', 'Decimal literals of the 13 walk files inside the image ranges: 54 excluded, 48 mapped, each with its rule, as the run writes it.'),
    'memwalks13/tables/overrides.tsv': ('table', 'Status of the override row in the run (applied).'),
    # ab1w/
    'ab1w/gen_symtab.py': ('script', 'Step 1 of ' + L + 'AB1w.v: section bounds, function ranges placed by code pairing, fake-stack, data and start-up names, every value taken from the target image and its twin extract, the donor rows from the released cgif_file_fuzzer lib/A/AB1w.v. Writes the AB1w.v of the commit before the function-row regeneration (not shipped; run.sh checks its sha256) and AB1w.tsv.'),
    'ab1w/resolve_code.py': ('script', 'Pairs donor and target code addresses by function (equal masked instruction streams) and by trampoline; loaded by gen_symtab.py.'),
    'ab1w/elfdis.py': ('script', 'Loads an ELF\'s bytes and disassembles an address range (the masked instruction streams gen_symtab.py compares); the functions gen_symtab.py calls, unchanged, from the disassembler of record.'),
    'ab1w/gen_b1w_own.py': ('script', 'Step 2 of ' + L + 'AB1w.v: rewrites the function-entry rows from the target\'s own STT_FUNC symbols in .text, with the retired-name rule (a row whose name changed meaning inside the musl text is renamed <name>_libc). Writes the shipped AB1w.v and AB1w.own.tsv.'),
    'ab1w/run.sh': ('script', 'run.sh REPO A_PIN DONOR_PIN OUTDIR: runs step 1 and step 2 and checks step 1\'s output by sha256 and the reports and the shipped AB1w.v by cmp.'),
    'ab1w/inputs/AB1w.in.v': ('input', 'The relocated AB1w.v that gen_symtab.py takes as RELOCATED.v; the lines it does not regenerate pass through. Its making was not recorded.'),
    'ab1w/AB1w.tsv': ('table', 'gen_symtab.py report: each row of AB1w.v with donor value, target value and placement method (11 section, 518 function, 6 fake-stack rows).'),
    'ab1w/AB1w.own.tsv': ('table', 'gen_b1w_own.py report: each of the 1285 function rows of the shipped AB1w.v with [A, E) and its symbol.'),
    # ae3i/
    'ae3i/ae3i.py': ('script', 'Generator of ' + L + 'AE3i.v: IMG_RO_HI from the read-only PT_LOAD of the image and img_ro_chunks as that region minus the owned ranges of AF0m.v (Tfib_owned_static). Re-derives the shipped AE3i.v byte for byte.'),
    'ae3i/run.sh': ('script', 'run.sh REPO A_PIN OUTDIR: runs ae3i.py with the shipped AE3i.v as template, and again with a template whose bounds and chunk list are blanked, and compares both outputs with ' + L + 'AE3i.v.'),
    # af0m/
    'af0m/gen_globals_cells.py': ('script', 'Generator of the asan_globals descriptor cells, their shadow cells and the zero-shadow ranges of ' + L + 'AF0m.v from the image.'),
    'af0m/globals-cells-disco-asan.txt': ('table', 'gen_globals_cells.py output on the released asan pin: 392 descriptor cells, 586 shadow cells, 25 zero-shadow ranges; each line occurs in ' + L + 'AF0m.v (Tfib_const_abs, Tfib_const_shadow, Tfib_zero_shadow). AF0m.v as a whole has no generator.'),
    'af0m/check_globals_in_af0m.py': ('script', 'Checks that each line of the globals table and each row of af0m-runtime-cells.tsv is in the matching definition of AF0m.v; exit 1 on a missing line.'),
    'af0m/cellcheck.py': ('script', 'Gate: every file-backed zN cell of a lib directory equals the image bytes at its address.'),
    'af0m/cellcheck-record.txt': ('gate', 'Written by af0m/run.sh: cellcheck.py on the shipped AF0m.v against the released asan pin (662 file-backed cells, 0 mismatch, rc 0) and on a planted control with one cell changed (1 mismatch, rc 1), with the tool, image and input sha256.'),
    'af0m/af0m-runtime-cells.tsv': ('table', 'The 110 .bss rows (address, width, value) of AF0m.v exported for the start-up state gate; no generator (each row is in Tfib_const_abs, checked by check_globals_in_af0m.py).'),
    'af0m/run.sh': ('script', 'run.sh REPO A_PIN OUTDIR: regenerates the globals table (image top read from lib/Reusable/YImgTop.v) and compares it, runs the presence check and its planted control, runs cellcheck.py and its control and compares the record.'),
    'tables/reloc-check.tsv': ('table', 'Relocation of the donor lib/A core onto the asan image: every moved numeral of ' + L + ' with file, line, donor value, staged value and class (7146 rows). The producing relocation run is not reproducible (its tool version was not recorded); the values are checked by the gate tables below.'),
    'tables/reloc-review.tsv': ('table', 'The 1435 numerals of the same relocation that the tool left for review, with the reason (settled by decide-ABCD.tsv and decide-AEAF.tsv).'),
    'tables/reloc-fixed.tsv': ('table', 'The 3 code values the relocation set by function pairing over its address map.'),
    'tables/reloc-auipc.tsv': ('table', 'The auipc-pair literals of the relocated lib/A core with their resolved values (411 rows).'),
    'tables/decide-ABCD.tsv': ('table', 'Settlement of the review rows of the AB, AC and AD files of ' + L + ' (file, line, old, new, kind, evidence; 103 rows): 53 new numerals, each present in the shipped file, and 50 rows that cite the name YImgTop.IMG_TOP instead of the image top numeral.'),
    'tables/decide-AEAF.tsv': ('table', 'Settlement of the review rows of the AE and AF files of ' + L + ' (file, line, old, new, reason; 241 rows); attribution clauses removed by project.py --neutral. 117 new values occur in the shipped files; the others later became the name YImgTop.IMG_TOP or a regenerated table, or were fixed by hand.'),
    'tables/overrides-718254b3f4dd.tsv': ('table', 'The 43 address and size values (52 positions, 17 files of ' + L + ') of the committed core that the release relocation tool 718254b3f4dd does not produce, as --override rows (file, donor line, donor value, committed value; comment lines dropped by project.py). With them every staged address or size equals the committed core except AFia.v:134, the segment-2 size 12288, which the tool\'s quotient pass rewrites to 8192 after the overrides (a known tool gap; 12288 is right: PT_LOAD 3 spans pages 0x9f000..0xa2000).'),
    'tables/REPORT-rows.tsv': ('gate', 'The numerals where the release relocation tool 718254b3f4dd (check-only run on the core) and the committed core differ, each with the tool rule, who moved it and the reason for the committed value: 189 numeral rows (168 port values right, 1 tool value right: AD1x.v:62, fixed later) and one file row for each of the 13 runtime memory walks, which memwalks13/ relocates instead. Written from the working table by project.py with no option (values unchanged; its CRLF line ends become LF).'),
    'tables/G5-verdicts.tsv': ('gate', 'Per-row verdict, measured on the released asan pin, of each value where the committed core differs from the release tool output (121 rows, each RIGHT; every value occurs in the shipped file); attribution clauses removed by project.py --neutral.'),
    'tables/G5A-rows-final-classified.tsv': ('gate', 'The rows where the release tool output still differs from the committed core after the override table, classified: region counts of the 80-region table, non-address numbers, structural edits.'),
    'tables/code-repair.tsv': ('table', 'Code literals of ' + L + ' where function pairing and the relocation map disagree, with the value taken (11 rows; the column of people\'s names dropped by project.py).'),
    'tables/got-slotmap-AEAF.tsv': ('table', 'Donor to target GOT slot map, matched by slot value, used for the GOT literals of the AE and AF files of ' + L + '.'),
    'tables/decimal-remap.tsv': ('table', 'Decimal code addresses of ' + L + ' moved by hand through the AB1w.v function-pair map (file, line, old, new; 213 rows); 199 new values occur in the shipped files, the other 14 are the model labels of model-labels.tsv and one later fix (AFfg.v 262728). No script.'),
    'tables/model-labels.tsv': ('table', 'Allocator-model check-site label numerals of ' + L + ' kept at the donor values, by file and line (42 rows).'),
    'tables/declared-c0ce.tsv': ('gate', 'Every donor-equal literal of ' + L + ' that the code-pointer check reported as kept, with its declared reason and file:line; attribution clauses removed by project.py --neutral.'),
    'tables/region-count-restate.diff': ('table', 'Hand restatement of the image-region counts and indices for the 80-region table in AD1o, AD1x, AD22, AD27, AD28, AD2d, AD2e, AD2f, AD2h of ' + L + ' (it follows the generated AD2j.v); every added line occurs in the restating commit. No script: the diff is the record.'),
    'tables/fakestack-remap.tsv': ('table', 'Per-address relocation of the fake-stack class 1 and 2 files AF0r.v, AF0s.v, AF0t.v, AF0u.v of ' + L + ' by the numeral relocation tool, before the hand function-pair edits; not re-derivable (hand edits have no record), covered by the code-pointer and decimal gates.'),
    'tables/B1w-rename-map.tsv': ('table', 'Old to new function-row name map, per address, for the retired-name rule of AB1w.v (and YB1w.v of image B): a row whose name changed meaning is renamed <name>_libc.'),
}


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    files = sorted(os.path.relpath(os.path.join(r, f), d) for r, ds, fs in os.walk(d) for f in fs
                   if f != 'MANIFEST' and '__pycache__' not in r)
    missing = [f for f in files if f not in ROLES]
    stale = [f for f in ROLES if f not in files]
    if missing or stale:
        sys.exit('mk_manifest: no role for: %s; role for absent file: %s' % (missing, stale))
    lines = [HEADER.rstrip('\n')]
    for f in files:
        kind, role = ROLES[f]
        sha = hashlib.sha256(open(os.path.join(d, f), 'rb').read()).hexdigest()
        lines.append(f'{f} {kind} {sha} {role}')
    open(os.path.join(d, 'MANIFEST'), 'w').write('\n'.join(lines) + '\n')
    print(f'mk_manifest: {len(files)} files')


if __name__ == '__main__':
    main()
