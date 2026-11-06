#!/usr/bin/env python3
"""mk_manifest.py -- writes this directory's MANIFEST: one line per file, `<path> <kind> <sha256> <role>`.

The kind and role of each file are listed below; the sha256 is computed from the file's bytes. It refuses to
write (exit 1) when a file of the directory has no role here or a role names no file.
Usage: mk_manifest.py [DIR]   (DIR defaults to this script's directory)
"""
import hashlib
import os
import sys

U = "proofs/libreac/fuzz_disco/lib"
HEAD = [
    "# evidence/image-facts: the program listings of both images and the read-only range bounds",
    "# One line per file: path (relative to this directory), kind, sha256, role.",
    "# kind: script = script of record; table = per-value table; gate = gate record; input = input a script reads.",
    "# Re-derive: run.sh PIN_A PIN_B TWIN_A TWIN_B UNIT OUT re-runs every script here and compares each output with",
    "# the table, gate record or proof file it re-derives, byte for byte. Image A (asan): extract/, then",
    "# listing-A/mklisting.py and emit_disco.py write %s/A/Prog/DiscoSyms.v, DiscoList.v, DiscoAddr.v." % U,
    "# Image B (asan-ubsan): listing-A/mklisting.py, listing-Y/repin.py, listing-Y/gen_y.py write",
    "# %s/Reusable/YI0w.v, YI0z.v, YI12.v, YCef.v, YC8i.v (and YB1v.v of the start-up data)." % U,
    "# The kernel re-checks every listing slot (pi_check); the symbol name of each address is checked only by the",
    "# gates here (checklisting, pichk, straightline, heldcheck). RELRO: extract/relro.out. Gate argument: the listed",
    "# code reads one label-minus-base jump table, 9 int32 entries at 0x212b8 (both images; their .rodata is equal).",
]
ROLES = [
    ("run.sh", "script", "Re-runs every script of this directory from its files (all inputs as arguments) and "
     "compares each output with its table, gate record or proof file by cmp; exit 1 on any difference."),
    ("mk_manifest.py", "script", "Writes this MANIFEST from the roles it lists and the files' sha256."),
    ("extract/symbol_table.py", "script", "Writes the symbol table of an unstripped twin in `nm -S --size-sort` "
     "form, with one-word header lines naming the twin's and the pin's sha256 and that PT_LOAD 2..4 of twin and pin "
     "are byte-equal (it refuses otherwise). Ties of equal size and name are ordered by address; no such tie is a "
     "function in a listed range, so the order cannot change a listing."),
    ("extract/symbols-asan.txt", "input", "Symbol table extract of the asan twin (fuzz_disco.asan): the source of "
     "every symbol name and address in the image A listing (DiscoAddr.v's names, DiscoList.v's call targets)."),
    ("extract/symbols-asan-ubsan.txt", "input", "Symbol table extract of the asan-ubsan twin: the source of every "
     "symbol name and address in the image B listing (YI12.v tfib_sigma, YI0z.v's function offsets)."),
    ("extract/image_facts.py", "script", "Writes the section and segment facts of a pin: PT_LOAD table and count, "
     "allocated sections, the read-only-after-relocation range (.data.rel.ro start .. .got end), and the one .got "
     "slot that holds each given cell."),
    ("extract/facts-asan.txt", "table", "Facts of the asan pin: RELRO 9fee0..a1208, PT_LOAD count 4, the .got slots "
     "a0510 / a0568 of the shadow-base and use-after-return cells a90b8 / a90c0 (DiscoAddr.v objects 66 / 67)."),
    ("extract/facts-asan-ubsan.txt", "table", "Facts of the asan-ubsan pin: RELRO a0280..a15a8 and PT_LOAD count 4 "
     "(gen_y.py's arguments; YCbj.v tfib_relro_img, pa_relro_lo/hi), the .got slots a08b0 / a0908 of the cells "
     "a9478 / a9480 (YI12.v objects 0 / 1 / 12 / 13)."),
    ("extract/symbol_facts.py", "script", "Gives the listing range (start of LLVMFuzzerTestOneInput .. end of "
     "reac_ports_parse) and a symbol's address from a symbol table extract."),
    ("extract/relro_check.py", "script", "Gate: checks the RELRO literals of a proof file against a pin's facts."),
    ("extract/relro.out", "gate", "RELRO check verdict: %s/A/Prog/DiscoImg.v disco_relro_lo/hi and "
     "%s/Reusable/YCbj.v pa_relro_lo/hi equal the pins' .data.rel.ro start and .got end (4 of 4 equal). The same Y "
     "literals in YRoBelow.v are tied to YCbj.v's by conversion: its instance tfib_ro_below_ofl applies the lemma "
     "stated with them to PB_tfib's pa_relro_lo/hi, so a different literal would not type-check." % (U, U)),
    ("listing-A/mklisting.py", "script", "Reads a pin and its symbol table extract and writes the position-abstract "
     "listing of the program code range: instruction slots, call / tail targets, auipc values and the objects auipc "
     "pairs build (listing.json, listing.body). Used for both images."),
    ("listing-A/emit_disco.py", "script", "Writes %s/A/Prog/DiscoSyms.v, DiscoList.v and DiscoAddr.v from the image "
     "A listing, adding the two cells that only a GOT word reaches as objects 66 and 67 (--extra-obj). This version "
     "differs from the one that wrote them only in its docstring; its output is byte-identical." % U),
    ("listing-A/call-list.txt", "input", "The image A program functions reached by a call slot instead of being "
     "walked through (mklisting.py --call)."),
    ("listing-A/gen/listing.json", "table", "Per-value table of the image A listing: each symbol name with its "
     "address, each object address, each auipc value, each function offset, the slot count and range."),
    ("listing-A/checklisting.A.out", "gate", "Listing check verdict on the shipped DiscoList.v / DiscoAddr.v / "
     "DiscoSyms.v: 8567 slots, 0 failing, 105 auipc pairs with 0 failing, 38 function offsets = 38 function symbols."),
    ("listing-A/straightline.py", "script", "Gate: reports any auipc-to-use pair that a branch, jump, jump-table "
     "entry or data pointer can split; exit 1 on any report."),
    ("listing-A/straightline.S3a.json", "gate", "That gate's verdict on the image A listing: 105 pairs, 0 reported."),
    ("listing-A/pichk.A.out", "gate", "Slot check verdict on the image A listing: 0 bad slots of 8567."),
    ("listing-Y/repin.py", "script", "Moves given addresses to the object numbers the earlier unit's frame files "
     "name (0 / 1: the two .got slots, 12 / 13: the two cells) and renumbers the listing body to match."),
    ("listing-Y/gen_y.py", "script", "Writes %s/Reusable/YI0w.v, YI0z.v, YI12.v, YCef.v, YC8i.v and YB1v.v from the "
     "image B listing (also the first versions of YCbj.v and YXcalls.v, to which later commits added kernel-checked "
     "lines). This version takes as arguments what the one that wrote them had as constants: the RELRO range, the "
     "PT_LOAD count, the end of .text and the addresses of sysconf and oft_exit_guard (the last three only for "
     "YB1v.v); its docstring is neutral; its output is byte-identical." % U),
    ("listing-Y/call-b.txt", "input", "The image B program functions reached by a call slot (mklisting.py --call). "
     "The recorded list was lost; this one is rebuilt from YI0z.v's function offsets, and the listing re-derived "
     "from it equals the shipped files byte for byte."),
    ("listing-Y/gen/listing.json", "table", "Per-value table of the image B listing after repin.py: symbol names and "
     "addresses, objects, auipc values, function offsets, slot count and range."),
    ("listing-Y/pichk.py", "script", "Gate: an independent re-implementation of the kernel's slot check over a "
     "generated listing against the pin. This version imports mklisting.py from this directory tree."),
    ("listing-Y/pichk.Y.out", "gate", "Slot check verdict on the image B listing: 0 bad slots of 8769."),
    ("listing-Y/heldcheck.py", "script", "Gate: reports any auipc-to-use pair of a listing that control flow can "
     "split. This version imports mklisting.py from this directory tree."),
    ("listing-Y/heldcheck.b.out", "gate", "That gate's verdict on the image B listing: 107 pairs, 0 unsound."),
    ("listing-Y/checklisting.Y.out", "gate", "Listing check verdict on the image B listing rendered by emit_rocq.py: "
     "8769 slots, 0 failing, 107 auipc pairs with 0 failing, 40 function offsets = 40 function symbols."),
    ("checklisting/checklisting.py", "script", "Gate: re-checks a listing's three files against the pin without "
     "sharing code with the generator: every slot word, call and tail target, auipc pair, function offset and "
     "symbol address."),
    ("checklisting/emit_rocq.py", "script", "Renders a listing into the three files checklisting.py reads; used for "
     "the image B listing, whose shipped files use the earlier unit's file layout and names. This version differs "
     "from the one of record only in two docstring lines."),
]


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    files = sorted(os.path.relpath(os.path.join(d, f), root) for d, _ds, fs in os.walk(root) for f in fs)
    files = [f for f in files if f != "MANIFEST"]
    named = [p for p, _k, _r in ROLES]
    if sorted(named) != files:
        sys.exit("files without a role: %s; roles without a file: %s"
                 % (sorted(set(files) - set(named)), sorted(set(named) - set(files))))
    lines = list(HEAD)
    for p, k, r in ROLES:
        h = hashlib.sha256(open(os.path.join(root, p), "rb").read()).hexdigest()
        lines.append("%s %s %s %s" % (p, k, h, r))
    open(os.path.join(root, "MANIFEST"), "w").write("\n".join(lines) + "\n")
    print("MANIFEST: %d files" % len(ROLES))


if __name__ == "__main__":
    main()
