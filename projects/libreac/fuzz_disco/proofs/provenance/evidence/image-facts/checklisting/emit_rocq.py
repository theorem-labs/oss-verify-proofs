#!/usr/bin/env python3
"""emit_rocq.py -- the Rocq files of the position-abstract listing, for any target.

Input: the DIR that mklisting.py wrote (listing.json, listing.body).
Output, in the proof tree given by --dst, for --name Grant --prefix grant (the defaults):
  GrantSyms.v   `Inductive gsym`: the call-target names the listing uses (GS_<name>)
  GrantList.v   AF_<fn> (offset of each function from the listing's base) and `grant_listing`
  GrantAddr.v   the addresses of this image: grant_text, grant_sigma, grant_obj, grant_hi, with
                no proof (the image instance checks them against the image)
The symbol type is <first letter of --prefix>sym, its constructors <FIRST LETTER>S_<name>.

  --lib MODULE.lib and --sub A.Prog: the files Require `From <lib>.<sub> Require Import <table>
    <Name>Syms` (fuzz_grant image B: --sub B.Prog).
  --cells SHADOW_CELL,UAR_CELL: the two cells the walks read through a GOT word and no slot
    builds (the shadow-base cell, __asan_shadow_memory_dynamic_address, and the use-after-return
    flag, __asan_option_detect_stack_use_after_return). They are appended after the listing's
    objects, as numbers len(objs) and len(objs)+1, and the numbers are printed. A cell the
    listing already builds keeps its number. --extra-obj INDEX=ADDR,... (the older form, which
    states the numbers) still works.
  --style grant|cmd: the comment and licence lines. grant (default) is the form fuzz_grant's
    committed files have; cmd is the ProgCmd form of fuzz_command (no notice line on Syms.v, the upstream
    library's notice words, `Local Set Warnings "-abstract-large-number"` in List.v, Addr.v
    Requires only <Name>Syms).
  --tables match|list: grant_obj / grant_hi as a `match` (default, fuzz_grant's form) or as
    lists read by `nth` (fuzz_command's form: with 116 objects and 303 values a list keeps the
    range lemmas of the image instance one vm_compute each).
"""
import argparse
import json
import os

GEN_LINE = ("(* Machine-generated data computed from the task's compiled program image (decoder-built "
            "tables and encoded data blocks); may contain fragments of third-party object code - see "
            "NOTICE. No Anthropic licence header applies to this file. *)\n")
WORDS_LINE = {
    "grant": ("(* This file states or restates instruction words of the task's compiled program "
              "(third-party object code: libreac and the harness, compiled with the memory-checking "
              "runtime) for use in the proofs - see NOTICE. No Anthropic licence header is applied "
              "to this file. *)\n"),
    "cmd": ("(* This file states or restates instruction words of the task's compiled program "
            "(third-party object code: the upstream library at its pinned commit, the C library, "
            "the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. "
            "No Anthropic licence header is applied to this file. *)\n"),
}


def ident(n):
    """A Rocq identifier: the symbol's name with every other character as '_'."""
    return "".join(c if (c.isalnum() or c == "_") else "_" for c in n)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("gen")
    ap.add_argument("--dst", required=True)
    ap.add_argument("--lib", default="OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib",
                    help="module path of the harness's lib")
    ap.add_argument("--sub", default="A.Prog", help="the listing's subdirectory of lib (B.Prog for image B)")
    ap.add_argument("--name", default="Grant", help="file prefix")
    ap.add_argument("--prefix", default="grant", help="identifier prefix")
    ap.add_argument("--target", default="fuzz_grant", help="the harness's name, for comments")
    ap.add_argument("--table", default="PaTable", help="module of the pinstr type (cgif YP0b copy)")
    ap.add_argument("--cells", default="", help="SHADOW_CELL,UAR_CELL (hex)")
    ap.add_argument("--extra-obj", default="",
                    help="INDEX=ADDR,... : objects no slot builds, at the numbers given (older form "
                         "of --cells)")
    ap.add_argument("--style", choices=("grant", "cmd"), default="grant")
    ap.add_argument("--tables", choices=("match", "list"), default="match")
    args = ap.parse_args()
    m = json.load(open(os.path.join(args.gen, "listing.json")))
    body = open(os.path.join(args.gen, "listing.body")).read()
    os.makedirs(args.dst, exist_ok=True)
    N, p, sub = args.name, args.prefix, args.sub
    ty = p[0].lower() + "sym"
    cs = p[0].upper() + "S_"
    if args.cells and args.extra_obj:
        ap.error("give --cells or --extra-obj, not both")

    objs = list(m["objs"])
    extra = []
    for part in (args.extra_obj.split(",") if args.extra_obj else []):
        k, v = part.split("=")
        extra.append((int(k, 0), int(v, 16)))
    cells = [int(c, 16) for c in args.cells.split(",") if c]
    if args.cells and len(cells) != 2:
        ap.error("--cells takes two addresses: SHADOW_CELL,UAR_CELL")
    for what, c in zip(("shadow-base cell", "use-after-return flag cell"), cells):
        if c in objs:
            print("%s 0x%x: object %d (the listing builds it)" % (what, c, objs.index(c)))
        else:
            print("%s 0x%x: object %d" % (what, c, len(objs)))
            objs.append(c)
    if extra and args.tables == "list":
        if sorted(i for i, _ in extra) != list(range(len(objs), len(objs) + len(extra))):
            ap.error("--tables list needs --extra-obj numbers right after the listing's objects")
        objs += [a for _, a in sorted(extra)]
        extra = []
    has_cells = bool(cells or extra)

    syms = [ident(s) for s, _ in m["syms"]]
    with open(os.path.join(args.dst, N + "Syms.v"), "w") as f:
        if args.style == "grant":
            f.write(GEN_LINE)
        f.write("(* The names the listing of %s's program code calls: the memory-checking\n"
                "   runtime's entries, the wrappers' trampolines, and the program functions that\n"
                "   have their own contract. *)\n" % args.target)
        f.write("From Stdlib Require Import ZArith.\n")
        f.write("Inductive %s : Type :=\n" % ty)
        f.write("\n".join("| %s%s" % (cs, s) for s in syms) + ".\n")

    funcs = sorted(((ident(k), v) for k, v in m["funcs"].items()), key=lambda kv: kv[1])
    with open(os.path.join(args.dst, N + "List.v"), "w") as f:
        f.write(WORDS_LINE[args.style])
        f.write("(* %s's program code as a position-abstract listing: one slot per\n"
                "   4-byte instruction from the entry function's address upwards. *)\n" % args.target)
        f.write("From %s.%s Require Import %s %sSyms.\n" % (args.lib, sub, args.table, N))
        f.write("From Stdlib Require Import ZArith List.\n")
        f.write("From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.\n")
        f.write("From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n")
        f.write("Import ListNotations.\n")
        if args.style == "cmd":
            f.write("Local Set Warnings \"-abstract-large-number\".\n")
        f.write("Open Scope bv_scope. Open Scope Z_scope.\n")
        for nm, off in funcs:
            f.write("Definition AF_%s : Z := 0x%x.\n" % (nm, off))
        f.write("Definition %s_nslots : nat := %d%%nat.\n" % (p, m["nslots"]))
        f.write("Definition %s_listing : ptable %s := [\n" % (p, ty))
        f.write(body.rstrip().rstrip(";") + "\n")
        f.write("].\n")

    with open(os.path.join(args.dst, N + "Addr.v"), "w") as f:
        if args.style == "grant":
            f.write(GEN_LINE)
            f.write("(* The addresses %s.asan gives the listing's names, objects and\n"
                    "   auipc values. %sImg.v checks them against the image." % (args.target, N))
            if has_cells:
                f.write(" The objects past the\n"
                        "   ones the slots build are the cells the walks read through a GOT word:\n"
                        "   __asan_shadow_memory_dynamic_address (the shadow base) and\n"
                        "   __asan_option_detect_stack_use_after_return.")
            f.write(" *)\n")
            f.write("From %s.%s Require Import %s %sSyms.\n" % (args.lib, sub, args.table, N))
        else:
            f.write(GEN_LINE)
            f.write("(* The addresses %s's image gives the listing's names, objects and\n"
                    "   auipc values. The PAImg instance checks them against the image. *)\n" % args.target)
            f.write("From %s.%s Require Import %sSyms.\n" % (args.lib, sub, N))
        f.write("From Stdlib Require Import ZArith List.\n")
        f.write("Import ListNotations.\nOpen Scope Z_scope.\n")
        f.write("Definition %s_text : Z := 0x%x.\n" % (p, m["lo"]))
        f.write("Definition %s_sigma (s : %s) : Z :=\nmatch s with\n" % (p, ty))
        for s, a in m["syms"]:
            f.write("| %s%s => 0x%x\n" % (cs, ident(s), a))
        f.write("end.\n")
        if args.tables == "match":
            f.write("Definition %s_obj (i : nat) : Z :=\nmatch i with\n" % p)
            for i, a in enumerate(objs):
                f.write("| %d%%nat => 0x%x\n" % (i, a))
            for i, a in sorted(extra):
                f.write("| %d%%nat => 0x%x\n" % (i, a))
            f.write("| _ => 0\nend.\n")
            f.write("Definition %s_hi (j : nat) : Z :=\nmatch j with\n" % p)
            for j, a in enumerate(m["his"]):
                f.write("| %d%%nat => 0x%x\n" % (j, a))
            f.write("| _ => 0\nend.\n")
            f.write("Definition %s_nobj : nat := %d%%nat.\n"
                    % (p, max([len(objs)] + [i + 1 for i, _ in extra])))
            f.write("Definition %s_nhi : nat := %d%%nat.\n" % (p, len(m["his"])))
        else:
            f.write("Definition %s_objs : list Z := [\n%s].\n" % (p, ";\n".join("0x%x" % a for a in objs)))
            f.write("Definition %s_his : list Z := [\n%s].\n" % (p, ";\n".join("0x%x" % a for a in m["his"])))
            f.write("Definition %s_obj (i : nat) : Z := nth i %s_objs 0.\n" % (p, p))
            f.write("Definition %s_hi (j : nat) : Z := nth j %s_his 0.\n" % (p, p))
            f.write("Definition %s_nobj : nat := length %s_objs.\n" % (p, p))
            f.write("Definition %s_nhi : nat := length %s_his.\n" % (p, p))
    print("wrote %sSyms.v (%d names), %sList.v (%d slots, %d functions), %sAddr.v (%d objects, %d auipc values)"
          % (N, len(syms), N, m["nslots"], len(funcs), N, len(m["objs"]), len(m["his"])))


if __name__ == "__main__":
    main()
