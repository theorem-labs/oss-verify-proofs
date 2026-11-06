#!/usr/bin/env python3
"""emit_disco.py -- fuzz_disco's Rocq files of the position-abstract listing.

A port, for libreac/fuzz_disco, of the Rocq emitter of the position-abstract listing used by an earlier unit.
Differences: the names (Disco*, dsym, DS_, disco_*, configurable for the asan-ubsan twin) and no
explanatory comments. Each file carries the one required notice line that the earlier unit's files carry (the
object-code notice on the listing, the generated-data notice on the names and addresses).

Input: the DIR that mklisting.py wrote (listing.json, listing.body; mklisting --prefix disco).
Output in --dst: <Pre>Syms.v, <Pre>List.v, <Pre>Addr.v.
usage: emit_disco.py GEN --dst DIR [--pre Disco] [--sym dsym] [--cons DS] [--low disco]
"""
import argparse
import json
import os
import re

GEN_LINE = "(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)\n"
WORDS_LINE = "(* This file states or restates instruction words of the task's compiled program (third-party object code: libreac and the harness, compiled with the memory-checking runtime) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)\n"


def ident(n):
    return "".join(c if (c.isalnum() or c == "_") else "_" for c in n)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("gen")
    ap.add_argument("--dst", required=True)
    ap.add_argument("--lib", default="OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib")
    ap.add_argument("--dir", default="A.Prog", help="module directory of the output files")
    ap.add_argument("--engine", default="A.Prog", help="module directory of PaTable")
    ap.add_argument("--pre", default="Disco")
    ap.add_argument("--sym", default="dsym")
    ap.add_argument("--cons", default="DS")
    ap.add_argument("--low", default="disco")
    ap.add_argument("--extra-obj", default="", help="INDEX=ADDR,... : objects no slot builds that the walks read "
                    "through a GOT word (the shadow-base cell and the use-after-return flag cell)")
    args = ap.parse_args()
    m = json.load(open(os.path.join(args.gen, "listing.json")))
    body = open(os.path.join(args.gen, "listing.body")).read()
    if args.cons != "DS":
        body = re.sub(r"\bDS_", args.cons + "_", body)
    os.makedirs(args.dst, exist_ok=True)
    P, S, C, L = args.pre, args.sym, args.cons, args.low

    syms = [ident(s) for s, _ in m["syms"]]
    assert len(set(syms)) == len(syms), "two call names map to one identifier"
    with open(os.path.join(args.dst, P + "Syms.v"), "w") as f:
        f.write(GEN_LINE)
        f.write("From Stdlib Require Import ZArith.\n")
        f.write("Inductive %s : Type :=\n" % S)
        f.write("\n".join("| %s_%s" % (C, s) for s in syms) + ".\n")

    funcs = sorted(((ident(k), v) for k, v in m["funcs"].items()), key=lambda kv: kv[1])
    with open(os.path.join(args.dst, P + "List.v"), "w") as f:
        f.write(WORDS_LINE)
        f.write("From %s.%s Require Import PaTable.\n" % (args.lib, args.engine))
        f.write("From %s.%s Require Import %sSyms.\n" % (args.lib, args.dir, P))
        f.write("From Stdlib Require Import ZArith List.\n")
        f.write("From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.\n")
        f.write("From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n")
        f.write("Import ListNotations.\nOpen Scope bv_scope. Open Scope Z_scope.\n")
        for nm, off in funcs:
            f.write("Definition AF_%s : Z := 0x%x.\n" % (nm, off))
        f.write("Definition %s_nslots : nat := %d%%nat.\n" % (L, m["nslots"]))
        f.write("Definition %s_listing : ptable %s := [\n" % (L, S))
        f.write(body.rstrip().rstrip(";") + "\n")
        f.write("].\n")

    with open(os.path.join(args.dst, P + "Addr.v"), "w") as f:
        f.write(GEN_LINE)
        f.write("From %s.%s Require Import PaTable.\n" % (args.lib, args.engine))
        f.write("From %s.%s Require Import %sSyms.\n" % (args.lib, args.dir, P))
        f.write("From %s.Reusable Require Import YImgTop.\n" % args.lib)
        f.write("From Stdlib Require Import ZArith List Lia.\n")
        f.write("Import ListNotations.\nOpen Scope Z_scope.\n")
        f.write("Definition %s_text : Z := 0x%x.\n" % (L, m["lo"]))
        f.write("Definition %s_sigma (s : %s) : Z :=\nmatch s with\n" % (L, S))
        for s, a in m["syms"]:
            f.write("| %s_%s => 0x%x\n" % (C, ident(s), a))
        f.write("end.\n")
        f.write("Definition %s_obj (i : nat) : Z :=\nmatch i with\n" % L)
        extra = sorted((int(k, 0), int(v, 16)) for k, v in
                       (part.split("=") for part in (args.extra_obj.split(",") if args.extra_obj else [])))
        for i, a in enumerate(m["objs"]):
            f.write("| %d%%nat => 0x%x\n" % (i, a))
        for i, a in extra:
            assert i >= len(m["objs"]), "an extra object index clashes with a listed object"
            f.write("| %d%%nat => 0x%x\n" % (i, a))
        f.write("| _ => 0\nend.\n")
        f.write("Definition %s_hi (j : nat) : Z :=\nmatch j with\n" % L)
        for j, a in enumerate(m["his"]):
            f.write("| %d%%nat => 0x%x\n" % (j, a))
        f.write("| _ => 0\nend.\n")
        f.write("Definition %s_nobj : nat := %d%%nat.\n" % (L, max([len(m["objs"])] + [i + 1 for i, _ in extra])))
        f.write("Definition %s_nhi : nat := %d%%nat.\n" % (L, len(m["his"])))
        f.write("Definition %s_img_lo : Z := IMG_LO.\n" % L)
        f.write("Definition %s_img_top : Z := IMG_TOP.\n" % L)
        f.write("Lemma %s_obj_img : forall i, (i < %s_nobj)%%nat -> %s_img_lo <= %s_obj i /\\ %s_obj i + 8 <= %s_img_top.\n"
                % (L, L, L, L, L, L))
        f.write("Proof.\nintros i Hi. unfold %s_nobj in Hi.\n" % L)
        f.write("do %d (destruct i as [|i]; [vm_compute; split; discriminate|]). lia.\nQed.\n" % (max([len(m["objs"])] + [i + 1 for i, _ in extra])))
        f.write("Lemma %s_sigma_img : forall s, %s_img_lo <= %s_sigma s < %s_img_top.\n" % (L, L, L, L))
        f.write("Proof. destruct s; vm_compute; (split; [discriminate | reflexivity]). Qed.\n")
    print("wrote %sSyms.v (%d names), %sList.v (%d slots, %d functions), %sAddr.v (%d objects, %d auipc values)"
          % (P, len(syms), P, m["nslots"], len(funcs), P, len(m["objs"]), len(m["his"])))


if __name__ == "__main__":
    main()
