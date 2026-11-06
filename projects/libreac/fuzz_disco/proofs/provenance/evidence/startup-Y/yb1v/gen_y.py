#!/usr/bin/env python3
"""gen_y.py -- fuzz_disco asan-ubsan's position-abstract listing layer, in cgif_file_fuzzer's Y layout and names.
Written from scratch on fuzz_disco.asan-ubsan (sha256 cee6f04ad3d4...), so no licence line and no comments.

This version holds only the emitter of lib/Reusable/YB1v.v (the musl and exit-guard decode windows). The full script
also emits YI0w, YI0z, YI12, YCef, YC8i, YCbj and YXcalls from a listing that is not kept; YB1v reads none of it. The
four window values, constants in the full script (read by hand from nm / readelf), are arguments here:

usage: gen_y.py DST MUSL_START MUSL_COUNT GUARD_START GUARD_COUNT
  MUSL_START   sysconf, the first musl function (nm)
  MUSL_COUNT   4-byte slots from MUSL_START to the end of .text (readelf -S: 0x30f24 + 0x6e324 = 0x9f248)
  GUARD_START  oft_exit_guard: auipc a0; lbu a0, (oft_in_callback); bnez a0, 8; ret
  GUARD_COUNT  those 4 instructions
"""
import os
import sys

DST = sys.argv[1]
MUSL_START, MUSL_COUNT, GUARD_START, GUARD_COUNT = (int(x, 0) for x in sys.argv[2:6])
R = "OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable"
IMG = "OssFuzzTheorems.libreac.fuzz_disco.images"


def w(name, text):
    open(os.path.join(DST, name + ".v"), "w").write(text)


def yb1v():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From %s Require Import YP02.\nFrom %s Require Import AsanUbsan.\n"
         "Unset Lia Cache. Unset Nia Cache.\n"
         "Open Scope Z_scope.\nDefinition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.\n"
         "Definition tfibmusl_text_start : Z := 0x%x.\n"
         "Definition tfibmusl_text_count : nat := %d.\n"
         "Definition tfibguard_start : Z := 0x%x.\n"
         "Definition tfibguard_count : nat := %d.\n"
         "Definition tfibmusl_tbl : ctable := Eval vm_compute in\n"
         "(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start "
         "tfibmusl_text_count TEmpty)).\n"
         "Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count "
         "(build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).\n"
         "Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.\n"
         "Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.\n"
         "Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. "
         "discriminate. Qed.\n") % (R, R, IMG, MUSL_START, MUSL_COUNT, GUARD_START, GUARD_COUNT)
    w("YB1v", s)


yb1v()
print("YB1v written: musl window 0x%x + %d slots, guard window 0x%x + %d" % (MUSL_START, MUSL_COUNT, GUARD_START,
                                                                          GUARD_COUNT))
