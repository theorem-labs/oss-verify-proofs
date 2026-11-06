(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c, Img0.rsegs): the per-build part of the kit for the
    satisfiability lemmas of contract families F2, F3 and F4 (the build-independent parts: Prog/SegSatKit.v
    and Prog/SegSatKit234.v; the lemmas: Prog/sat/F234Sat*.v). proves no function (kind: statement text;
    closed satisfiability lemmas of contract premises).

    The image (read by computation): segments r-- [0x10000, 0x13000),
    r-x [0x13000, 0x20000), rw- [0x20000, 0x22000), rw- [0x22000, 0x54000); the reserved pages are the same four.
    The stack-protector GOT cell 0x21818 holds 0x52e80 and the guard 0x52e80 holds 0 in the image; the errno cell
    tp - 164 = 0x32b6c (tp = 0x32c10, FrameAPI's ms_tp) lies in .bss, in the writable last segment.

    The frames on the way from LLVMFuzzerTestOneInput (entry sp S_TOP) to each call site (the contracts' header
    comments; the plain binary):
    - main 208 (`addi sp,sp,-0xd0`): label[40] at sp + 0x40 (the drop-in's label, snprintf'd there), n (reac_segconf_
      declared's out cell) at sp + 0x3c.
    - m_file 208 (0xd0), called from main at 0x13a04 (drop-in) and 0x13a34 (last file).
    - reac_segconf_parse_file 976 (0x3d0), called from main at 0x13a18 (drop-in) and from reac_segconf_parse (32) at
      0x15710; buf at sp + 0x158, cur_name at sp + 0x358, the saved registers at sp + 0x368.
    - reac_segconf_parse 32, called from main at 0x13ab8; cross_check (64) from it at 0x1571c.
    - reac_segconf_declared 96, called from main at 0x13f1c: parent[16] at sp + 0x10, vid at sp + 0xe;
      reac_declared_vlan_split 64 (from 0x15a20), name_ok 48 (from split at 0x15bac), reac_declared_vlan_add 80
      (from 0x15a3c). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec SegSatKit SegSatKit234.
Import ListNotations.
Open Scope Z_scope.

Lemma rsegs_below : segs_below rsegs IMG_END = true.
Proof. vm_compute. reflexivity. Qed.

Definition MAIN_FRAME : Z := 208.
Definition SP_MAIN : Z := S_TOP - MAIN_FRAME.
(** main's label[40] (the drop-in label of turn 0) and its int n. *)
Definition LABA : Z := SP_MAIN + 0x40.
Definition NCELL : Z := SP_MAIN + 0x3c.
Definition MF_FRAME : Z := 0xd0.
Definition SP_MF : Z := SP_MAIN - MF_FRAME.
Definition PF_FRAME : Z := 0x3d0.
(** reac_segconf_parse_file's sp in turn 0 (called from main) and in turn 1 (called from reac_segconf_parse). *)
Definition SP_PF1 : Z := SP_MAIN - PF_FRAME.
Definition PARSE_FRAME : Z := 32.
Definition SP_PARSE : Z := SP_MAIN - PARSE_FRAME.
Definition SP_PF2 : Z := SP_PARSE - PF_FRAME.
Definition BUF1 : Z := SP_PF1 + 0x158.
Definition NAMEBUF1 : Z := SP_PF1 + 0x358.
Definition DECL_FRAME : Z := 96.
Definition SP_DECL : Z := SP_MAIN - DECL_FRAME.
Definition PARENT : Z := SP_DECL + 0x10.
Definition VIDA : Z := SP_DECL + 0xe.
Definition SPLIT_FRAME : Z := 64.
Definition SP_SPLIT : Z := SP_DECL - SPLIT_FRAME.
(** The thread pointer (FrameAPI.v: ms_tp = 0x32c10) and the errno cell tp - 164. *)
Definition TPV : Z := 0x32c10.
Definition ERRNO : Z := TPV - 164.
(** .rodata literals (the same addresses in both images): "segment" (ieq's word at m_file 0x14400). *)
Definition STR_SEGMENT : Z := 0x10313.
