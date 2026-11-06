(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd, U/Img0.rsegs): the per-build part of the kit for the
    satisfiability lemmas of contract families F2, F3 and F4 (the build-independent parts: Prog/SegSatKit.v
    and Prog/SegSatKit234.v; the lemmas: U/Prog/sat/F234Sat*.v). proves no function (kind: statement text;
    closed satisfiability lemmas of contract premises).

    The image ends at 0x55000 (its last segment rw-); the stack-protector GOT cell 0x221b0 holds the guard's address
    0x53820, the guard holds 0; the errno cell tp - 164 = 0x3350c (tp = 0x335b0, U/FrameAPI's ms_tp) lies in .bss.

    The frames on the way from LLVMFuzzerTestOneInput (entry sp S_TOP) to each call site (the contracts' header
    comments; the UBSan binary):
    - main 240 (`addi sp,sp,-0xf0`): label[40] at sp + 0x60, n at sp + 0x5c.
    - m_file 272 (0x110), called from main for each turn.
    - reac_segconf_parse_file 1056 (0x420), called from main (drop-in) and from reac_segconf_parse (32): buf at
      sp + 0x1a8, cur_name at sp + 0x3a8, the saved registers at sp + 0x3b8.
    - reac_segconf_parse 32; cross_check (80) from it.
    - reac_segconf_declared 112: parent[16] at sp + 8, vid at sp + 6; reac_declared_vlan_split 64, name_ok 48,
      reac_declared_vlan_add 112. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec SegSatKit SegSatKit234.
Import ListNotations.
Open Scope Z_scope.

Lemma rsegs_below : segs_below rsegs IMG_END = true.
Proof. vm_compute. reflexivity. Qed.

Definition MAIN_FRAME : Z := 240.
Definition SP_MAIN : Z := S_TOP - MAIN_FRAME.
Definition LABA : Z := SP_MAIN + 0x60.
Definition NCELL : Z := SP_MAIN + 0x5c.
Definition MF_FRAME : Z := 0x110.
Definition SP_MF : Z := SP_MAIN - MF_FRAME.
Definition PF_FRAME : Z := 0x420.
Definition SP_PF1 : Z := SP_MAIN - PF_FRAME.
Definition PARSE_FRAME : Z := 32.
Definition SP_PARSE : Z := SP_MAIN - PARSE_FRAME.
Definition SP_PF2 : Z := SP_PARSE - PF_FRAME.
Definition BUF1 : Z := SP_PF1 + 0x1a8.
Definition NAMEBUF1 : Z := SP_PF1 + 0x3a8.
Definition DECL_FRAME : Z := 112.
Definition SP_DECL : Z := SP_MAIN - DECL_FRAME.
Definition PARENT : Z := SP_DECL + 8.
Definition VIDA : Z := SP_DECL + 6.
Definition SPLIT_FRAME : Z := 64.
Definition SP_SPLIT : Z := SP_DECL - SPLIT_FRAME.
Definition TPV : Z := 0x335b0.
Definition ERRNO : Z := TPV - 164.
Definition STR_SEGMENT : Z := 0x10313.
