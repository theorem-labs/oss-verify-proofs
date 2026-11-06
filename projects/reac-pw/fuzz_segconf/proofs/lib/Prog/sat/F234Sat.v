(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c): satisfiability of the premises of contract families F2,
    F3 and F4 (lib/Prog/*_c.v of commit aca5136e2baf):
    for each named premise one closed lemma [<premise>_sat] that it holds at a real call site with real values;
    [_dropin] lemmas add the other call site the contract's header names. The cut predicates of Prog/seg_cuts.v and
    the HEAD cuts' entry facts are in F234SatCuts.v.

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    The real values (Prog/SegSatKit234.v section 2): the input INP2 (cap 4, flags 1, two files: T1 under label byte
    3, T2 the hand-written file), the states between the turns from seg_spec.seg_run / seg_after (RC1, MC1 after the
    drop-in, RC2, MC2 after the run: two segments eth0.5 and eth1.7, three refusals kept), and the states inside each
    function at its call site by SegModel's own functions (pf_spine for reac_segconf_parse_file, m_lines for m_file,
    r_parse_file for cross_check, r_decl_go for the VLAN walk). The blocks c, m, tab and the text blocks sit at
    SegSatKit's C0, M0, TAB0 and SegSatKit234's TX1A, TX2A, holding the canonical images of those states; the stack
    region is [LO, S_TOP); sp at each site is S_TOP minus the frames of its callers (Prog/SegSat234.v). Bytes no
    premise fixes (stack bytes outside the named buffers, buf's bytes past the strings) are 0. The stack-protector
    cells and the .rodata literals are read from the image. fcsr is 0. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SegSatKit SegSatKit234 SegSat234.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import
  trim_c refuse_c cross_check_c reac_segconf_parse_file_c reac_segconf_parse_c m_find_c m_refuse_c ieq_c
  name_ok_c reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c m_file_c.
Import ListNotations.
Open Scope Z_scope.

Ltac sat := sat2 rsegs_below.

(** ** Family F2: the reader's helpers *)

(** trim, reac_segconf_parse_file 0x14efc in turn 0 (the drop-in, parse_file called from main: sp = SP_PF1), line 2
    "role = box": after `*eq = 0` buf holds "role \0 box\0"; trim(line) gets buf, the C string "role " (a trailing
    blank to trim). *)
Definition ROLE_BUF : list Z := sb "role " ++ [0] ++ sb " box" ++ [0].
Definition RS_TRIM : list region := [(BUF1, padz ROLE_BUF 512); R_STACK].
Lemma trim_pre_sat : trim_pre (RMEM RS_TRIM) SP_PF1 LO BUF1 (sb "role ").
Proof. unfold trim_pre. sat. Qed.

(** refuse, reac_segconf_parse_file 0x152b0 (the KNOCK site) in turn 0, line 5 "knock = 1": refuse(c, 5, F_knock
    (0x10762), cur_name, val) with c holding the state after lines 1-4 (PF1 4), cur_name = "eth0.5" at sp + 0x358,
    val = "1" at buf + 8 (buf: "knock\0\0 1\0" after the two trims). *)
Definition RCK : rconf := fst (fst (PF1 4)).
Definition NM05 : list Z := sb "eth0.5".
Definition KNOCK_BUF : list Z := sb "knock" ++ [0; 0] ++ sb " 1" ++ [0].
Definition RS_REFUSE : list region :=
  [(NAMEBUF1, padz NM05 16); (BUF1, padz KNOCK_BUF 512); (C0, rconf_img RCK); R_STACK].
Lemma refuse_pre_sat :
  refuse_pre (RMEM RS_REFUSE) (Z_to_bv 32 0) SP_PF1 LO C0 5 PF_STR_KNOCK
    [Z_to_bv 64 NAMEBUF1; Z_to_bv 64 (BUF1 + 8); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
    RCK 5 F_knock [AS NM05; AS (sb "1")].
Proof. unfold refuse_pre, printf_env, ssp_ok. sat. Qed.

(** cross_check, reac_segconf_parse 0x1571c in turn 1: c holds the state after the last file's parse_file (RCX:
    eth1.7 has model s0808 under role master, so cross_check refuses F_xmodel). *)
Definition RS_CROSS : list region := [(C0, rconf_img RCX); R_STACK].
Lemma cross_check_pre_sat : cross_check_pre (RMEM RS_CROSS) (Z_to_bv 32 0) SP_PARSE LO C0 RCX.
Proof. unfold cross_check_pre, printf_env, ssp_ok. sat. Qed.

(** ** Family F3: the reader's parse *)

(** reac_segconf_parse_file, reac_segconf_parse 0x15710 in turn 1: c holds RC1 (after the drop-in), the text T2 in
    its block, the label "reac-pw.conf" in .rodata (seg_spec.STR_BASE). *)
Definition RS_PF2 : list region := [(C0, rconf_img RC1); (TX2A, txt_img T2); R_STACK].
Lemma reac_segconf_parse_file_pre_sat :
  reac_segconf_parse_file_pre (RMEM RS_PF2) (Z_to_bv 32 0) SP_PARSE LO C0 TX2A STR_BASE RC1 T2 (Some S_base).
Proof. unfold reac_segconf_parse_file_pre, reader_pre, printf_env, ssp_ok. cbv beta iota. sat. Qed.

(** reac_segconf_parse_file, LLVMFuzzerTestOneInput 0x13a18 in turn 0: c holds rconf0 (reac_segconf_init's zeros),
    the text T1, the label LAB1 = "reac-pw.conf.d/3-x.conf" in main's label[40]. *)
Definition RS_PF1 : list region := [(LABA, padz LAB1 40); (C0, rconf_img rconf0); (TX1A, txt_img T1); R_STACK].
Lemma reac_segconf_parse_file_pre_sat_dropin :
  reac_segconf_parse_file_pre (RMEM RS_PF1) (Z_to_bv 32 0) SP_MAIN LO C0 TX1A LABA rconf0 T1 (Some LAB1).
Proof. unfold reac_segconf_parse_file_pre, reader_pre, printf_env, ssp_ok. cbv beta iota. sat. Qed.

(** reac_segconf_parse (reader_pre PARSE_STACK), LLVMFuzzerTestOneInput 0x13ab8 in turn 1. *)
Lemma reac_segconf_parse_pre_sat : reader_pre PARSE_STACK (RMEM RS_PF2) (Z_to_bv 32 0) SP_MAIN LO C0 TX2A RC1 T2.
Proof. unfold reader_pre, printf_env, ssp_ok. sat. Qed.

(** ** Family F3: the harness's model *)

(** m_find, m_file 0x14494 (m_header) in turn 1, line 1 "[segment eth1.7]": c holds m_file's state before the line
    (MC1 with gen + 1 and reading "reac-pw.conf"), name = the 6 bytes "eth1.7" in the text block. *)
Definition MCH : mconf := fst (MF2 0).
Definition RS_MFIND : list region := [(M0, mblk_img false MCH); (TX2A, txt_img T2); R_STACK].
Lemma m_find_pre_sat : m_find_pre (RMEM RS_MFIND) SP_MF LO M0 (TX2A + 9) 6 MCH (zb (sb "eth1.7")).
Proof. unfold m_find_pre. sat. Qed.

(** m_refuse, m_file 0x143d0 from the knock branch in turn 0, line 5: c holds the state after lines 1-4 with
    kept_knock[0] = 1 stored (mconf_atp true), knock = true. *)
Definition MCK : mconf := fst (MF1 4).
Definition RS_MREF : list region := [(M0, mblk_img true MCK); R_STACK].
Lemma m_refuse_pre_sat : m_refuse_pre (RMEM RS_MREF) (Z_to_bv 32 0) SP_MF LO M0 5 MCK true.
Proof. unfold m_refuse_pre, printf_env, ssp_ok. sat. Qed.

(** ieq, m_file 0x14400 (m_header) in turn 0, line 1: ieq(b, 7, "segment"), b = the text after '['. *)
Definition RS_IEQ : list region := [(TX1A, txt_img T1); R_STACK].
Lemma ieq_pre_sat : ieq_pre (RMEM RS_IEQ) SP_MF LO (TX1A + 1) 7 STR_SEGMENT (zb S_segment) S_segment.
Proof. unfold ieq_pre. sat. Qed.

(** m_file, LLVMFuzzerTestOneInput 0x13a34 (the last turn): m holds MC1, the text T2, label NULL. *)
Definition RS_MF2 : list region := [(M0, mblk_img false MC1); (TX2A, txt_img T2); R_STACK].
Lemma m_file_pre_sat : m_file_pre (RMEM RS_MF2) (Z_to_bv 32 0) SP_MAIN LO M0 TX2A 0 MC1 T2 None.
Proof. unfold m_file_pre, printf_env, ssp_ok, words_img. cbv beta iota. sat. Qed.

(** m_file, LLVMFuzzerTestOneInput 0x13a04 (the drop-in turn 0): m holds calloc's zeros (mconf0), the text T1, the
    label LAB1 in main's label[40]. *)
Definition RS_MF1 : list region := [(LABA, padz LAB1 40); (M0, mblk_img false mconf0); (TX1A, txt_img T1); R_STACK].
Lemma m_file_pre_sat_dropin : m_file_pre (RMEM RS_MF1) (Z_to_bv 32 0) SP_MAIN LO M0 TX1A LABA mconf0 T1 (Some LAB1).
Proof. unfold m_file_pre, printf_env, ssp_ok, words_img. cbv beta iota. sat. Qed.

(** ** Family F4: the declared VLANs *)

(** name_ok, reac_declared_vlan_split 0x15bac on seg[0] = eth0.5: parent = "eth0" (memcpy + NUL) in declared's
    parent[16]. *)
Definition RS_NOK : list region := [(PARENT, padz (sb "eth0") 16); R_STACK].
Lemma name_ok_pre_sat : name_ok_pre (RMEM RS_NOK) SP_SPLIT LO PARENT (sb "eth0").
Proof. unfold name_ok_pre. sat. Qed.

(** reac_declared_vlan_split, reac_segconf_declared 0x15a20 on seg[0]: segment = c->seg[0].name = "eth0.5" (c holds
    RC2), parent = declared's sp + 0x10, cap 16, vid = declared's sp + 0xe, the errno cell tp - 164 holding 0. *)
Definition RS_SPLIT : list region := [(C0, rconf_img RC2); (ERRNO, zrep 4); R_STACK].
Lemma split_pre_sat :
  split_pre (RMEM RS_SPLIT) SP_DECL LO TPV (rseg_addr C0 0) PARENT 16 VIDA NM05 (Z_to_bv 64 0).
Proof. unfold split_pre, errno_ok, ssp_ok. sat. Qed.

(** reac_declared_vlan_add, reac_segconf_declared 0x15a3c on seg[1] = eth1.7 (the second add): the table holds TB1 =
    [(enp1s0, 33); (eth0, 5)] in calloc(cap + 1, 18) with the guard entry, *n = 2 in main's n, parent = "eth1",
    vid = 7. *)
Definition RS_ADD : list region :=
  [(PARENT, padz (sb "eth1") 16); (NCELL, le4z 2); (TAB0, tab_img TB1 CAP2); R_STACK].
Lemma vtab_pre_sat : vtab_pre (RMEM RS_ADD) SP_DECL LO TAB0 CAP2 NCELL TB1.
Proof. unfold vtab_pre. sat. Qed.
Lemma add_pre_sat : add_pre (RMEM RS_ADD) SP_DECL LO TAB0 CAP2 NCELL PARENT 7 TB1 (sb "eth1").
Proof. unfold add_pre, vtab_pre. sat. Qed.

(** reac_segconf_declared, LLVMFuzzerTestOneInput 0x13f1c: c holds RC2, tab = calloc(cap + 1, 18) holding
    vlan_init's (enp1s0, 33), zeros, the 0x5a guard entry; n = 1 in main's n; the errno cell holding 0. *)
Definition RS_DECL : list region :=
  [(NCELL, le4z 1); (C0, rconf_img RC2); (TAB0, tab_img TB0 CAP2); (ERRNO, zrep 4); R_STACK].
Lemma reac_segconf_declared_pre_sat :
  declared_pre (RMEM RS_DECL) SP_MAIN LO TPV C0 TAB0 CAP2 NCELL RC2 TB0 (Z_to_bv 64 0).
Proof. unfold declared_pre, vtab_pre, errno_ok, ssp_ok. sat. Qed.
