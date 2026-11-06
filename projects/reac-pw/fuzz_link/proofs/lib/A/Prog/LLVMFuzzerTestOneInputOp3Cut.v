(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 198 of its 257 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputArmR.v; 49 of its 86 lines of code are new or changed and 220 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm (+0x6e8 .. +0x954, +0xfb8 .. +0xfbc; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): the arm's own cuts.
   They are inside the arm's segment, so they are this lane's and not the interface's.

     u_k_inv i     +0x6f0  kernel(&cursor) at 0x82ec0 has returned
     u_l_inv i j   +0x76c  the head of the per-mark loop, mark j (0 <= j < n_mark): s7 = m + MD_MARK + 16 j,
                           s4 = j, s2 = shadow(m + MD_N_MARK); the requests the model owes, walked by link_spec's
                           unmark_walk over the marks left, give unmark's answer
     u_x_inv i     +0x924  the loop is done: the model owes exactly unmark's requests

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
Import ListNotations.
Open Scope Z_scope.

Definition LU_kret : Z := AF_LLVMFuzzerTestOneInput + 0x6f0.   (* 0x82ec4 *)
Definition LU_body : Z := AF_LLVMFuzzerTestOneInput + 0x76c.   (* 0x82f40 *)
Definition LU_exit : Z := AF_LLVMFuzzerTestOneInput + 0x924.   (* 0x830f8 *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variables LF_MO_SET LF_MO_OP : Z.

(* the loop registers of lf_lregs but s7 (op_unmark walks the marks with it) *)
Definition u_regs (cx : lcx) (md fp i : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK) /\
  getr (ms_regs ms3) 22 = w64 md /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* what every cut of the arm carries *)
Definition u_mem (i md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (sh : list Z)
    (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    : Prop :=
  0 <= i <= 47 /\ lf_core cx ms3 /\ u_regs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 sh /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3
    T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i.

(* +0x6f0: kernel has returned *)
Definition u_k_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LU_kret ms3 /\ getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  u_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\ nk_next kbs = 0.

(* +0x76c: the head of the per-mark loop, at mark j *)
Definition u_l_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LU_body ms3 /\
  getr (ms_regs ms3) 23 = w64 (md + MD_MARK + MARK_LEN * j) /\ getr (ms_regs ms3) 20 = w64 j /\
  getr (ms_regs ms3) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  u_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\
  0 <= j < md_n_mark mbs /\ nk_n_sent kbs = 0 /\
  unmark_walk lf_tab (skipn (Z.to_nat j) (mk_names gbs)) (md_reqs mbs) (md_kstate mbs kbs) =
    unmark lf_tab (mk_names gbs) [] (nk_kstate kbs).

(* +0x924: every mark is done *)
Definition u_x_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LU_exit ms3 /\
  getr (ms_regs ms3) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  u_mem i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\
  nk_n_sent kbs = 0 /\ md_reqs mbs = fst (unmark lf_tab (mk_names gbs) [] (nk_kstate kbs)).

End b.
End a.
