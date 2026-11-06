(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 1190 of its 1221 lines of code are new or changed and 321 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/nl_talk_exit.v, with its module names changed; 20 of its 51 lines of code are new or changed and 1190 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4) on image A: the cut between the two entry pieces of its walk.
   The entry is walked in two files:
     reac_served_unmark_allEntryA.v : um_br_obl -> (the entry run reaches um_post)   (+0x00 .. +0x188: the prologue,
                                      frame_alloc_3, the frame's header and its 44 shadow bytes)
     reac_served_unmark_allEntryB.v : um_rel_obl -> um_tail_obl -> um_head_obl 0 -> um_br_obl
                                      (+0x18c `beqz s4` -> REL; the check of m->n, `blez` -> TAIL; the loop set-up
                                      -> HEAD 0)
   The BRANCH cut is +0x18c (`beqz s4`, 0x8a060): the frame is taken and set up, s10 still holds the shadow base,
   and g_nl and the marks block are as at the call (the entry writes only its stack window, the frame, its
   shadow and its flag byte).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide reac_served_unmark_allDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition UM_CUT_BR : Z := AF_reac_served_unmark_all + 0x18c.   (* `beqz s4` *)
Lemma UM_CUT_BR_pin : 0x821cc + UM_CUT_BR = 0x8a060. Proof. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
Variable B : asyms.

(* the bytes of the fake kernel are still the caller's *)
Definition um_gnl_kept (cx : umcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
    aview SEGS (w_H W3) m3 a = aview SEGS (w_H (um_W cx)) (um_memc cx) a.

(* +0x18c `beqz s4`: s4 = m (um_base), s10 = the shadow base, g_nl and the marks block untouched. *)
Definition um_gi_br (cx : umcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_BR) /\
  getr (ms_regs ms3) 26 = w64 SHADOW_OFF /\
  um_gnl_kept cx W3 (ms_mem ms3) /\
  (um_mk cx <> 0 -> um_marks_kept cx W3 (ms_mem ms3)) /\
  um_base SK B cx fpos ly3 S3 W3 ms3 md3.

Definition um_br_obl : Prop := um_from SK B um_gi_br.

End b.
End a.

(* No global sink_head instance is in scope here. *)
Fail Definition sink_head_probe_um_edefs : YI16.sink_head := _.
