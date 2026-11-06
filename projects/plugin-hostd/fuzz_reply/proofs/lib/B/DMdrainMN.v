(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainMN.v (commit 68fe993efc49, Quarantine::Drain walk set; file sha256 c85a5d64c290) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainMN.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): memnorm safety (MemnormT.mn_safe) of EVERY word the drain walk
   writes, proved at cgif_file's image - not assumed.  The drain writes only its stack window, the quarantine's
   words outside the batch objects (DMiface.qhdr: the image's mutex word and global header, the thread object's
   cache header) and batch cells in the primary space; each is either in the image's read-write part at or above
   0x9d000 (MemnormSafecgif.mn_safe_rw), in a zone-3 object (MemnormLoc.mn_safe_zone3) or in high memory below
   ASAN_CEIL (MemnormHitG.mn_safe_high).
   This replaces the layer's instance facts MemnormT.mn_owned_low / mn_owned_wr / mn_stack in the drain's files:
   mn_owned_wr is FALSE at cgif_file and at the shared instance (MemnormT.v:28-31: owned statics include bytes of
   the read-only segment [0x10000, 0x30000)), so a theorem that took it was vacuous there.
   rule 24: no function proved (kind: address facts at the image; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0x YFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMiface DMdrainG1 DMdrainG4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormHitG MemnormLoc MemnormSafereply.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the image's mutex word and global header: in the read-write part of the image *)
Lemma mn_safe_quar_img : forall x : word, A_QUAR + 152 <= bv_unsigned x < A_QUAR + 192 -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx. assert (EAQ : A_QUAR = 668336) by reflexivity.
apply MemnormSafereply.mn_safe_rw. rewrite EAQ in Hx. unfold TASK_SIZE. lia.
Qed.

Section l.
Variable ly : alayout.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.

(* the thread object: a zone-3 object below ASAN_CEIL *)
Lemma mn_safe_thr : forall x : word, ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.TOBJ ly LY IMG (DMdrainG4.T_app ly LY) (DMdrainG4.T_img ly LY)) as (_ & TZ & _ & T3 & _).
exact (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x TZ Hx T3).
Qed.

(* the primary space's reservation: high memory below ASAN_CEIL *)
Lemma mn_safe_prim : forall x : word, ly_prim ly <= bv_unsigned x < ly_prim ly + kPrimResvSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.LYB2 ly LY) as (P1 & _ & _ & P4 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kImgEnd, TASK_SIZE, YG0f.ASAN_CEIL in *. lia.
Qed.

(* the stack: high memory below kHighMemEnd *)
Lemma mn_safe_stk : forall x : word, ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* the quarantine's words outside the batch objects, at the instance's quarantine *)
Lemma mn_safe_qhdr : forall inst (x : word), inst + o_quar = A_QUAR -> qhdr inst ly (bv_unsigned x) ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros inst x AQ HQ. unfold qhdr in HQ. rewrite AQ in HQ. destruct HQ as [HQ | [HQ | HQ]].
- apply mn_safe_quar_img. lia.
- apply mn_safe_quar_img. lia.
- apply mn_safe_thr. unfold t_qc, kThreadObjSize in *. lia.
Qed.

(* a batch object placed in the primary space *)
Lemma mn_safe_bobj : forall b (x : word),
  ly_prim ly <= ly_space ly + b_self b -> ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize ->
  bobj ly b (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros b x B1 B2 Hob. pose proof (DMdrainG1.LYB2 ly LY) as (_ & _ & P3 & _).
apply mn_safe_prim. unfold bobj in Hob. unfold kBatchBytes, kSpaceSize in *. lia.
Qed.
End l.
End f.
