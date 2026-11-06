(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillLoccgif.v (a working branch 30a1993588f, c5 + memnorm; file sha256 c420700196db) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, hand H1 of task MEMNORM; lead a Theorem Labs lane, integrator ReallocPrimary).
   rule 24: no function proved (kind: location facts - the refill and Enqueue write windows are mn_safe at cgif).
   At cgif_file's image: a byte of the stack, the thread object, the primary space / region info / free arrays or the
   high shadow is [MemnormT.mn_safe tfibsegs] (off every read-only segment byte, below TASK_SIZE).  Built on a Theorem Labs lane's
   MemnormHitG.mn_safe_high / mn_safe_owned and MemnormLoc (a working branch fd6ec37fd04); the primary space
   and its region info / free arrays are MemnormLoc.mn_safe_ceil.  Every existing statement is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormHitG MemnormLoc.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill windows' zones.                                                                                       *)

(* the stack [ly_stk_lo, ly_stk_hi): above kHighMemBeg, below kHighMemEnd (YG0f.v:324-326) *)
Lemma mn_safe_stack : forall ly (x : word), layout_ok ly -> ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY Hx. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* the thread object [ly_T, + kThreadObjSize): an owned extent *)
Lemma mn_safe_thread : forall ly (x : word), layout_ok ly -> img_cover ly ->
  ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY IMG Hx.
exact (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG ltac:(unfold owned_extents; right; right; left; reflexivity) Hx).
Qed.

(* the high shadow [kHighShadowBeg, kHighShadowEnd) *)
Lemma mn_safe_hshadow : forall (x : word), kHighShadowBeg <= bv_unsigned x < kHighShadowEnd -> MemnormT.mn_safe tfibsegs x.
Proof. intros x Hx. apply MemnormHitG.mn_safe_high. unfold kHighShadowBeg, kHighShadowEnd, kImgEnd, TASK_SIZE in *. lia. Qed.
End b.
