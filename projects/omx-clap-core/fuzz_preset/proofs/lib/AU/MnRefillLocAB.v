(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillLoccgif.v (a working branch 29b7505aa27, file sha256 c420700196db) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (0 lines name this file); 0 numerals changed. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, hand H1 of task MEMNORM; lead a Theorem Labs lane, integrator ReallocPrimary).
   rule 24: no function proved (kind: location facts - the refill and Enqueue write windows are mn_safe at cgif).
   At cgif_file's image: a byte of the stack, the thread object, the primary space / region info / free arrays or the
   high shadow is [MemnormT.mn_safe tfibsegs] (off every read-only segment byte, below TASK_SIZE).  Built on
   MemnormHitGB.mn_safe_high / mn_safe_owned and MemnormLoc (cgif/cgif_file_fuzzer lib/MemnormHitG.v (file sha256 ae14e070a8c8; donor not released), cgif/cgif_file_fuzzer lib/MemnormLoc.v (file sha256 3fb4dca88750; donor not released)); the primary space
   and its region info / free arrays are MemnormLocB.mn_safe_ceil.  Every existing statement is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitGB MemnormLocB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill windows' zones.                                                                                       *)

(* the stack [ly_stk_lo, ly_stk_hi): above kHighMemBeg, below kHighMemEnd (YG0f.v:321-323) *)
Lemma mn_safe_stack : forall ly (x : word), layout_ok ly -> ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY Hx. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply MemnormHitGB.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* the thread object [ly_T, + kThreadObjSize): an owned extent *)
Lemma mn_safe_thread : forall ly (x : word), layout_ok ly -> img_cover ly ->
  ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY IMG Hx.
exact (MemnormHitGB.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG ltac:(unfold owned_extents; right; right; left; reflexivity) Hx).
Qed.

(* the high shadow [kHighShadowBeg, kHighShadowEnd) *)
Lemma mn_safe_hshadow : forall (x : word), kHighShadowBeg <= bv_unsigned x < kHighShadowEnd -> MemnormT.mn_safe tfibsegs x.
Proof. intros x Hx. apply MemnormHitGB.mn_safe_high. unfold kHighShadowBeg, kHighShadowEnd, kImgEnd, TASK_SIZE in *. lia. Qed.
End b.
