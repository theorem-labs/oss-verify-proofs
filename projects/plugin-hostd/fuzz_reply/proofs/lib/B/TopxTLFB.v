(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/TopxImage.v, with its module paths and module names changed; 7 of its 31 lines of code are new or changed and 152 lines of the source are left out. *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, for a Theorem Labs lane's reply-B top row TLF; a Theorem Labs lane's B W1 round, lead
   a Theorem Labs lane).  rule 24: no function proved (kind: image facts of the instance).
   topx_TLF_B : PALibF TfibB at image B (lib/B/W_frame.v Record PALibF; lib/B/YD2l.v TfibB), ReplyBTop's TLF row
   `forall rc fx, @W_frame.PALibF rc fr_prog_listing (@PB_fr rc) TfibB`.  The image-B twin of a Theorem Labs lane's
   lib/A/TopxImage.v topx_TLF, the same script: the stack-use-after-return GOT slot (as_got_uar TfibB = A_OBJ 6), the
   word's cell in the image and 4-aligned, __asan_stack_malloc_0 / _1's listing entries equal the code's, and the four
   cells (A_OBJ 0, A_OBJ 6, A_OBJ 30, the uar cell) pairwise apart, each decided over TfibB by vm_compute.  TLF has no
   premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v YI04 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame.
Import ListNotations.
Local Open Scope Z_scope.

Section topx_tlf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma topx_TLF_B : PALibF TfibB.
Proof.
  constructor.
  - vm_compute. reflexivity.
  - cbn [as_uar_cell TfibB]. lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - cbn [zseps zseps_from fst snd].
    repeat split; first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.
End topx_tlf.

(* ReplyBTop's TLF row, at every RunCeil and FPState *)
Theorem topx_TLF_B_all : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @PALibF rc fr_prog_listing (@PB_fr rc) TfibB.
Proof. intros rc fx. exact (@topx_TLF_B rc). Qed.
