(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 753 of its 995 lines of code are new or changed and 985 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyATopX.v, with its module names changed; 22 of its 104 lines of code are new or changed and 913 lines of the source are left out. *)
(* lib/A/ReplyInstFacts.v -- a Theorem Labs lane, 2026-10-30, for a Theorem Labs lane's COMPOSE-A (lib/A/ReplyATopX.v).
   reply_api_env, the runtime environment fact (Reusable/YCbq.v:809 api_env) at tfibsegs / TfibB, which ReplyATopX's
   MT_sec allocator plugs (CfRBridgeRules' *_kf, CfRStrndup.ASTRNDUP_x_kf) pass as errno_low.
   The four ameter_triv rule plugs this file held (reply_AMA_x / reply_AFREE_x / reply_AFREE0_x / reply_ARE_x over
   CfRBridgeRules' AMA_x_cf / AFREE_x_cf / AFREEN_x_cf / ARE_x_cf) are removed: ReplyATopX is at MT_sec since
   a Theorem Labs lane's 0d4f5b7d311, and those four rules are deleted (a Theorem Labs lane 2026-10-30 19:50Z).
   Fit check (end of the file): api_env's body quoted from YCbq.v, closed by `exact`.
   The imports, options and sink instance are top_x's own (:43-151, the same order, comments dropped).
   proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_addI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_check_bounded W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_latch_x W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_op_add W_list_push ACk0 W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_event_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_drain_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_exit W_LLVMFuzzerTestOneInput_exit_x YE01_x W_LLVMFuzzerTestOneInput_Gx AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_shadow_pin_x W_rg_place.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone W_LLVMFuzzerTestOneInput_gone_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_relay_add W_relay_event W_relay_finish_h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_check_shape_done W_check_no_loss_read.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
CfRBridgeRules W_ERRL_x TopxEntry TopxImage TopX_RT TopX_RT2 TopX_INTRIN ReplyCnt ReplyLScnt ReplyTrPeakCnl
W_source_reset W_gesture_end W_gestures_end_top AsmTopX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_check_shape_event W_cshe_top W_check_no_loss W_next_line W_list_find W_list_drop W_list_drop_top W_gesture_model_g
W_w1_place W_rom_place_fr W_w3_place_fr TopX_RT3.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance AE2k.tfib_sink_head.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_top_x ACeg ACej.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp YG0dcf YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeAjRealloc.
(* the cf instance's image and parameters, as CfRBridgeRules.v Section TOP declares them (:666-667) *)
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- api_env (Reusable/YCbq.v:809) at segs := tfibsegs, B := TfibB ---- *)
Lemma reply_api_env : api_env tfibsegs TfibB.
Proof.
  split; [|split].
  - (* errno's cell: as_errno TfibB = AF0m.TFIB_ERRNO = 0x5d93cc, below kLowMemEnd *)
    change (as_errno TfibB) with TFIB_ERRNO. unfold TFIB_ERRNO, kLowMemEnd. lia.
  - (* errno's 4 bytes lie in the 4th loaded segment (as AFim.v:531) *)
    intros a Ha. change (as_errno TfibB) with TFIB_ERRNO in Ha. unfold TFIB_ERRNO in Ha.
    eexists. split; [right; right; right; left; reflexivity|].
    match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
      let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
    lia.
  - (* the two universe memberships (ACeg.v:41-42) *)
    split; apply ACej.memZL_In; vm_compute; reflexivity.
Qed.

(* fit check: YCbq.v:810-812, api_env's body at segs := tfibsegs, B := TfibB *)
Goal (0 <= as_errno TfibB /\ as_errno TfibB + 4 <= kLowMemEnd) /\
  (forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> in_img tfibsegs a) /\
  (In [pc_malloc_ra0 (as_code TfibB)] (as_universe TfibB) /\ In [pc_free_ra0 (as_code TfibB)] (as_universe TfibB)).
Proof. exact reply_api_env. Qed.
End s.
