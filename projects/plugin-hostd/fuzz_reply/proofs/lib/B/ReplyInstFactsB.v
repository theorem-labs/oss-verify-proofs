(* lib/B/ReplyInstFactsB.v, 2026-10-30: the B twin of lib/A/ReplyInstFacts.v.
   replyb_api_env, the runtime environment fact (Reusable/YCbq.v api_env) at top_x's segs
   (@pa_segs _ fr_prog_listing PB_fr) and B := TfibB, which the B MT_sec allocator plugs (lib/B/CfRBridgeRulesB.v's
   *_kf) pass as errno_low.
   The ameter_triv rule plugs (Section triv) and the generic-MT restatements of the four kf rules with their fit checks
   (Section kf: replyb_AMA_x_kf / replyb_AFREE_x_kf / replyb_AFREE0_x_kf / replyb_ARE_x_kf; Section chk) are removed:
   the triv rules are deleted, the kf restatements quoted top_x's relation before the arodata conjunct
   (lib/B/CfRBridgeRulesB.v's Section TOPK now carries its own fit check of that relation), and nothing used them.
   This mirrors lib/A/ReplyInstFacts.v, which keeps only reply_api_env since commit 454e7065c27.
   proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* CfRBridgeRulesB.v's import block (:52-66), as the file had it before its kf sections were removed *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YP09 YP03 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YGcallcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x YD2l YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfRBridgeAjReallocB CfRBridgeRulesB.
(* top_x's segs / pa_sigma / WS_* (W_kit, W_img, W_syms, W_listing), the laws AR_laws_ok_cf, and its WR_MMAX *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCej W_LLVMFuzzerTestOneInput_write.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.

(* ---- 1. api_env (Reusable/YCbq.v api_env) at top_x's segs and B := TfibB ---- *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Lemma replyb_api_env : api_env segs TfibB.
Proof.
  assert (HE : as_errno TfibB = 0x5d994c) by (vm_compute; reflexivity).
  split; [|split].
  - (* errno's cell (top_x's top_HEV: TFIB_ERRNO_B = 0x5d994c), below kLowMemEnd *)
    rewrite HE. unfold kLowMemEnd. lia.
  - (* errno's 4 bytes lie in one loaded segment, found by computation *)
    intros a Ha. rewrite HE in Ha.
    assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x5d994c) &&
      (0x5d994c + 4 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true) by (vm_compute; reflexivity).
    apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as (H1 & H2).
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
  - (* the two universe memberships (YCeg.v tl_env's last step) *)
    split; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.
End e.

Print Assumptions replyb_api_env.
