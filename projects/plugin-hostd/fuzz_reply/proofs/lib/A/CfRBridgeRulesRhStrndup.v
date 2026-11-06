(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/CfRBridgeRulesFreeRh.v, with its module names changed; 19 of its 67 lines of code are new or changed and 390 lines of the source are left out. *)
(* plugin-hostd/fuzz_reply.asan, image A: top_x's strndup rule at route R, at its room record RP_cf and the KF meter
   (a Theorem Labs lane R, CfRBridgeRules.v Section TOPK at R, the strndup part; new file). Rule 24: proves no function
   (kind: bridge lemma between existing contract forms).
   ASTRNDUP_x_kf_rh is CfRStrndup.v's ASTRNDUP_x_kf (W_journal_x.v astrndup_cf_rule_c_x at top_x's instance and the
   strndup pc of the listing) lifted to R := wle' segs RZ_cf by CfRBridgeRulesRh.astrndup_cf_rule_c_xR_lift_xs over
   YGcallcf's ARxs (strndup crosses no re-hide; top_x's ARX lies in ARxs, CfRBridgeRulesRhTop.ARX_in_xs_rh). At CfF1's A
   rule fit (fu2-mp 9118a6a96818): Section TOPK_rh is CfRBridgeRules.v Section TOPK's header verbatim (top_x's ARX
   with arodata_ok_cf on the memory, MT_ok, HRS, HER), as CfRBridgeRulesRhTop.v's.
   Stated against the names of CfRStrndup.v and CfRBridgeRulesRhTop.v (through it, CfRBridgeRules.v). Numeral 0x427b8
   is CfRStrndup.v's text. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* the strndup pc of the listing (top_x's text `@pa_sigma _ fr_prog_listing PB_fr WS_strndup`) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YGcfRoomPre YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomLive YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x CfParamsReply AD2l ACej CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgePrim CfRBridgeNev CfRBridgeRules CfRStrndup.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeRulesRh CfRBridgeRulesRhTop.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* CfRBridgeRules.v Section TOPK's header verbatim (as CfRBridgeRulesRhTop.v Section TOPK_rh). *)
Section TOPK_rh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
(* FIT CHECK of the relation: the rules' ARX is top_x's relation after W1, whose text is quoted
   here VERBATIM from commit b27e847023f8, lib/A/W_LLVMFuzzerTestOneInput_top_x.v:171-172
   (Definition ARX's body); it closes by reflexivity only if the two are the same term. *)
Goal ARX = (
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem).
Proof. reflexivity. Qed.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
(* MT_sec's defining equations, its literal text (ReplyKfMeter.v at a968c6e24aec: mkAMeter (fun s m => nsec s + m <= KMAX)
   (fun s s' m => nsec s' <= nsec s + m) (fun n => if 64512 <? n then 1 else 0) 0); each holds by reflexivity at
   MT := MT_sec nsec_cf cf_kmax.  mo_ok is not used by these rules' posts. *)
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.
Hypothesis MT_le : forall s s' m, mo_le MT s s' m <-> nsec_cf s' <= nsec_cf s + m.
(* MT_sec's fourth defining equation, its mo_ok (MT_ok, the same text route R's TOPK_rh takes, commit
   07260ccc92a1 lib/A/CfRBridgeRulesRhTop.v:267): at MT := MT_sec YGcfNames.nsec_cf cf_kmax it holds by iff_refl. *)
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
(* The unit's two image rows (Section B's HRS / HER). *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

Theorem ASTRNDUP_x_kf_rh :
  astrndup_realizes_cf segs TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x427b8 ->
  astrndup_cf_rule_c_xR segs TfibB [] ARX MT fr_MMAX RP_cf CTX_strndup (wle' segs RZ_cf)
    (@pa_sigma _ fr_prog_listing PB_fr WS_strndup).
Proof.
intros AS.
apply (astrndup_cf_rule_c_xR_lift_xs segs TfibB [] ARX _ (AR_laws_x_xs segs TfibB L) (ARX_in_xs_rh segs) segs_low
  (wle' segs RZ_cf) (wle_wle' segs RZ_cf) (wle'_trans segs RZ_cf)).
eapply ASTRNDUP_x_kf; first [exact AS | eassumption].
Qed.
End TOPK_rh.
