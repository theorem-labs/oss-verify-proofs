(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   ERRB_SEP_t, the ONE image row that places the error-message-buffer object (YGcfInstBase.errb_cells_cf's 56 bytes
   at cf_errbuf_obj) apart from what the Allocate walks write: the instance object, the out-of-memory byte, errno and
   the two interfaces' depot write zones (AImgS's ims_dzone for the secondary walk, AGImg's ag_dzone for the hit walk).
   Text agreed by CfInstSec and CfInstHit; its first clause is the class-free row YGcfImgRows.ERRB_QAPART (Main), so
   that the drain layer takes that clause without AGImg / AImgS.  [ERRB_SEP_at] gives the five-conjunct form at a B
   with im_syms; [ERRB_SEP_ag] is the hit walk's ag_dzone part.  YGcfInstSec.v and YGcfInstHit.v import this file
   and state no copy; the class-free rows (ERRB_QAPART, EXH_OFF_t) live in YGcfImgRows.v.
   rule 24: no function proved (a statement of a unit image row and its projections). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {IM : AImg} {AG : AGImg} {IMS : AImgS}.

Definition ERRB_SEP_t (B : asyms) : Prop := YGcfImgRows.ERRB_QAPART /\
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a.

(* The five-conjunct form (the text before the split) at a B with im_syms. *)
Lemma ERRB_SEP_at : forall B, im_syms B -> ERRB_SEP_t B -> forall ly a, layout_ok ly -> im_img_cover ly ->
  ly_tsd ly = as_tsd B -> cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof. intros B TS [Q R] ly a LY IMG HT Ha. exact (conj (Q B TS a Ha) (R ly a LY IMG HT Ha)). Qed.

(* The hit walk's part (YGcfInstHit.v's ERRB_AG): ag_dzone misses the buffer object. *)
Lemma ERRB_SEP_ag : forall B, ERRB_SEP_t B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ag_dzone ly a -> ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof. intros B [_ R] ly a LY IMG HT Hd Ha. exact (proj2 (proj2 (proj2 (R ly a LY IMG HT Ha))) Hd). Qed.
End a.
