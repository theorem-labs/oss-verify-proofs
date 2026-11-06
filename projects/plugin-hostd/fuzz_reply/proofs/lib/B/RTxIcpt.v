(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/RTxIcpt.v, with its module paths changed; 14 of its 64 lines of code are new or changed and 1 line of the source is left out. *)
(* The image-B twin of lib/A/RTxIcpt.v (a working branch 6b4f6082575), with B names:
   the one-record bridge between the runtime law record Rt/RTx.v rt_laws (image B's runtime twins RT_<entry>_x.v use
   it) and the interceptor law record YE2y.v icpt_laws_x (image B's interceptor walks YE2* / YE6* / YE7* /
   Rt/Memchr_x / Rt/MemchrChk_x / Rt/Strnlen* / Rt/Bcmp use it).
   - icpt_laws_of_rt: rt_laws plus YCbqG's zero-shadow law give icpt_laws_x.  Field by field: ilx_frame = rtl_frame,
     ilx_stack = rtl_stack, ilx_const = rtl_const_cells, ilx_layout = rtl_layout (the same texts), ilx_zshadow = the
     extra YCbqG.ARx_zshadow_law (rt_laws has no zero-shadow field; RTx.v is not changed).
   - ecall_pre_ix_iff: YE2y.ecall_pre_ix is FCiface.ecall_pre_x at tfibsegs (convertible).
   - *_x_iff: each contract text of B/IcptRealizesX.v is its RTx.v / W_sites_x.v twin at tfibsegs (convertible).
   - the ARcf chain: icpt_laws_x_cf_via_rt proves icpt_laws_x at ARx := ARcf tfibsegs B from AR_laws_cf through
     RTx.rt_laws_cf and alc_zshadow; the _cf corollaries of the interceptor contracts follow: memcmp / bcmp / strnlen
     at ARx := ARcf tfibsegs B, stated with the shared RTx.v / W_sites_x.v texts where those exist.  memchr has no
     row here: image B's generic memchr proof is Rt/Memchr_x.v (memchr_icpt_realizesM_x, M form only, no whole form),
     and its users cite that file directly.
   A's cf_meet is lib/B/RTxIcptMeet.v, not here: it needs B/YD2mcf.v, whose load would give the partial name `YCbqG.`
   to lib/B/YCbqG.v in every importer.
   No interceptor walk Requires this file (YE2y.v's comment: FCiface / YCbqG redefine Zify / lia globally). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require IcptRealizesX YE2z YE2s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require Strnlen Bcmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require FCiface YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_tbl W_place W_kit W_img.
Import ListNotations.
Open Scope Z_scope.
Module IRX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.IcptRealizesX.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- 1. the law records ---- *)
Section l.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Lemma icpt_laws_of_rt : RTx.rt_laws tfibsegs B ARx -> YCbqG.ARx_zshadow_law tfibsegs B ARx -> icpt_laws_x B ARx.
Proof.
intros RL ZS. constructor.
- exact (RTx.rtl_frame _ _ _ RL).
- exact (RTx.rtl_stack _ _ _ RL).
- exact ZS.
- exact (RTx.rtl_const_cells _ _ _ RL).
- exact (RTx.rtl_layout _ _ _ RL).
Qed.
Lemma ecall_pre_ix_iff : forall ly S Hp W regs mem md,
ecall_pre_ix B ARx ly S Hp W regs mem md <-> FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md.
Proof. intros. split; intros H; exact H. Qed.

(* ---- 2. the contract texts ---- *)
Lemma astrnlen_whole_realizes_x_iff : forall pc,
IRX.astrnlen_whole_realizes_x B ARx pc <-> RTx.astrnlen_whole_realizes_x tfibsegs B ARx pc.
Proof. intros. split; intros H; exact H. Qed.
Lemma astrnlen_whole_realizesM_x_iff : forall lo hi pc,
IRX.astrnlen_whole_realizesM_x B ARx lo hi pc <-> RTx.astrnlen_whole_realizesM_x tfibsegs B ARx lo hi pc.
Proof. intros. split; intros H; exact H. Qed.
Lemma abcmp_realizes_x_iff : forall pc,
IRX.abcmp_realizes_x B ARx pc <-> W_sites_x.abcmp_realizes_x tfibsegs B ARx pc.
Proof. intros. split; intros H; exact H. Qed.
End l.

(* ---- 3. the ARcf chain ---- *)
Section c. Context {ci : CfImg} {cp : CfParams}.
Lemma icpt_laws_x_cf_via_rt : forall B, AR_laws_cf tfibsegs B ->
icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md).
Proof. intros B L. exact (icpt_laws_of_rt B _ (RTx.rt_laws_cf tfibsegs B L) (alc_zshadow _ _ L)). Qed.

(* the interceptor contracts at ARcf *)
Corollary memcmp_icpt_contract_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
IRX.amemcmp_realizes_x B (ARcf tfibsegs B) 0x42200.
Proof. intros B L TB. exact (YE2z.memcmp_icpt_contract_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary bcmp_site_realizes_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
W_sites_x.abcmp_realizes_x (@pa_segs _ fr_prog_listing PB_fr) B (ARcf tfibsegs B) (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B L TB. exact (Bcmp.bcmp_site_realizes_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary strnlen_icpt_realizesM_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.astrnlen_whole_realizesM_x tfibsegs B (ARcf tfibsegs B) 0x10350 0x10370 0x421e8.
Proof. intros B L TB. exact (Strnlen.strnlen_icpt_realizesM_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary strnlen_icpt_realizes_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.astrnlen_whole_realizes_x tfibsegs B (ARcf tfibsegs B) 0x421e8.
Proof. intros B L TB. exact (Strnlen.strnlen_icpt_realizes_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
End c.
End a.
