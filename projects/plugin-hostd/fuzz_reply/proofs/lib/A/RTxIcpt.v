(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RTxIcpt.v, with its module paths changed. *)
(* The one-record bridge between a Theorem Labs lane's runtime law record Rt/RTx.v rt_laws (the image-A
   runtime twins RT_<entry>_x.v use it) and SitesCf's interceptor law record AE2y.v icpt_laws_x (the interceptor
   walks AE2* / AE3* / AE6* / AE7* / Rt/Memchr* / Rt/Strnlen* / Rt/Bcmp use it).
   - icpt_laws_of_rt: rt_laws plus YCbqG's zero-shadow law give icpt_laws_x.  Field by field: ilx_frame = rtl_frame,
     ilx_stack = rtl_stack, ilx_const = rtl_const_cells, ilx_layout = rtl_layout (the same texts), ilx_zshadow = the
     extra YCbqG.ARx_zshadow_law (rt_laws has no zero-shadow field; RTx.v is not changed).
   - ecall_pre_ix_iff: AE2y.ecall_pre_ix is FCiface.ecall_pre_x at tfibsegs (convertible).
   - *_x_iff: each contract text of IcptRealizesX.v is its RTx.v / W_sites_x.v twin at tfibsegs (convertible).
   - the ARcf chain: icpt_laws_x_cf_via_rt proves, from AR_laws_cf through RTx.rt_laws_cf and alc_zshadow, the
     statement of SitesCf's AD2mcf.icpt_laws_x_cf (which cites the same AR_laws_cf / ARmcf fields directly);
     cf_meet checks that the two inhabit one type.  The _cf corollaries of the interceptor contracts follow:
     memcmp / bcmp / memchr / strnlen at ARx := ARcf tfibsegs B, stated with the shared RTx.v / W_sites_x.v texts
     where those exist.
   No interceptor walk Requires this file (AE2y.v:81-88: FCiface / YCbqG redefine Zify / lia globally).
   Scope (a Theorem Labs lane, 2026-10-29): these twins and this bridge close none of ReplyATop's 27 Section Variables today
   (the runtime contracts there are closed by atop_LAWS at cgif's AR); their use is the cf top A/ReplyTFIBcf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require IcptRealizesX AE2z AE2s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt Require Memchr Strnlen Bcmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require FCiface YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_sites_x AD2mcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_tbl W_place W_kit W_img.
Import ListNotations.
Open Scope Z_scope.
Module IRX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.IcptRealizesX.
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
Lemma amemchr_realizes_x_iff : forall pc,
IRX.amemchr_realizes_x B ARx pc <-> RTx.amemchr_realizes_x tfibsegs B ARx pc.
Proof. intros. split; intros H; exact H. Qed.
Lemma amemchr_realizesM_x_iff : forall lo hi pc,
IRX.amemchr_realizesM_x B ARx lo hi pc <-> RTx.amemchr_realizesM_x tfibsegs B ARx lo hi pc.
Proof. intros. split; intros H; exact H. Qed.
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
Definition cf_meet :=
(icpt_laws_x_cf_via_rt, fun B L => AD2mcf.icpt_laws_x_cf B L) :
(forall B, AR_laws_cf tfibsegs B -> icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)) *
(forall B, AR_laws_cf tfibsegs B -> icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)).

(* the interceptor contracts at ARcf *)
Corollary memcmp_icpt_contract_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
IRX.amemcmp_realizes_x B (ARcf tfibsegs B) 0x421a8.
Proof. intros B L TB. exact (AE2z.memcmp_icpt_contract_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary bcmp_site_realizes_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
W_sites_x.abcmp_realizes_x (@pa_segs _ fr_prog_listing PB_fr) B (ARcf tfibsegs B) (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B L TB. exact (Bcmp.bcmp_site_realizes_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary memchr_icpt_realizesM_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.amemchr_realizesM_x tfibsegs B (ARcf tfibsegs B) 0x10350 0x10370 0x421b0.
Proof. intros B L TB. exact (Memchr.memchr_icpt_realizesM_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary memchr_icpt_realizes_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.amemchr_realizes_x tfibsegs B (ARcf tfibsegs B) 0x421b0.
Proof. intros B L TB. exact (Memchr.memchr_icpt_realizes_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary strnlen_icpt_realizesM_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.astrnlen_whole_realizesM_x tfibsegs B (ARcf tfibsegs B) 0x10350 0x10370 0x42190.
Proof. intros B L TB. exact (Strnlen.strnlen_icpt_realizesM_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
Corollary strnlen_icpt_realizes_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
RTx.astrnlen_whole_realizes_x tfibsegs B (ARcf tfibsegs B) 0x42190.
Proof. intros B L TB. exact (Strnlen.strnlen_icpt_realizes_x B _ (icpt_laws_x_cf_via_rt B L) TB). Qed.
End c.
End a.
