(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: top_x group RT (port-reply's TOPX-OWNERS.md, owner g-ph-verbs): three runtime
   hypotheses of A's top_x (W_LLVMFuzzerTestOneInput_top_x.v at integ bb9dae5d905) PROVED at the instance
     ALOCK     (top_x.v:166) : alock_realizes_x   TfibB ARX (SIGMA WS_pthread_mutex_lock)
     AUNLOCK   (top_x.v:167) : aunlock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_unlock)
     ASTRLEN_x (top_x.v:268) : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen)
   with ARX := fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
   (top_x.v:125-126; restated here VERBATIM as ARX_rt, so the plug is `exact` up to unfolding ARX).
   Each is the generic runtime twin over any ARx with RTx.rt_laws (cold/g-ph-verbs-reply-rtwins:
   RT_pthread_mutex_lock_x / _unlock_x / RT_strlen_x) applied at ARX_rt. rt_laws at ARX_rt: frame / stack / const /
   const cells from top_x's own law proof (W_journal_x.AR_laws_x_and_hp over YGcallcf.AR_laws_x_cf
   (YG0lawscf.AR_laws_ok_cf), hl := cf_head, exactly top_x.v:127-131's ARX_laws) and layout_ok from ARcf's amc_layout.
   strlen's two image premises are discharged at TfibB: FrShadowSyms by RT_kit.fr_shadow_of_palib on
   W_palib_fr.palib_tfib TfibB TfibB_syms, TfibSyms by AD2l.TfibB_syms.  No premise is left: every lemma here is
   closed.  The other two rows of the group (ASTRNLEN_x, SNP_x) have no twin yet and are not in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/TopX_RT.v, with its module paths changed; 52 of its 107 lines of code are new or changed and 14 lines of the source are left out. *)
(* top_x group RT (TOPX-OWNERS.md (sha256 bb821fae800d; internal record)): three runtime
   hypotheses of A's top_x (W_LLVMFuzzerTestOneInput_top_x.v at integ bb9dae5d905) PROVED at the instance
     ALOCK     (top_x.v:166) : alock_realizes_x   TfibB ARX (SIGMA WS_pthread_mutex_lock)
     AUNLOCK   (top_x.v:167) : aunlock_realizes_x TfibB ARX (SIGMA WS_pthread_mutex_unlock)
     ASTRLEN_x (top_x.v:268) : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen)
   with ARX := fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
   (top_x.v:125-126; restated here VERBATIM as ARX_rt, so the plug is `exact` up to unfolding ARX).
   Each is the generic runtime twin over any ARx with RTx.rt_laws (a working branch:
   RT_pthread_mutex_lock_x / _unlock_x / RT_strlen_x) applied at ARX_rt. rt_laws at ARX_rt: frame / stack / const /
   const cells from top_x's own law proof (W_journal_x.AR_laws_x_and_hp over YGcallcf.AR_laws_x_cf
   (YG0lawscf.AR_laws_ok_cf), hl := cf_head, exactly top_x.v:127-131's ARX_laws) and layout_ok from ARcf's amc_layout.
   strlen's two image premises are discharged at TfibB: FrShadowSyms by RT_kit.fr_shadow_of_palib on
   W_palib_fr.palib_tfib TfibB TfibB_syms, TfibSyms by AD2l.TfibB_syms.  No premise is left: every lemma here is
   closed.  The other two rows of the group (ASTRNLEN_x, SNP_x) have no twin yet and are not in this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_palib_fr.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pthread_mutex_lock_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pthread_mutex_unlock_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strlen_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf YGcfPres FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKeptAroA ReplyRelroGeoA.
Import ListNotations.
Open Scope Z_scope.

Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Module LK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pthread_mutex_lock_x.
Module UL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pthread_mutex_unlock_x.
Module SL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_strlen_x.

Section topx_rt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:125-126, verbatim *)
Definition ARX_rt : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [].

(* the five runtime laws at ARX_rt: four from top_x's own AR_laws_x proof (top_x.v:127-131), layout from amc_layout *)
Lemma rt_laws_ARX : RTX.rt_laws segs TfibB ARX_rt.
Proof.
  apply (RTX.rt_laws_of_x segs TfibB ARX_rt (@cf_head CfParams_reply)).
  - unfold ARX_rt. apply AR_laws_x_and_hp.
    exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
  - (* ARcf's own frame law (alc_frame), Hp = [] unchanged: rtl_frame's text has no kept-bytes premise (QMm W0') *)
    intros ly S Hp W mem md mem' md' (HAR & Hp0) H1 H2 H3 H4 H5 H6.
    exact (conj (YG0dcf.alc_frame _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md mem' md' HAR H1 H2 H3 H4 H5 H6) Hp0).
  - intros ly S Hp W mem md (HAR & _). exact (amc_layout _ _ _ _ _ (proj1 HAR)).
Qed.

(* ALOCK (top_x.v:166) *)
Lemma topx_ALOCK : alock_realizes_x TfibB ARX_rt (SIGMA WS_pthread_mutex_lock).
Proof. exact (LK.rt_pthread_mutex_lock_x TfibB ARX_rt rt_laws_ARX). Qed.

(* AUNLOCK (top_x.v:167) *)
Lemma topx_AUNLOCK : aunlock_realizes_x TfibB ARX_rt (SIGMA WS_pthread_mutex_unlock).
Proof. exact (UL.rt_pthread_mutex_unlock_x TfibB ARX_rt rt_laws_ARX). Qed.

(* ASTRLEN_x (top_x.v:268) *)
Lemma topx_ASTRLEN_x : astrlen_realizes_x TfibB ARX_rt (SIGMA WS_strlen).
Proof.
  exact (SL.rt_strlen_x TfibB ARX_rt rt_laws_ARX
           (K.fr_shadow_of_palib TfibB (palib_tfib TfibB TfibB_syms)) TfibB_syms).
Qed.

(* ---- QMm W1 LIFTS, image A (a Theorem Labs lane, 2026-10-31; token for token the image-B text of a Theorem Labs lane's
   B/TopX_RT_lock.v at cf82ea55a740, with CfImg_B -> CfImg_A, ReplyKeptAroB.relro_kept_B -> ReplyKeptAroA.relro_kept_A,
   ReplyRelroGeoB.relro_seg_reply_B -> ReplyRelroGeoA.relro_seg_reply_A). top_x's ARX carries arodata_ok_cf as its
   last conjunct (lib/A/W_LLVMFuzzerTestOneInput_top_x.v ARX); the runtime contracts above are proved at ARX_rt (its first
   two conjuncts), which keeps its text and name so that no file citing it changes. A contract's post keeps every view
   off its write set and its stack window; a read-only byte that arodata_ok_cf covers is a kept byte
   (ReplyKeptAroA.relro_kept_A) and an image byte, so it is in neither when the write set holds no kept byte and the
   stack window lies above the image. aro_keep_view is that step; ARX_rtW is top_x's ARX at segs (`exact` against
   top_x's text: do not re-associate it); aentry_post_x_rtW lifts aentry_post_x, the post of the W_sites_x site rules.
   Each rule's lift, ADDED beside the existing lemma as topx_<RULE>_W: split the W1 pre (ecall_pre_rtW), run the
   ARX_rt contract, rebuild the post (aentry_post_x_rtW / aro_keep_view). ---- *)
Definition ARX_rtW : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem.
Lemma ecall_pre_rtW : forall ly S Hp W regs mem md, FCiface.ecall_pre_x segs TfibB ARX_rtW ly S Hp W regs mem md ->
  FCiface.ecall_pre_x segs TfibB ARX_rt ly S Hp W regs mem md /\ @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem.
Proof. intros ly S Hp W regs mem md ((HA & HH & HQ) & R). exact (conj (conj (conj HA HH) R) HQ). Qed.
(* the stack starts above the image: kHighMemBeg <= ly_stk_lo (layout_ok's lo_top), kImgEnd = 0x677000 *)
Lemma stk_above_img : forall ly S Hp W mem md, ARX_rt ly S Hp W mem md -> kImgEnd + 2 ^ 40 <= ly_stk_lo ly.
Proof.
intros ly S Hp W mem md (HA & _).
assert (HK : kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (amc_layout _ _ _ _ _ (proj1 HA))) as T.
  repeat match type of T with _ /\ _ => destruct T as [_ T] end. exact T. }
unfold kHighMemBeg, kImgEnd in *. lia.
Qed.
(* THE STEP: arodata_ok_cf survives a view frame whose first exception set X holds no kept byte and whose second Y lies
   at or above kImgEnd *)
Lemma aro_keep_view : forall ly S Hp (W : world segs) mem md (mem' : word -> option byte) (X Y : Z -> Prop),
  ARX_rt ly S Hp W mem md ->
  (forall a, X a -> ~ kept_x segs TfibB a) -> (forall a, Y a -> kImgEnd <= a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> ~ Y a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem -> @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem'.
Proof.
intros ly S Hp W mem md mem' X Y (HA & _) HX HY HV AR a b E Ha NO.
destruct (YG0dcf.relro_apart_cf segs TfibB ly S Hp W mem md a HA ReplyRelroGeoA.relro_seg_reply_A Ha NO)
  as (RI & _ & _ & _).
destruct (ReplyKeptAroA.aro_kept_A a Ha NO) as (Hb & HK).
assert (Hi : in_img segs a) by exact (proj1 HK).
pose proof (HV a Hb (fun Hx => HX a Hx HK) (fun Hy => ltac:(pose proof (HY a Hy); lia))) as X0.
unfold aview, mbyte, mrestrict in X0.
rewrite (YGcfPres.cfp_img_unhidden segs W a Hb Hi), E in X0. cbn [option_map] in X0.
destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:E0; cbn [option_map] in X0.
- rewrite (AR a b0 E0 Ha NO). injection X0 as X0. f_equal. apply bv_eq. symmetry. exact X0.
- destruct (seg_rom segs (Z_to_bv 64 a)) as [r|] eqn:Er; cbn [option_map] in X0; [|discriminate X0].
  injection X0 as X0. f_equal. apply bv_eq. symmetry. exact X0.
Qed.
(* the site rules' post: from ARX_rt to ARX_rtW, when the write set holds no kept byte and the stack window is at most
   2 ^ 40 bytes *)
Lemma aentry_post_x_rtW : forall stk ly S Hp W regs mem md Wr Pr W' c',
  ARX_rt ly S Hp W mem md -> @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem ->
  ly_stk_lo ly <= spZ regs -> 0 <= stk <= 2 ^ 40 -> (forall a, Wr a -> ~ kept_x segs TfibB a) ->
  aentry_post_x ARX_rt stk ly S Hp W regs mem md Wr Pr W' c' -> aentry_post_x ARX_rtW stk ly S Hp W regs mem md Wr Pr W' c'.
Proof.
intros stk ly S Hp W regs mem md Wr Pr W' c' HA HQ Hsp Hstk HWr (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & HPr & HV & Hpr).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|]. split.
- split; [exact HA'|]. split; [exact HH'|].
  pose proof (stk_above_img _ _ _ _ _ _ HA) as HI.
  apply (aro_keep_view ly S Hp W mem md mem' Wr (fun a => spZ regs - stk <= a < spZ regs) HA HWr); [|exact HV | exact HQ].
  intros a Ha. cbv beta in Ha. lia.
- exact (conj Hrp (conj Hsm (conj HPr (conj HV Hpr)))).
Qed.

End topx_rt.
