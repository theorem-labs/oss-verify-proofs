(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/TopX_RT.v at commit f1fb3bc1169 (a Theorem Labs lane's top_x group RT) relocated to
   image B (fuzz_reply.asan-ubsan) by alreloc ced0368250cb6538 (this file holds no image numeral), then cut to the two
   runtime hypotheses of image B's top_x (lib/B/W_LLVMFuzzerTestOneInput_top_x.v at commit e43cf0c7bef), PROVED at
   its instance:
     ALOCK   (top_x.v:304) : alock_realizes_x   (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_lock)
     AUNLOCK (top_x.v:305) : aunlock_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_unlock)
   with ARX := fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
   (top_x.v:154-155; restated here VERBATIM as ARX_rt, so the plug is `exact` up to unfolding ARX).
   Each is the generic runtime twin over any ARx with RTx.rt_laws (lib/B/RT_pthread_mutex_lock_x /
   RT_pthread_mutex_unlock_x, relocated from lib/A the same way; the musl code of both entries is byte-identical in
   the two images, at A 0x9883c / 0x98d28 and B 0x98dbc / 0x992a8) applied at ARX_rt. rt_laws at ARX_rt: frame /
   stack / const / const cells from top_x's own law proof (lib/B/W_journal_x.AR_laws_x_and_hp over
   Reusable/YGcallcf.AR_laws_x_cf (Reusable/YG0lawscf.AR_laws_ok_cf), hl := cf_head, exactly top_x.v:156-160's
   ARX_laws) and layout_ok from ARcf's amc_layout.  No premise is left: every lemma here is closed.
   Cut from the A file: its ASTRLEN_x row (image B's top_x has no such hypothesis) with the imports only that row
   used (RT_kit, RT_strlen_x, W_palib_fr), and CfImgA (no term here names it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x W_contract_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf YGcfPres FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB ReplyRelroGeoB.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pthread_mutex_lock_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pthread_mutex_unlock_x.
Import ListNotations.
Open Scope Z_scope.

Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module LK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pthread_mutex_lock_x.
Module UL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pthread_mutex_unlock_x.

Section topx_rt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:154-155, verbatim *)
Definition ARX_rt : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [].

(* the five runtime laws at ARX_rt: four from top_x's own AR_laws_x proof (top_x.v:156-160), layout from amc_layout *)
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

(* ALOCK (top_x.v:304) *)
Lemma topx_ALOCK : alock_realizes_x TfibB ARX_rt (SIGMA WS_pthread_mutex_lock).
Proof. exact (LK.rt_pthread_mutex_lock_x TfibB ARX_rt rt_laws_ARX). Qed.

(* AUNLOCK (top_x.v:305) *)
Lemma topx_AUNLOCK : aunlock_realizes_x TfibB ARX_rt (SIGMA WS_pthread_mutex_unlock).
Proof. exact (UL.rt_pthread_mutex_unlock_x TfibB ARX_rt rt_laws_ARX). Qed.

(* ---- QMm W1 LIFTS (a Theorem Labs lane, 2026-10-31). top_x's ARX carries arodata_ok_cf as its last conjunct
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v ARX); the runtime contracts above are proved at ARX_rt (its first two
   conjuncts). A contract's post keeps every view off its write set and its stack window; a read-only byte that
   arodata_ok_cf covers is a kept byte (ReplyKeptAroB.aro_kept_B; part 3c: RELRO or cf_ro_reads) and an image byte, so it is in neither when the
   write set holds no kept byte and the stack window lies above the image. aro_keep_view is that step; ARX_rtW is top_x's
   ARX at segs (`exact` against top_x's text: do not re-associate it); aentry_post_x_rtW lifts aentry_post_x, the post
   of the W_sites_x site rules. Each rule's lift: split the W1 pre (ecall_pre_rtW), run the ARX_rt contract, rebuild the
   post (aentry_post_x_rtW / aro_keep_view). The worked rules are topx_ALOCK_W / topx_AUNLOCK_W below. ---- *)
Definition ARX_rtW : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem.
Lemma ecall_pre_rtW : forall ly S Hp W regs mem md, FCiface.ecall_pre_x segs TfibB ARX_rtW ly S Hp W regs mem md ->
  FCiface.ecall_pre_x segs TfibB ARX_rt ly S Hp W regs mem md /\ @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem.
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
  @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem -> @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem'.
Proof.
intros ly S Hp W mem md mem' X Y (HA & _) HX HY HV AR a b E Ha NO.
destruct (YG0dcf.relro_apart_cf segs TfibB ly S Hp W mem md a HA ReplyRelroGeoB.relro_seg_reply_B Ha NO)
  as (RI & _ & _ & _).
destruct (ReplyKeptAroB.aro_kept_B a Ha NO) as (Hb & HK).
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
  ARX_rt ly S Hp W mem md -> @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem ->
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

(* the worked writing rules: ALOCK / AUNLOCK at top_x's W1 ARX. Their write set [A + 4, A + 8) holds no kept byte by
   the rule's own premise (QMm W1 engine edit, B/W_sites_x.v alock_realizes_x / aunlock_realizes_x) *)
Lemma topx_ALOCK_W : alock_realizes_x TfibB ARX_rtW (SIGMA WS_pthread_mutex_lock).
Proof.
intros ly S Hp W regs mem md A tb HPRE H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST HKW.
destruct (ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply SRr_mono; [exact (topx_ALOCK ly S Hp W regs mem md A tb HPRE0 H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST HKW)|].
intros W' c' _ HP.
apply (aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | exact HKW | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
Qed.
Lemma topx_AUNLOCK_W : aunlock_realizes_x TfibB ARX_rtW (SIGMA WS_pthread_mutex_unlock).
Proof.
intros ly S Hp W regs mem md A HPRE H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST HKW.
destruct (ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply SRr_mono; [exact (topx_AUNLOCK ly S Hp W regs mem md A HPRE0 H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST HKW)|].
intros W' c' _ HP.
apply (aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | exact HKW | exact HP].
- destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
- unfold ESTACK. lia.
Qed.

End topx_rt.
