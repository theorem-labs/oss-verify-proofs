(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 81 of its 124 lines of code are new or changed and 895 lines of the source are left out. *)
(* Image B (plugin-hostd fuzz_reply, ASan-UBSan): the row SR_R of ReplyBTop's Section btop, source_reset at route R,
   at ReplyBTop's instance (MT := ReplyKfMeterB.MT_sec nsec_cf cf_kmax, ARx := top_x's ARX, R := wle' tfibsegs RZ_cf).
   btr_SR_R is W_source_reset.pb_source_reset_gc_lf_xR (source_reset's R walk with list_free's R walk
   W_list_free.pb_list_free_g_xR inside) at that instance, with RO := arodata_ok_cf (top_x's ARX carries it) and
   CTX := YCk0.CTX_AFREE.  Its premises are closed by:
   - R_refl / R_trans / WLE_R: YA0nH's wle'_refl / wle'_trans / wle_wle' at tfibsegs, RZ_cf;
   - LAWS: top_x's ARX_laws; BLKN: the cf block law (YG0dcf.alc_blocks, as top_x's proof derives it); HPST at PST = [];
     TL: W_palib.pb_palib_tfib; MLAW: ReplyKfMeterB.MT_sec_laws; RO_ARx: ARX's last conjunct;
   - AFREE_R / AFREEN_R: CfRBridgeRulesFreeRhB.AFREE_x_kf_rh / AFREEN_x_kf_rh, their free target the closed primed
     realizer ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all, their meter rows MT_sec's by reflexivity, their image
     rows ReplyRelroGeoB's;
   - AMEMSET_R: W_sites_x.aintrin_realizes_xR_of_x of btr_AMEMSET_W, __asan_memset's strict rule at top_x's ARX: the
     proved rule TopX_INTRIN_memset.topx_AMEMSET_x at TopX_RT_lock.ARX_rt, the arodata fact carried to the post's memory
     by TopX_RT_lock.aro_keep_view (the steps of TopX_INTRIN_memcpy.topx_AMEMCPY_W, for memset);
   - HCTX_sr_free / HCTX_lf_exit: the return addresses source_reset + 0x60 and list_free + 0xa0 are rows of CTX_AFREE.
   The premise left is LD_R, list_drop at R at every G' with gx_ok / gx_rt / rom_out (the closer's own hypothesis
   LD_R, at the instance): image B has no route-R list_drop walk, and the strict walk W_list_drop.pb_list_drop_ro_x
   (lifted by W_contract_xR_g3.ldrop_spec_xR_of_x) takes the strict free rule afree_cf_rule_c_x at ARX, whose unprimed
   free realizer image B does not prove (ReplyDeallocInstB proves only the primed one).
   rule 24: no function proved (instantiation of proved walks)
   proves no function (kind: segment lemma) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp YM05 YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSBo ReplyLS3B_inst ReplyB3LScap W_palib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CfRBridgeRulesB CfRBridgeRulesFreeRhB ReplyInstFactsB
  ReplyRelroGeoB YD25cf ReplyDeallocInstB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0 W_sites_x TopX_RT_lock TopX_INTRIN_memset.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_srlf_xR W_contract_xR_g3 W_list_drop
  W_source_reset.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive YGcfNames YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).

Section btr_memset.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* __asan_memset's strict rule at top_x's ARX: TopX_INTRIN_memset.topx_AMEMSET_x at ARX_rt, its post's memory keeping
   arodata_ok_cf by TopX_RT_lock.aro_keep_view (X := the destination, no kept byte by the rule's own premise; Y := the
   ESTACK window below sp, above the image by TopX_RT_lock.stk_above_img) *)
Lemma btr_AMEMSET_W : W_sites_x.aintrin_realizes_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB
  (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) OSet (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_asan_memset).
Proof.
  intros ly S Hp W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HDEST HAMR HNK HRA HSH HOP.
  destruct (TopX_RT_lock.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (TopX_INTRIN_memset.topx_AMEMSET_x ly S Hp W regs mem md d x n HPRE0 H10 H11 H12 Hn Hd Hdn HDEST HAMR HNK
      HRA HSH HOP)|].
  intros W' c' _ (-> & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & H10' & Hst & Hfr & Hpr).
  split; [reflexivity|]. exists regs', mem', md'.
  split; [exact Hc|]. split; [|exact (conj Hrp (conj Hsm (conj H10' (conj Hst (conj Hfr Hpr)))))].
  refine (conj HA' (conj HH' _)).
  apply (TopX_RT_lock.aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n)
    (fun a => spZ regs - ESTACK <= a < spZ regs) (proj1 HPRE0) HNK); [| exact Hfr | exact HQ].
  intros a Ha. pose proof (TopX_RT_lock.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HS.
  destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in *. lia.
Qed.
End btr_memset.

(* SR_R: W_source_reset.pb_source_reset_gc_lf_xR at ReplyBTop's instance; LD_R (list_drop at R) is its premise *)
Lemma btr_SR_R
  (LD_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (G' : list (Z * Z)),
    gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @gx_rt rc (@PB_fr rc) TfibB G' ->
    @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' ->
    @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
      (RR rc) MT CfRBridgeRulesB.RP_cf G' (@W_list_drop.A_list_dropP rc (@PB_fr rc))) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_srlf_xR.sr_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_source_reset).
Proof.
  intros rc fx.
  Set Generate Goal Names.
  eapply W_source_reset.pb_source_reset_gc_lf_xR
    with (RO := @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB)
         (CTX := YCk0.CTX_AFREE).
  try (only [R_refl]: solve [exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [R_trans]: solve [exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [WLE_R]: solve [exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [LAWS]: solve [exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws]).
  try (only [BLKN]: solve [
    intros ly S Hp W mem md p n H Hin;
    destruct (YG0dcf.alc_blocks _ _ (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply)
      (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn);
    pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb; lia]).
  try (only [HPST]: solve [intros a _ H; inversion H]).
  try (only [TL]: solve [exact W_palib.pb_palib_tfib]).
  try (only [MLAW]: solve [exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX)]).
  try (only [RO_ARx]: solve [intros ly S Hp W mem md H; exact (proj2 (proj2 H))]).
  try (only [AFREE_R]: solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh;
    first [ exact (ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all fx rc)
          | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
          | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env
          | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
          | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
          | (intros; reflexivity) | (intros; apply iff_refl) ]]).
  try (only [AFREEN_R]: solve [eapply CfRBridgeRulesFreeRhB.AFREEN_x_kf_rh;
    first [ exact (ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all fx rc)
          | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
          | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env
          | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
          | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
          | (intros; reflexivity) | (intros; apply iff_refl) ]]).
  try (only [AMEMSET_R]: solve [eapply W_sites_x.aintrin_realizes_xR_of_x;
    first [ exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact (@btr_AMEMSET_W fx rc) ]]).
  try (only [HCTX_sr_free]: solve [unfold YCk0.CTX_AFREE; cbn [In]; repeat (first [left; reflexivity | right])]).
  try (only [HCTX_lf_exit]: solve [unfold YCk0.CTX_AFREE; cbn [In]; repeat (first [left; reflexivity | right])]).
  try (only [LD_R]: solve [exact (LD_R rc fx)]).
Qed.
