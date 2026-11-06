(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 106 of its 155 lines of code are new or changed and 889 lines of the source are left out. *)
(* The image-B composition ReplyBTop at route R: its Section hypothesis RE_R (relay_event's contract at R), closed.
   btr_RE_R's statement is RE_R's Context type, word for word, under ReplyBTop's notations (copied below).
   The closer is W_relay_event_x.pb_relay_event_xR at the top's instance (PB_fr, TfibB, PST = [], top_x's ARX,
   R := wle' tfibsegs RZ_cf, MT := MT_sec nsec_cf cf_kmax, RP := RP_cf, MMAX := fr_MMAX, G := et_GRE, RG := fr_RG).
   Its premises:
   - the instance (LAWS, HP0, BLKM, HG) and the placements (HV3 .. HLPST): top_x's ARX_laws / ARX_hp0 / GX_ok,
     W_bx_inst_x's block bound at ARX's first two conjuncts, _G's G_fr_c facts, and computation, as
     W_relay_event_x_top discharges the strict walk's;
   - the mutex and strlen entries: the W1 lifts TopX_RT_lock.topx_ALOCK_W / topx_AUNLOCK_W, TopX_RT_B2.topx_ASTRLEN_B_W;
   - R's laws: YA0nH.wle'_refl / wle'_trans / wle_wle';
   - SL_R, send_line at R: btr_SL_R below, W_send_line_x.pb_send_line_xR at the same instance, its static and
     placement premises as top_x's strict SL_x block discharges them, its realloc rule at R
     CfRBridgeRulesRhTopB.ARE_x_kf_rh (RO := arodata_ok_cf, HA := cf_hull_adm, over ReplyAreallocTargetB's two
     realloc realizations), RO_ARx by ARX's third conjunct, and HA_call (btr_hull_adm_of_mo) from MT_sec's
     equations and ReplyKfMeterB.sec_lit.
   proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1w_cf YD1w_cf_fp YD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1mcf YD1pcf ReplyTFIBBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x ReplyLSB ReplyRINVB.
(* the zify flag as ReplyBTop's proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyDriverCfB ReplyRINVB ReplyLSBo ReplyLSBDrainPre.
Import ReplyDriverCfB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLS3B_inst ReplyB3LScap ReplyB3LScnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB
  TopX_INTRIN_memcpy TopX_RT_B2 TopX_RT_lock TopX_RT4 CfRBridgeRulesB CfRBridgeRulesRhTopB ReplyInstFactsB YD1vcf YD25cf
  ReplyRelroGeoB ReplyAreallocTargetB W_palib W_errno_azs W_bx_inst_x YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_contract_xR W_send_line_xR W_send_line_x W_relay_event_x W_LLVMFuzzerTestOneInput_arm_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
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

(* each walk's premises are closed by the goal names eapply gives them (its Section hypotheses' names) *)
Local Set Generate Goal Names.

(* the realloc rule's hull admission from the meter: MT_sec's budget at the call is nsec_cf + (1 for a secondary
   request) <= cf_kmax, which is cf_hull_adm at CfParams_reply *)
Lemma btr_hull_adm_of_mo : forall (lyc : alayout) (Sc : astate) (regsT : bvmap 5 word) (ch : list (Z * Z * Z))
  (p n : Z), mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> @cf_hull_adm CfParams_reply Sc n.
Proof.
  intros lyc Sc regsT ch p n H.
  unfold ReplyKfMeterB.MT_sec in H. cbn [mo_ok mo_malloc mo_free] in H.
  cbn [cf_hull_adm cf_kmax CfParams_reply] in H |- *.
  pose proof (ReplyKfMeterB.sec_lit n) as E. change (PresetRoom.is_primary n) with (from_primary n) in E.
  destruct (from_primary n); destruct (64512 <? n); cbn [negb] in E; try discriminate E; cbv beta iota in H |- *; lia.
Qed.

(* send_line at R at the top's instance: W_send_line_x.pb_send_line_xR, its premises as top_x's strict SL_x block
   closes them, the realloc rule at R by CfRBridgeRulesRhTopB.ARE_x_kf_rh *)
Lemma btr_SL_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_send_line_xR.sl_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_send_line).
Proof.
  intros rc fx.
  eapply W_send_line_x.pb_send_line_xR with (CTX_R := YCk0.CTX_AREALLOC).
  (* the realloc rule at R first: it fixes RO and HA *)
  only [AREALLOC_R]: (eapply CfRBridgeRulesRhTopB.ARE_x_kf_rh; first [
    exact (@ReplyAreallocTargetB.arealloc_realizes_cf_k_replyB_rc fx rc 0%nat)
    | exact (@ReplyAreallocTargetB.arealloc_null_realizes_cf_replyB_rc fx rc)
    | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low
    | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
    | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
    | (intros; reflexivity) | (intros; apply iff_refl) ]).
  only [RO_ARx]: (intros ly S Hp W mem md H; exact (proj2 (proj2 H))).
  only [HA_call]: exact btr_hull_adm_of_mo.
  (* the instance *)
  only [LAWS]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws.
  only [HP0]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  only [BLKM]: (intros ly S Hp W mem md p n H Hin;
    exact (W_bx_inst_x.bxi_BLKM_cf (cp := CfParams_reply) TfibB (AR_laws_ok_cf (cp := CfParams_reply) _ TfibB)
      ly S Hp W mem md p n (conj (proj1 H) (proj1 (proj2 H))) Hin)).
  (* G_SL inside G_fr_c *)
  only [HG]: (apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB));
    [exact (c_HG_SL TfibB) | exact W_LLVMFuzzerTestOneInput_top_x.GX_ok]).
  only [HGR]: (intros a Hg Hr;
    exact (c_rom_apart TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a Hr (c_HG_SL TfibB a Hg))).
  only [HROMO]: (intros a Ha;
    destruct (c_rom_out TfibB TfibB_syms W_LLVMFuzzerTestOneInput_top_x.top_HEV a Ha) as (H1 & H2 & H3 & H4);
    split; [intros HGa; exact (H1 (c_HG_SL TfibB a HGa)) | exact (conj H2 (conj H3 H4))]).
  only [HGO]: (apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB)); [|exact W_LLVMFuzzerTestOneInput_top_x.GX_ok];
    apply inG_sub;
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]);
    apply Forall_nil).
  only [MTL]: exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX).
  only [TL]: exact W_palib.pb_palib_tfib.
  (* the runtime entries: the W1 lifts at top_x's ARX *)
  only [AERRNO]: exact TopX_RT4.topx_AERRNO_W.
  only [AMEMCPY]: exact TopX_INTRIN_memcpy.topx_AMEMCPY_W.
  (* errno and the placements, decided *)
  only [HCTX_slr]: (vm_compute; repeat (first [left; reflexivity | right])).
  only [HERRNO]: (vm_compute; reflexivity).
  only [HERRZ]: exact (W_errno_azs.errno_azs TfibB TfibB_syms).
  only [HERRAL]: (vm_compute; reflexivity).
  only [HV9]: (vm_compute; reflexivity).
  only [HV10]: (vm_compute; reflexivity).
  only [HV11]: (vm_compute; reflexivity).
  only [HV12]: (vm_compute; reflexivity).
  only [HH18]: (vm_compute; reflexivity).
  only [HH20]: (vm_compute; reflexivity).
  only [HH21]: (vm_compute; reflexivity).
  only [HH22]: (vm_compute; reflexivity).
  only [HH23]: (vm_compute; reflexivity).
  only [HH24]: (vm_compute; reflexivity).
  only [HH25]: (vm_compute; reflexivity).
  only [HRGD]: (vm_compute; repeat split; first [left; discriminate | right; discriminate |
    left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H]).
  (* R's laws *)
  only [R_refl]: exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  only [R_trans]: exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  only [WLE_R]: exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Qed.

Lemma btr_RE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.re_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_relay_event).
Proof.
  intros rc fx.
  eapply W_relay_event_x.pb_relay_event_xR.
  (* the instance, as W_relay_event_x_top *)
  only [LAWS]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws.
  only [HP0]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  (* a live block's size: W_bx_inst_x's bound at ARX's first two conjuncts *)
  only [BLKM]: (intros ly S Hp W mem md p n H Hin;
    exact (W_bx_inst_x.bxi_BLK_cf (cp := CfParams_reply) TfibB (AR_laws_ok_cf (cp := CfParams_reply) _ TfibB)
      ly S Hp W mem md p n (conj (proj1 H) (proj1 (proj2 H))) Hin)).
  only [HG]: (intros a Ha; apply W_LLVMFuzzerTestOneInput_top_x.GX_ok;
    unfold W_LLVMFuzzerTestOneInput_arm_event.et_GRE, inG in Ha; apply Exists_cons in Ha as [Ha | Ha];
    [exact (c_HGlock TfibB a Ha) | exact (c_HG_SL TfibB a Ha)]).
  (* the mutex and strlen entries: the W1 lifts at top_x's ARX *)
  only [ALOCK]: exact TopX_RT_lock.topx_ALOCK_W.
  only [AUNLOCK]: exact TopX_RT_lock.topx_AUNLOCK_W.
  only [ASTRLEN]: exact TopX_RT_B2.topx_ASTRLEN_B_W.
  (* the placements, as W_relay_event_x_top *)
  only [HV3]: (vm_compute; reflexivity).
  only [HLA]: (vm_compute; reflexivity).
  only [HLD]: (intros a Ha Hg;
    exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok (rg_lock fr_RG) 12 (G_SL TfibB fr_RG)
      ltac:(vm_compute; reflexivity) a Hg Ha)).
  only [HLRW]: (intros a Ha Hr;
    exact (c_rom_apart TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a Hr (c_HGlock TfibB a Ha))).
  only [HAOD]: (intros a Ha; cbn [fr_RG fr_globals_b rg_lock rg_send_max rg_client rg_send_dead] in *; lia).
  only [HAO3]: (cbn [fr_RG fr_globals_b rg_send_max rg_client rg_send_dead]; lia).
  only [HLPST]: (intros a _ H; inversion H).
  (* R's laws *)
  only [R_refl]: exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  only [R_trans]: exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  only [WLE_R]: exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  (* send_line at R *)
  only [SL_R]: exact (btr_SL_R rc fx).
Qed.
