(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 95 of its 138 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: image B (plugin-hostd fuzz_reply, ASan-UBSan): the row LD_R of ReplyBTop's
   Section btop, list_drop at route R, at ReplyBTop's instance (MT := ReplyKfMeterB.MT_sec nsec_cf cf_kmax, ARx := top_x's
   ARX, R := wle' tfibsegs RZ_cf), at every G' with gx_ok / gx_rt / rom_out.
   btr_LD_R is W_list_drop.pb_list_drop_ro_xR (list_drop's R walk) at that instance, with RO := arodata_ok_cf (top_x's
   ARX carries it) and CTX := YCk0.CTX_AFREE.  Its premises are closed by:
   - R_refl / R_trans / WLE_R: YA0nH's wle'_refl / wle'_trans / wle_wle' at tfibsegs, RZ_cf;
   - LAWS: top_x's ARX_laws; HP0: ARX's second conjunct; TL: W_palib.pb_palib_tfib; RO_ARx: ARX's last conjunct;
   - AMOVE: TopX_RT3.topx_AMEMMOVE_W, __asan_memmove's strict rule at TopX_RT_lock.ARX_rtW (top_x's ARX, same body);
   - AFREE_R: CfRBridgeRulesFreeRhB.AFREE_x_kf_rh, its free target the closed primed realizer
     ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all, as in ReplyBTopR_SR.btr_SR_R;
   - HCTX_ld_free: the return address list_drop + 0x9c is a row of CTX_AFREE.
   btr_LDROP_R is W_list_drop.pb_list_drop_at_xR (list_drop's R walk at its entry BASE + AF_fr_list_drop, Section d
   wR) at the same instance, with the same discharges; its ROMS premise (W_list_drop.v:599) is LDROP_R's third premise.
   The statements are ReplyBTop.v's Contexts LD_R and LDROP_R word
   for word (each fit Goal below closes by exact), so ReplyBTop closes them by `exact ReplyBTopR_LD.btr_LD_R` and
   `exact ReplyBTopR_LD.btr_LDROP_R`.
   rule 24: proves no function (kind: segment lemma) *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0 W_sites_x TopX_RT_lock TopX_RT3.
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

(* LD_R: W_list_drop.pb_list_drop_ro_xR at ReplyBTop's instance *)
Lemma btr_LD_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall (G' : list (Z * Z)),
  gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @gx_rt rc (@PB_fr rc) TfibB G' ->
  @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' ->
  @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (RR rc) MT CfRBridgeRulesB.RP_cf G' (@W_list_drop.A_list_dropP rc (@PB_fr rc)).
Proof.
  intros rc fx G' HG GRT HRO.
  Set Generate Goal Names.
  eapply W_list_drop.pb_list_drop_ro_xR
    with (RO := @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB)
         (CTX := YCk0.CTX_AFREE).
  try (only [R_refl]: solve [exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [R_trans]: solve [exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [WLE_R]: solve [exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [LAWS]: solve [exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws]).
  try (only [HP0]: solve [intros ly S Hp W mem md H; exact (proj1 (proj2 H))]).
  try (only [TL]: solve [exact W_palib.pb_palib_tfib]).
  try (only [RO_ARx]: solve [intros ly S Hp W mem md H; exact (proj2 (proj2 H))]).
  try (only [AMOVE]: solve [exact (@TopX_RT3.topx_AMEMMOVE_W fx rc)]).
  try (only [AFREE_R]: solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh;
    first [ exact (ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all fx rc)
          | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
          | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env
          | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
          | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
          | (intros; reflexivity) | (intros; apply iff_refl) ]]).
  try (only [HCTX_ld_free]: solve [unfold YCk0.CTX_AFREE; cbn [In]; repeat (first [left; reflexivity | right])]).
  all: first [exact HG | exact GRT | exact HRO | idtac].
Qed.

(* fit check: btr_LD_R's type is ReplyBTop.v's LD_R text, quoted verbatim *)
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall (G' : list (Z * Z)), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @gx_rt rc (@PB_fr rc) TfibB G' -> @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (RR rc) MT CfRBridgeRulesB.RP_cf G' (@W_list_drop.A_list_dropP rc (@PB_fr rc)).
Proof. exact btr_LD_R. Qed.


(* LDROP_R: W_list_drop.pb_list_drop_at_xR at ReplyBTop's instance; its ROMS premise is LDROP_R's third premise *)
Lemma btr_LDROP_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall (G' : list (Z * Z)),
  gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> gx_rt (PI := @PB_fr rc) TfibB G' ->
  (forall a, in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a ->
    (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB a) /\
    ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\ ~ inG G' a) ->
  @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G'
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_drop).
Proof.
  intros rc fx G' HG GRT HROMS.
  Set Generate Goal Names.
  eapply W_list_drop.pb_list_drop_at_xR
    with (RO := @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB)
         (CTX := YCk0.CTX_AFREE).
  try (only [R_refl]: solve [exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [R_trans]: solve [exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [WLE_R]: solve [exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))]).
  try (only [LAWS]: solve [exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws]).
  try (only [HP0]: solve [intros ly S Hp W mem md H; exact (proj1 (proj2 H))]).
  try (only [TL]: solve [exact W_palib.pb_palib_tfib]).
  try (only [RO_ARx]: solve [intros ly S Hp W mem md H; exact (proj2 (proj2 H))]).
  try (only [AMOVE]: solve [exact (@TopX_RT3.topx_AMEMMOVE_W fx rc)]).
  try (only [AFREE_R]: solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh;
    first [ exact (ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all fx rc)
          | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
          | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env
          | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
          | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
          | (intros; reflexivity) | (intros; apply iff_refl) ]]).
  try (only [HCTX_ld_free]: solve [unfold YCk0.CTX_AFREE; cbn [In]; repeat (first [left; reflexivity | right])]).
  all: first [exact HG | exact GRT | exact HROMS | idtac].
Qed.

(* fit check: btr_LDROP_R's type is ReplyBTop.v's LDROP_R text, quoted verbatim *)
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall (G' : list (Z * Z)), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> gx_rt (PI := @PB_fr rc) TfibB G' -> (forall a, in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a -> (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB a) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\ ~ inG G' a) -> @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G' (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_drop).
Proof. exact btr_LDROP_R. Qed.

