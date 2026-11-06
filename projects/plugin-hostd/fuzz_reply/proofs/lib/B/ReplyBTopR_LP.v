(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 65 of its 110 lines of code are new or changed and 893 lines of the source are left out. *)
(* The image-B composition's list_push row at route R (ReplyBTop's Section btop, Context LP_R), closed.
   btr_LP_R states that Context's type word for word, for every rc and fx, at ReplyBTop's instance: MT := ReplyKfMeterB's
   MT_sec nsec_cf cf_kmax, the room record CfRBridgeRulesB.RP_cf, top_x's ARX, R := YA0nH.wle' tfibsegs RZ_cf and
   MMAX := W_LLVMFuzzerTestOneInput_write.WR_MMAX (2 ^ 30 - 2 ^ 20, the instance's cf_malloc_max).
   The closer is the route-R list_push walk W_list_push.pb_list_push_g_xR.  Its premises are discharged by proved lemmas:
   - LAWS / HP0: top_x's ARX_laws / ARX_hp0; TL: W_palib.pb_palib_tfib; MLAW: ReplyKfMeterB.MT_sec_laws;
     HMMAX: W_LLVMFuzzerTestOneInput_write.wr_HMMAX; IMGC: W_img_x.fr_img_cover_x; BLKN: the cf blocks law
     (YG0dcf.alc_blocks over YG0lawscf.AR_laws_ok_cf), as top_x's own proof states it;
   - the caller contexts: realloc returns to list_push + 0xc0 (a row of YCk0.CTX_AREALLOC), malloc to list_push + 0xe4
     (a row of YCk0.CTX_AMALLOC), each by evaluation, as top_x's strict LP;
   - AMEMCPY: TopX_INTRIN_memcpy.topx_AMEMCPY_W (strict, as the walk takes it);
   - the laws of R: YA0nH.wle'_refl / wle'_trans / wle_wle'; RO := arodata_ok_cf, RO_ARx: ARX's last conjunct;
   - HA := cf_hull_adm Sc n (the realloc rule's entry admission at CfParams_reply), HA_call from MT_sec's budget and
     ReplyHullAdm.adm_charge_eq (a request is secondary exactly when the meter charges it);
   - ARE_R: CfRBridgeRulesRhTopB.ARE_x_kf_rh over ReplyAreallocTargetB's two realloc realizations;
   - AMA_R: CfRBridgeRulesRhTopB.AMA_x_kf_rh over ReplyClosedB.reply_amalloc_target_B;
   each rule's instance rows as ReplyBTop's AMALLOC_R line closes them (the cf laws, the segments' low bound, the api
   environment, the nsec facts, the relro rows, MT_sec's equations by reflexivity).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1w_cf YD1w_cf_fp YD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1mcf YD1pcf ReplyTFIBBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x ReplyLSB ReplyRINVB.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

(* the notations' modules (as ReplyBTop requires them), and the closer with its dischargers *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSBo ReplyLS3B_inst ReplyB3LScap ReplyKfMeterB
  ReplyLSBSec ReplyKfCB YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive YGcfNames YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_list_push W_contract_xR W_palib W_img_x
  W_LLVMFuzzerTestOneInput_write TopX_INTRIN_memcpy YCk0 CfRBridgeRulesB CfRBridgeRulesRhTopB ReplyAreallocTargetB
  ReplyClosedB YD25cf ReplyInstFactsB ReplyRelroGeoB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyHullAdm.
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).

(* the cf allocator rules' instance rows, as ReplyBTop's AMALLOC_R line closes them *)
Ltac btr_rows rc fx :=
  first [ exact (@ReplyAreallocTargetB.arealloc_realizes_cf_k_replyB_rc fx rc 0)
        | exact (@ReplyAreallocTargetB.arealloc_null_realizes_cf_replyB_rc fx rc)
        | exact (ReplyClosedB.reply_amalloc_target_B fx rc)
        | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
        | exact YD25cf.tfib_segs_low
        | exact ReplyInstFactsB.replyb_api_env
        | exact YGcfNsec.nsec_malloc_cf
        | exact YGcfNsec.nsec_free_cf
        | exact ReplyRelroGeoB.relro_seg_reply_B
        | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
        | (intros; reflexivity)
        | (intros; apply iff_refl) ].

Lemma btr_LP_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.lp_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf W_LLVMFuzzerTestOneInput_write.WR_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_push).
Proof.
  intros rc fx.
  (* realloc's entry admission from the meter's budget at the call: MT_sec charges a request 1 exactly when it is
     secondary, which is the admission's charge *)
  assert (HA_call : forall (lyc : alayout) (Sc : astate) (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) (p n : Z),
    mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> @cf_hull_adm CfParams_reply Sc n).
  { intros lyc Sc regsT ch p n H. unfold ReplyKfMeterB.MT_sec in H. cbn [mo_ok mo_malloc mo_free] in H.
    cbn [cf_hull_adm cf_kmax CfParams_reply] in H |- *. rewrite ReplyHullAdm.adm_charge_eq. lia. }
  (* the blocks law at ARX (top_x's BLKN) *)
  assert (BLKN : forall ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md p n,
    @W_LLVMFuzzerTestOneInput_top_x.ARX rc ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) -> 0 <= n).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) _ TfibB) ly S Hp W mem md p n
      (proj1 H) Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    lia. }
  Set Generate Goal Names.
  eapply (@W_list_push.pb_list_push_g_xR fx rc tfib_sink_head (@PB_fr rc)) with
    (RO := @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB)
    (HA := fun (_ : alayout) (Sc : astate) (_ : bvmap 5 word) (_ : list (Z * Z * Z)) (_ : Z) (n : Z) =>
             @cf_hull_adm CfParams_reply Sc n)
    (CTX_R := YCk0.CTX_AREALLOC) (CTX_M := YCk0.CTX_AMALLOC).
  all: try (only [LAWS]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws).
  all: try (only [HP0]: exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0).
  all: try (only [TL]: exact W_palib.pb_palib_tfib).
  all: try (only [MLAW]: exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX)).
  all: try (only [HMMAX]: exact W_LLVMFuzzerTestOneInput_write.wr_HMMAX).
  all: try (only [IMGC]: exact (W_img_x.fr_img_cover_x TfibB _ W_LLVMFuzzerTestOneInput_top_x.ARX_laws)).
  all: try (only [BLKN]: exact BLKN).
  all: try (only [HCTX_lp_realloc]: solve [vm_compute; repeat (first [left; reflexivity | right])]).
  all: try (only [HCTX_lp_malloc]: solve [vm_compute; repeat (first [left; reflexivity | right])]).
  all: try (only [AMEMCPY]: exact TopX_INTRIN_memcpy.topx_AMEMCPY_W).
  all: try (only [R_refl]: exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))).
  all: try (only [R_trans]: exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))).
  all: try (only [WLE_R]: exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))).
  all: try (only [RO_ARx]: solve [intros ly S Hp W mem md H; exact (proj2 (proj2 H))]).
  all: try (only [HA_call]: exact HA_call).
  all: try (only [ARE_R]: solve [eapply CfRBridgeRulesRhTopB.ARE_x_kf_rh with (nsec_cf := YGcfNames.nsec_cf);
    btr_rows rc fx]).
  all: try (only [AMA_R]: solve [eapply CfRBridgeRulesRhTopB.AMA_x_kf_rh with (nsec_cf := YGcfNames.nsec_cf);
    btr_rows rc fx]).
Qed.
