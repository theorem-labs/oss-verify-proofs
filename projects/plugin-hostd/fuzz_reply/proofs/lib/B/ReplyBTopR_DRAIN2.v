(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 242 of its 309 lines of code are new or changed and 871 lines of the source are left out. *)
(* ReplyBTop's Section hypotheses DRAIN_R and CNL_dr_R (plugin-hostd fuzz_reply, image B = ASan-UBSan), each a lemma
   whose statement is the hypothesis' type for every rc and fx, at ReplyBTop's instance: MT := ReplyKfMeterB.MT_sec
   nsec_cf cf_kmax, RP := CfRBridgeRulesB.RP_cf, ARx := B top_x's ARX, R := YA0nH.wle' tfibsegs RZ_cf.  Route R only:
   no strict free or realloc realizer is used.
   btr_DRAIN_R: the drain walk at R, W_drain_pb.pb_drain_xR, at R := wle' tfibsegs RZ_cf, RO := arodata_ok_cf (ARX's
     third conjunct) and HA := cf_hull_adm (HA_call by ReplyBTopR_RE.btr_hull_adm_of_mo).  Its premises:
     - the cf rules at R: realloc by CfRBridgeRulesRhTopB.ARE_x_kf_rh over ReplyAreallocTargetB's live-block and
       NULL realizations, free by CfRBridgeRulesFreeRhB.AFREE_x_kf_rh over the primed
       ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all, strndup by CfRBridgeRulesRhStrndupB.ASTRNDUP_x_kf_rh over
       ReplyClosedB.reply_astrndup_cf_B_all, each with the meter rows as ReplyBTop's AMALLOC_R line closes them;
     - send_line at R by ReplyBTopR_RE.btr_SL_R, list_push at R by ReplyBTopR_LP.btr_LP_R (its WR_MMAX is fr_MMAX by
       conversion);
     - the instance facts as B top_x's strict DR_x block closes them: W_drain_pb's drain_* facts, TopX_RT3 / RT4 /
       RT_B2 / INTRIN_memcpy, TopxDrainLitB, the cf blocks law.
   btr_CNL_dr_R: the check_no_loss walk at R, W_check_no_loss.pb_check_no_loss_xR.  Its premises:
     - gesture_model at R by W_gesture_model_g.pb_gesture_model_g_xR (list_find strict by W_list_find.pb_list_find_x,
       list_push at R by btr_LP_R, list_drop at R by LD_R, the three literals' shadow from TopxDrainLitB);
     - list_drop at R: LD_R;
     - next_line strict by W_next_line.pb_next_line_x, bcmp by TopX_CSE.topx_ABCMP_W, the ROM and g_s facts from
       W_LLVMFuzzerTestOneInput_G.c_rom_out, gx_ok / gx_rt of check_no_loss's read-only objects cnl_ro decided below
       (Section cro).
   The one premise left, of btr_CNL_dr_R only, named: LD_R, ReplyBTop's row LD_R (list_drop at R), its Context text.
   rule 24: no function proved (instantiation of proved walks)
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
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_G W_palib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB TopX_INTRIN_memcpy
  TopX_CSE TopX_RT_B2 ReplyClosedB CfRBridgeRulesB ReplyInstFactsB YD1vcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive YGcfNames YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
(* the closers' files and the instance facts they take *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_x W_contract_xR W_contract_xR_g3
  W_contract_xR_g6 W_send_line_xR W_drain_pb W_check_no_loss W_list_drop W_list_find W_gesture_model_g W_next_line
  W_img_x TopX_RT3 TopX_RT4 TopxDrainLitB ReplyAreallocTargetB ReplyDeallocInstB CfRBridgeRulesRhTopB
  CfRBridgeRulesFreeRhB CfRBridgeRulesRhStrndupB ReplyBTopR_RE ReplyBTopR_LP YD25cf ReplyRelroGeoB YCk0 YCej YF0m
  W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG08cf YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).

(* ---- check_no_loss's read-only objects cnl_ro at PB_fr / TfibB, decided: g_gone / g_nout / g_out / g_s are objects
   of G_fr_c (W_LLVMFuzzerTestOneInput_G.c_img), the three literals lie in drain's read-only literal ranges
   (TopxDrainLitB), and no byte of cnl_ro is an owned static, a kept byte, errno or a runtime cell (the decisions of
   W_LLVMFuzzerTestOneInput_G.c_obj_unowned / c_HKEPT and top_x's top_HOWN, over cnl_ro) ---- *)
Section cro.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Lemma cro_HGRR : gx_rt TfibB (cnl_ro (PI := PB_fr)).
Proof.
  intros a Ha. rewrite W_LLVMFuzzerTestOneInput_top_x.top_HEV. split; [|split].
  - exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok TFIB_ERRNO_B 4 (cnl_ro (PI := PB_fr)) eq_refl a Ha).
  - exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok (VAL (A_OBJ 0)) 8 (cnl_ro (PI := PB_fr)) eq_refl a Ha).
  - exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok (VAL (A_OBJ 30)) 8 (cnl_ro (PI := PB_fr)) eq_refl a Ha).
Qed.
Lemma cro_HGR : gx_ok segs TfibB (cnl_ro (PI := PB_fr)).
Proof.
  intros a Ha. split; [|split].
  - unfold cnl_ro in Ha.
    apply inG_cons in Ha as [Ha | Ha];
      [apply (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV); apply (obj_c TfibB); revert a Ha;
       apply rng_cover_zr; reflexivity|].
    apply inG_cons in Ha as [Ha | Ha];
      [apply (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV); apply (obj_c TfibB); revert a Ha;
       apply rng_cover_zr; reflexivity|].
    apply inG_cons in Ha as [Ha | Ha];
      [apply (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV); apply (obj_c TfibB); revert a Ha;
       apply rng_cover_zr; reflexivity|].
    apply inG_cons in Ha as [Ha | Ha];
      [apply (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV); apply (obj_c TfibB); revert a Ha;
       apply rng_cover_zr; reflexivity|].
    apply inG_cons in Ha as [Ha | Ha].
    { change (VAL A_lit_gesture) with (VAL (A_OBJ 18)) in Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
      assert (E : Z.of_nat (length (RelayModel.K_GESTURE ++ [0])) = 14) by reflexivity.
      assert (Hin : VAL (A_OBJ 18) <= a < VAL (A_OBJ 18) + Z.of_nat (length (RelayModel.K_GESTURE ++ [0])))
        by (rewrite E; lia).
      destruct (proj1 (proj2 TopxDrainLitB.topx_HLIT5_x) a Hin) as (sg & Hsg & _ & Hb).
      exists sg. exact (conj Hsg Hb). }
    apply inG_cons in Ha as [Ha | Ha].
    { change (VAL A_lit_begin) with (VAL (A_OBJ 20)) in Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
      assert (E : Z.of_nat (length (RelayModel.W_BEGIN ++ [0])) = 6) by reflexivity.
      assert (Hin : VAL (A_OBJ 20) <= a < VAL (A_OBJ 20) + Z.of_nat (length (RelayModel.W_BEGIN ++ [0])))
        by (rewrite E; lia).
      destruct (proj1 (proj2 TopxDrainLitB.topx_HLIT6_x) a Hin) as (sg & Hsg & _ & Hb).
      exists sg. exact (conj Hsg Hb). }
    apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
    change (VAL A_lit_end) with (VAL (A_OBJ 21)) in Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
    assert (E : Z.of_nat (length (RelayModel.W_END ++ [0])) = 4) by reflexivity.
    assert (Hin : VAL (A_OBJ 21) <= a < VAL (A_OBJ 21) + Z.of_nat (length (RelayModel.W_END ++ [0])))
      by (rewrite E; lia).
    destruct (proj1 (proj2 TopxDrainLitB.topx_HLIT7_x) a Hin) as (sg & Hsg & _ & Hb).
    exists sg. exact (conj Hsg Hb).
  - rewrite (YF0m.ts_owned TfibB TfibB_syms). intros Hex.
    apply Exists_exists in Hex as (r & Hr & Hz). destruct r as [lo n].
    assert (Hb : forallb (fun r => W_LLVMFuzzerTestOneInput_top_x.top_apart (fst r) (snd r) (cnl_ro (PI := PB_fr)))
      YF0m.Tfib_owned_static = true) by reflexivity.
    rewrite forallb_forall in Hb.
    exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok lo n _ (Hb (lo, n) Hr) a Ha Hz).
  - rewrite (YF0m.ts_kept TfibB TfibB_syms). intros Hex.
    apply Exists_exists in Hex as (r & Hr & Hz). destruct r as [lo n].
    assert (Hb : forallb (fun r => W_LLVMFuzzerTestOneInput_top_x.top_apart (fst r) (snd r) (cnl_ro (PI := PB_fr)))
      YF0m.Tfib_kept = true) by reflexivity.
    rewrite forallb_forall in Hb.
    exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok lo n _ (Hb (lo, n) Hr) a Ha Hz).
Qed.
End cro.

(* ---- the callee contracts at B top_x's instance, at one fx and rc: the cf rules at R, the strict leaves ---- *)
Section drx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
Local Notation ARX := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).
Local Notation RPi := CfRBridgeRulesB.RP_cf.
Local Notation RO := (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB).
Local Notation HA := (fun (_ : alayout) (Sc : astate) (_ : bvmap 5 word) (_ : list (Z * Z * Z)) (_ : Z) (n : Z) =>
  @cf_hull_adm CfParams_reply Sc n).

(* the cf rules' instance rows at MT := MT_sec nsec_cf cf_kmax (ReplyBTop's AMALLOC_R / AFREE_R lines), with the
   realizers: realloc of a live block and of NULL, the primed free, strndup *)
Local Ltac rh_rows := first [ exact (@ReplyAreallocTargetB.arealloc_realizes_cf_k_replyB_rc fx rc 0%nat)
  | exact (@ReplyAreallocTargetB.arealloc_null_realizes_cf_replyB_rc fx rc)
  | exact (ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all fx rc)
  | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc)
  | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low
  | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf
  | exact ReplyRelroGeoB.relro_seg_reply_B | exact (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms)
  | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B)
  | (intros; reflexivity) | (intros; apply iff_refl) ].

Lemma drx_ARE_R : arealloc_cf_rule_c_xR segs TfibB [] ARX MT fr_MMAX RPi RO HA YCk0.CTX_AREALLOC (RR rc)
  (SIGMA WS_realloc).
Proof.
  first [ solve [eapply CfRBridgeRulesRhTopB.ARE_x_kf_rh with (nsec_cf := YGcfNames.nsec_cf); rh_rows]
        | solve [unshelve eapply CfRBridgeRulesRhTopB.ARE_x_kf_rh; rh_rows] ].
Qed.
Lemma drx_AFREE_R : afree_cf_rule_c_xR segs TfibB [] ARX MT RPi RO YCk0.CTX_AFREE (RR rc).
Proof.
  first [ solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh with (nsec_cf := YGcfNames.nsec_cf); rh_rows]
        | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; rh_rows] ].
Qed.
Lemma drx_ASTRNDUP_R : astrndup_cf_rule_c_xR segs TfibB [] ARX MT fr_MMAX RPi YCej.CTX_strndup (RR rc)
  (SIGMA WS_strndup).
Proof.
  first [ solve [eapply CfRBridgeRulesRhStrndupB.ASTRNDUP_x_kf_rh with (nsec_cf := YGcfNames.nsec_cf); rh_rows]
        | solve [unshelve eapply CfRBridgeRulesRhStrndupB.ASTRNDUP_x_kf_rh; rh_rows] ].
Qed.

(* a live cf block's size (B top_x's BLKR: AR_blocks_law_cf's last conjunct and YG08cf's bound) *)
Lemma drx_BLKR : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  0 <= n < 2 ^ 30.
Proof.
  intros ly S Hp W mem md p n H Hin.
  destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
    as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia.
Qed.
Lemma drx_BLKN : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  0 <= n.
Proof. intros ly S Hp W mem md p n H Hin. exact (proj1 (drx_BLKR ly S Hp W mem md p n H Hin)). Qed.
Lemma drx_BLKM : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  n < 2 ^ 30.
Proof. intros ly S Hp W mem md p n H Hin. exact (proj2 (drx_BLKR ly S Hp W mem md p n H Hin)). Qed.

(* list_push at R at MMAX := fr_MMAX: ReplyBTopR_LP.btr_LP_R (WR_MMAX is fr_MMAX by conversion) *)
Lemma drx_LP_R : W_contract_xR.lp_spec_g_xR (PI := PB_fr) TfibB [] ARX (RR rc) MT RPi fr_MMAX
  (BASE + AF_fr_list_push).
Proof. exact (ReplyBTopR_LP.btr_LP_R rc fx). Qed.

(* DRAIN_R's text at this fx and rc: W_drain_pb.pb_drain_xR *)
Lemma drx_DR_R : @W_contract_xR.dr_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_drain).
Proof.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  pose proof drx_BLKN. pose proof drx_BLKM.
  pose proof (ReplyKfMeterB.MT_sec_laws NSEC KMAX). pose proof W_palib.pb_palib_tfib.
  pose proof TopX_INTRIN_memcpy.topx_AMEMCPY_W.
  pose proof TopX_RT3.topx_AMEMMOVE_W. pose proof TopX_RT3.topx_AMEMCHR_W.
  pose proof TopX_RT4.topx_AERRNO_W. pose proof TopX_RT4.topx_ASTRRCHR_W.
  pose proof TopX_RT4.topx_ASTRNCMP_W. pose proof TopX_RT4.topx_ASTRCMP_W.
  pose proof TopX_RT_B2.topx_ASTRLEN_B_W.
  pose proof (fun S k k' H => rp_RMM RPi S k' k H).
  pose proof TopxDrainLitB.topx_HLIT5_x. pose proof TopxDrainLitB.topx_HLIT6_x. pose proof TopxDrainLitB.topx_HLIT7_x.
  pose proof W_drain_pb.drain_hctx_re1. pose proof W_drain_pb.drain_hctx_re2.
  pose proof W_drain_pb.drain_hctx_fr2. pose proof W_drain_pb.drain_hctx_sd. pose proof W_drain_pb.drain_hctx_ld.
  pose proof W_drain_pb.drain_HCROM. pose proof W_drain_pb.drain_HVS.
  pose proof W_drain_pb.drain_HV9. pose proof W_drain_pb.drain_HSD.
  pose proof W_drain_pb.drain_HGSB. pose proof W_drain_pb.drain_HSM.
  pose proof W_drain_pb.drain_HRGD. pose proof W_drain_pb.drain_HERRW.
  pose proof W_drain_pb.drain_HG. pose proof W_drain_pb.drain_HGO.
  pose proof W_drain_pb.drain_HGR. pose proof W_drain_pb.drain_HROMO.
  assert (0 < fr_MMAX <= 2 ^ 30) by (split; [apply Z.ltb_lt | apply Z.leb_le]; reflexivity).
  pose proof W_drain_pb.drain_HERRNO. pose proof W_drain_pb.drain_HERRAL. pose proof W_drain_pb.drain_HERRZ.
  pose proof W_drain_pb.drain_HGSZ.
  pose proof W_drain_pb.drain_PSTR. pose proof W_drain_pb.drain_PSTG. pose proof W_drain_pb.drain_PSTO.
  (* the laws of R, RO / HA at the call sites, the cf rules and the callee specs at R *)
  pose proof (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  assert (RO_ARx : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> RO mem)
    by (intros ly0 S0 Hp0 W0 mem0 md0 HAR; exact (proj2 (proj2 HAR))).
  pose proof ReplyBTopR_RE.btr_hull_adm_of_mo as HA_call.
  pose proof drx_ARE_R. pose proof drx_AFREE_R. pose proof drx_ASTRNDUP_R.
  pose proof (ReplyBTopR_RE.btr_SL_R rc fx). pose proof drx_LP_R.
  eapply (W_drain_pb.pb_drain_xR (PI := PB_fr) TfibB [] ARX MT RPi fr_MMAX fr_RG)
    with (R := RR rc) (RO := RO) (HA := HA)
      (CTX_R := YCk0.CTX_AREALLOC) (CTX_F := YCk0.CTX_AFREE) (CTX_S := YCej.CTX_strndup).
  all: try eassumption.
  all: match goal with |- ?G => fail 0 "drx_DR_R: premise left:" G end.
Qed.

(* ---- check_no_loss's callees at the instance ---- *)
(* next_line (W_next_line.pb_next_line_x; check_no_loss keeps it strict) *)
Lemma drx_NL : W_contract_x.nl_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_next_line).
Proof.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  pose proof W_palib.pb_palib_tfib. pose proof W_next_line.nl_objs_apart_fr.
  pose proof TopX_RT3.topx_AMEMCHR_W. pose proof W_next_line.nl_crom_fr.
  eapply W_next_line.pb_next_line_x; eassumption.
Qed.
(* list_find at every G (W_list_find.pb_list_find_x; gesture_model keeps it strict) *)
Lemma drx_LFIND : W_contract_x.lfind_spec_g_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_list_find).
Proof.
  intros G _ _.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  pose proof W_palib.pb_palib_tfib. pose proof TopX_CSE.topx_ABCMP_W.
  eapply W_list_find.pb_list_find_x; eassumption.
Qed.
(* ashp_x is monotone in the length (W_shadow_pin.v ashp_sub over ARx) *)
Lemma drx_ashp_sub : forall a n n', 0 < n' <= n -> W_contract_x.ashp_x (PI := PB_fr) ARX a n ->
  W_contract_x.ashp_x (PI := PB_fr) ARX a n'.
Proof.
  intros a n n' Hn H ly S Hp W mem md HAR. destruct (H ly S Hp W mem md HAR) as [Hr Hh]. split.
  - exact (YG0v.range_addressable_sub _ _ a n a n' Hr ltac:(lia) ltac:(lia)).
  - intros _ s Hs. apply (Hh ltac:(lia)).
    assert (M : shadow_addr (a + n' - 1) / 8 * 8 <= shadow_addr (a + n - 1) / 8 * 8).
    { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
      apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
    lia.
Qed.

(* list_drop at R at this fx and rc: ReplyBTop's row LD_R (the premise LD_R of btr_CNL_dr_R) *)
Hypothesis LD_s : forall (G' : list (Z * Z)), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @gx_rt rc (@PB_fr rc) TfibB G' -> @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (RR rc) MT CfRBridgeRulesB.RP_cf G' (@W_list_drop.A_list_dropP rc (@PB_fr rc)).
Lemma drx_LDROP_R : forall G0, gx_ok segs TfibB G0 -> gx_rt TfibB G0 -> rom_out segs TfibB G0 ->
  W_contract_xR_g3.ldrop_spec_xR (PI := PB_fr) TfibB [] ARX (RR rc) MT RPi G0 (BASE + AF_fr_list_drop).
Proof. exact LD_s. Qed.

(* gesture_model at R (W_gesture_model_g.pb_gesture_model_g_xR); its three literals' shadow from drain's literal facts
   (the same objects A_OBJ 18 / 20 / 21, at their full lengths 14 / 6 / 4) *)
Lemma drx_GM_R : W_contract_xR_g6.gm_spec_g_xR (PI := PB_fr) TfibB [] ARX (RR rc) MT RPi fr_MMAX
  (BASE + AF_fr_gesture_model).
Proof.
  assert (HLITG : W_contract_x.ashp_x (PI := PB_fr) ARX (VAL A_lit_gesture) 13).
  { pose proof (proj2 (proj2 TopxDrainLitB.topx_HLIT5_x)) as H.
    refine (drx_ashp_sub _ _ 13 _ H). split; [lia|]. apply Z.leb_le. reflexivity. }
  assert (HLITB : W_contract_x.ashp_x (PI := PB_fr) ARX (VAL A_lit_begin) 5).
  { pose proof (proj2 (proj2 TopxDrainLitB.topx_HLIT6_x)) as H.
    refine (drx_ashp_sub _ _ 5 _ H). split; [lia|]. apply Z.leb_le. reflexivity. }
  assert (HLITE : W_contract_x.ashp_x (PI := PB_fr) ARX (VAL A_lit_end) 3).
  { pose proof (proj2 (proj2 TopxDrainLitB.topx_HLIT7_x)) as H.
    refine (drx_ashp_sub _ _ 3 _ H). split; [lia|]. apply Z.leb_le. reflexivity. }
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  pose proof W_palib.pb_palib_tfib. pose proof (ReplyKfMeterB.MT_sec_laws NSEC KMAX).
  pose proof TopX_CSE.topx_ABCMP_W. pose proof drx_LFIND. pose proof drx_LP_R. pose proof drx_LDROP_R.
  pose proof (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  eapply (W_gesture_model_g.pb_gesture_model_g_xR (PI := PB_fr) TfibB MT RPi fr_MMAX [] ARX) with (R := RR rc).
  all: try eassumption.
  all: match goal with |- ?G => fail 0 "drx_GM_R: premise left:" G end.
Qed.

(* CNL_dr_R's text at this fx and rc: W_check_no_loss.pb_check_no_loss_xR *)
Lemma drx_CNL_R : ∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @gx_rt rc (@PB_fr rc) TfibB G → @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cnl_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G fr_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_no_loss).
Proof.
  intros G HG _ _.
  pose proof (W_LLVMFuzzerTestOneInput_G.c_rom_out TfibB TfibB_syms W_LLVMFuzzerTestOneInput_top_x.top_HEV) as HROc.
  assert (ROMNS : forall a, in_rom segs a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\
    (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned segs TfibB a)).
  { intros a Ha. destruct (HROc a Ha) as (_ & Hp & He & _). exact (conj He Hp). }
  assert (HRO : rom_out segs TfibB [(VAL A_g_s, 384)]).
  { intros a Ha. destruct (HROc a Ha) as (Hn & Hrest). split; [|exact Hrest].
    intros Hin. apply Hn. apply (c_HGs TfibB).
    apply inG_cons in Hin as [Hin | Hin]; [|exfalso; exact (inG_nil a Hin)].
    unfold in_zr in Hin. cbn [fst snd] in Hin. change (VAL A_g_s) with (VAL (A_OBJ 19)) in Hin.
    rewrite W_drain_pb.drain_HVS in Hin. unfold ASRC. lia. }
  clear HROc.
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  pose proof (W_img_x.fr_img_cover_x TfibB ARX W_LLVMFuzzerTestOneInput_top_x.ARX_laws) as IMGC.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0.
  pose proof drx_BLKN. pose proof W_palib.pb_palib_tfib. pose proof W_check_no_loss.cnl_objs_apart_fr.
  pose proof (ReplyKfMeterB.MT_sec_laws NSEC KMAX).
  pose proof drx_NL. pose proof TopX_CSE.topx_ABCMP_W.
  pose proof cro_HGR. pose proof cro_HGRR.
  pose proof drx_GM_R. pose proof drx_LDROP_R.
  pose proof (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  pose proof (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
  eapply (W_check_no_loss.pb_check_no_loss_xR (PI := PB_fr) TfibB [] ARX MT RPi G fr_MMAX) with (R := RR rc).
  all: try eassumption.
  all: match goal with |- ?G => fail 0 "drx_CNL_R: premise left:" G end.
Qed.
End drx.

(* ---- the rows: each statement is ReplyBTop's Context type, for every rc and fx ---- *)
Lemma btr_DRAIN_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.dr_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_drain).
Proof. intros rc fx. exact (@drx_DR_R fx rc). Qed.

Lemma btr_CNL_dr_R
  (LD_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall (G' : list (Z * Z)), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @gx_rt rc (@PB_fr rc) TfibB G' -> @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (RR rc) MT CfRBridgeRulesB.RP_cf G' (@W_list_drop.A_list_dropP rc (@PB_fr rc))) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @gx_rt rc (@PB_fr rc) TfibB G → @rom_out tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cnl_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G fr_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_no_loss).
Proof. intros rc fx. exact (@drx_CNL_R fx rc (LD_R rc fx)). Qed.
