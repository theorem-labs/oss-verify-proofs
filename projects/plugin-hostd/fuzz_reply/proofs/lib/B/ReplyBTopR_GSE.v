(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v, with its module paths changed; 156 of its 206 lines of code are new or changed and 888 lines of the source are left out. *)
(* The image-B composition ReplyBTop at route R: its Section hypotheses GSE_R (gestures_end's contract at R) and GE_R
   (gesture_end's, its callee; btrg_GE_R, plug `exact (btrg_GE_R rc fx)`), closed.
   btrg_GSE_R's statement is GSE_R's Context type in lib/B/ReplyBTop.v, word for word, under ReplyBTop's notations
   (copied below), with one argument AF, ReplyBTop's free target
   (as ReplyBTopR_EXIT.btr_LXRF_R takes it): the plug is `exact (btrg_GSE_R AF rc fx)`.
   The closer is W_gestures_end_top.pb_gestures_end_closed_xR at the top's instance (PB_fr, TfibB, PST = [], top_x's
   ARX, R := wle' tfibsegs RZ_cf, MT := MT_sec nsec_cf cf_kmax, RP := RP_cf, MMAX := fr_MMAX, RG := fr_RG), as image A's
   top_x.v:1983 closes its GSE_R. Its premises:
   - the instance and the placements: top_x's facts (ARX_laws, ARX_hp0, GX_ok, top_HOWN, top_apart_ok, top_HEV), _G's
     G_fr_c facts, and computation, as top_x's strict GSE_x block (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:1200-1260) discharges them;
   - GE_R, gesture_end at R: W_gesture_end.pb_gesture_end_xR at the same instance, its send_line at R
     ReplyBTopR_RE.btr_SL_R, its strlen TopX_RT_B2.topx_ASTRLEN_B_W;
   - the free rules at R: ReplyBTopR_EXIT.btrx_AFREE_R / btrx_AFREEN_R AF; RO := arodata_ok_cf, RO_ARx by ARX's third
     conjunct;
   - R's laws: YA0nH.wle'_refl / wle'_trans / wle_wle'.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_gesture_end W_gestures_end_top TopxImageB W_img_x ReplyAllocTargetsB ReplyBTopR_RE ReplyBTopR_EXIT.
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

Local Notation TX_ARX rc := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).

Ltac btrg_inst rc fx :=
  first [ exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws | exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0
        | exact (ReplyBTopR_EXIT.btrx_BLKN rc)
        | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | exact W_palib.pb_palib_tfib
        | exact TopX_RT_B2.topx_ASTRLEN_B_W
        | exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))
        | exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))
        | exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) ].

(* G_SL inside G_fr_c; its rom_out; the image cover; the end5 literal and g_out's footprint (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:1202-1255) *)
Lemma btrg_HG : forall (rc : YM05.RunCeil), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (G_SL TfibB fr_RG).
Proof. intros rc. apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB)); [exact (c_HG_SL TfibB) | exact W_LLVMFuzzerTestOneInput_top_x.GX_ok]. Qed.

Lemma btrg_HROMO : forall (rc : YM05.RunCeil), @rom_out YE2k.tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (G_SL TfibB fr_RG).
Proof.
  intros rc a Ha. destruct (c_rom_out TfibB TfibB_syms W_LLVMFuzzerTestOneInput_top_x.top_HEV a Ha) as (H1 & H2 & H3 & H4).
  split; [intros HGa; exact (H1 (c_HG_SL TfibB a HGa)) | exact (conj H2 (conj H3 H4))].
Qed.

(* gestures_end's callee at R, gesture_end: W_gesture_end.pb_gesture_end_xR, its send_line at R ReplyBTopR_RE.btr_SL_R;
   its statement is ReplyBTop's GE_R text, byte for byte *)
Lemma btrg_GE_R :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.ge_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gesture_end).
Proof.
  intros rc fx.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws as LAWS0. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0 as HP00.
  pose proof (ReplyBTopR_EXIT.btrx_BLKN rc) as BLKN0.
  pose proof (btrg_HG rc) as HG0. pose proof (btrg_HROMO rc) as HROMO0.
  assert (IMGC0 : forall ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md, TX_ARX rc ly S Hp W mem md ->
      fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
    by exact (W_img_x.fr_img_cover_x TfibB (TX_ARX rc) W_LLVMFuzzerTestOneInput_top_x.ARX_laws).
  assert (HEND5I0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a < @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 ->
      in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha.
    apply (segin_ok (@pa_segs rc fr_prog_listing (@PB_fr rc))).
    assert (E : a = 134912 \/ a = 134913 \/ a = 134914 \/ a = 134915 \/ a = 134916) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; subst a; vm_compute; reflexivity. }
  assert (HEND5G0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a < @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 ->
      ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\
      ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha.
    split; [|split].
    - intros H. apply (c_HG_SL TfibB) in H. rewrite (G_fr_c_val TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV) in H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]) ltac:(vm_compute; reflexivity) a H Ha).
    - rewrite (ts_owned TfibB TfibB_syms). intros H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 Tfib_owned_static ltac:(vm_compute; reflexivity) a H Ha).
    - rewrite W_LLVMFuzzerTestOneInput_top_x.top_HEV. intros He.
      apply (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 [(TFIB_ERRNO_B, 4)] ltac:(vm_compute; reflexivity) a); [|exact Ha].
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He. }
  assert (HEND5S0 : ashp_x (TX_ARX rc) (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) 5).
  { apply (TopxImageB.tfib_shp_x TfibB TfibB_syms (TX_ARX rc)).
    - intros ly S Hp W mem md HAR. exact (alx_const_cells _ _ _ W_LLVMFuzzerTestOneInput_top_x.ARX_laws ly S Hp W mem md HAR).
    - intros ly S Hp W mem md r HAR Hr. exact (alx_zshadow _ _ _ W_LLVMFuzzerTestOneInput_top_x.ARX_laws ly S Hp W mem md r HAR Hr).
    - vm_compute. reflexivity. }
  assert (cov_pair : forall lo hi a, rng_inb lo (hi - lo) G_fr_obj = true -> lo <= a < hi -> inG (G_fr_c TfibB) a)
    by (intros lo hi a H Ha; apply (obj_c TfibB); apply (rng_cover lo (hi - lo) G_fr_obj H a); lia).
  assert (HOUTG0 : forall r a, In r (aout_fp TfibB fr_RG 0 0) -> fst r <= a < snd r ->
      ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
      in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\ ~ in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\
      ~ Exists (in_zr a) (as_owned_static TfibB)).
  { intros r a Hin Ha Hne.
    assert (HGa : inG (G_fr_c TfibB) a).
    { unfold aout_fp in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; cbn [fst snd] in Ha;
        first [ match type of Ha with ?lo <= _ < ?hi => apply (cov_pair lo hi a); [vm_compute; reflexivity | exact Ha] end
              | exfalso; apply Hne; lia ]. }
    split; [|split].
    - first [exact (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a HGa) | exact (c_img TfibB a HGa)].
    - intros Hr. first [exact (c_rom_apart TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a Hr HGa) | exact (c_rom_apart TfibB a Hr HGa)].
    - exact (W_LLVMFuzzerTestOneInput_top_x.top_HOWN a HGa). }
  assert (HOUTLO0 : forall r, In r (aout_fp TfibB fr_RG 0 0) -> 0 <= fst r /\ snd r <= 0x5fc000).
  { intros r Hin. unfold aout_fp in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; split; apply Z.leb_le; vm_compute; reflexivity. }
  eapply W_gesture_end.pb_gesture_end_xR.
    all: try (only [SL_R]: exact (ReplyBTopR_RE.btr_SL_R rc fx)).
    all: try (only [PSTR]: (intros a _ H; inversion H)).
    all: try (only [HEND5P]: (intros a _ H; inversion H)).
    all: try (only [HOUTLO]: exact HOUTLO0).
    all: first [ assumption | btrg_inst rc fx | idtac ].
Qed.

Lemma btrg_GSE_R (AF : ReplyAllocTargetsB.afree_target_replyB) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.gse_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end).
Proof.
  intros rc fx.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws as LAWS0. pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0 as HP00.
  pose proof (ReplyBTopR_EXIT.btrx_BLKN rc) as BLKN0.
  pose proof (btrg_HG rc) as HG0. pose proof (btrg_HROMO rc) as HROMO0.
  assert (IMGC0 : forall ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md, TX_ARX rc ly S Hp W mem md ->
      fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
    by exact (W_img_x.fr_img_cover_x TfibB (TX_ARX rc) W_LLVMFuzzerTestOneInput_top_x.ARX_laws).
  assert (HEND5I0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a < @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 ->
      in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha.
    apply (segin_ok (@pa_segs rc fr_prog_listing (@PB_fr rc))).
    assert (E : a = 134912 \/ a = 134913 \/ a = 134914 \/ a = 134915 \/ a = 134916) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; subst a; vm_compute; reflexivity. }
  assert (HEND5G0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a < @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 ->
      ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\
      ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha.
    split; [|split].
    - intros H. apply (c_HG_SL TfibB) in H. rewrite (G_fr_c_val TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV) in H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]) ltac:(vm_compute; reflexivity) a H Ha).
    - rewrite (ts_owned TfibB TfibB_syms). intros H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 Tfib_owned_static ltac:(vm_compute; reflexivity) a H Ha).
    - rewrite W_LLVMFuzzerTestOneInput_top_x.top_HEV. intros He.
      apply (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 [(TFIB_ERRNO_B, 4)] ltac:(vm_compute; reflexivity) a); [|exact Ha].
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He. }
  assert (HEND5S0 : ashp_x (TX_ARX rc) (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) 5).
  { apply (TopxImageB.tfib_shp_x TfibB TfibB_syms (TX_ARX rc)).
    - intros ly S Hp W mem md HAR. exact (alx_const_cells _ _ _ W_LLVMFuzzerTestOneInput_top_x.ARX_laws ly S Hp W mem md HAR).
    - intros ly S Hp W mem md r HAR Hr. exact (alx_zshadow _ _ _ W_LLVMFuzzerTestOneInput_top_x.ARX_laws ly S Hp W mem md r HAR Hr).
    - vm_compute. reflexivity. }
  assert (cov_pair : forall lo hi a, rng_inb lo (hi - lo) G_fr_obj = true -> lo <= a < hi -> inG (G_fr_c TfibB) a)
    by (intros lo hi a H Ha; apply (obj_c TfibB); apply (rng_cover lo (hi - lo) G_fr_obj H a); lia).
  assert (HOUTG0 : forall r a, In r (aout_fp TfibB fr_RG 0 0) -> fst r <= a < snd r ->
      ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
      in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\ ~ in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\
      ~ Exists (in_zr a) (as_owned_static TfibB)).
  { intros r a Hin Ha Hne.
    assert (HGa : inG (G_fr_c TfibB) a).
    { unfold aout_fp in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; cbn [fst snd] in Ha;
        first [ match type of Ha with ?lo <= _ < ?hi => apply (cov_pair lo hi a); [vm_compute; reflexivity | exact Ha] end
              | exfalso; apply Hne; lia ]. }
    split; [|split].
    - first [exact (c_img TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a HGa) | exact (c_img TfibB a HGa)].
    - intros Hr. first [exact (c_rom_apart TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV a Hr HGa) | exact (c_rom_apart TfibB a Hr HGa)].
    - exact (W_LLVMFuzzerTestOneInput_top_x.top_HOWN a HGa). }
  assert (HOUTLO0 : forall r, In r (aout_fp TfibB fr_RG 0 0) -> 0 <= fst r /\ snd r <= 0x5fc000).
  { intros r Hin. unfold aout_fp in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; split; apply Z.leb_le; vm_compute; reflexivity. }
  (* gesture_end at R: its send_line at R is ReplyBTopR_RE.btr_SL_R *)
  pose proof (btrg_GE_R rc fx) as GE_R0.
  eapply W_gestures_end_top.pb_gestures_end_closed_xR with (CTX_AFREE := YCk0.CTX_AFREE).
  all: try (only [GE_R]: exact GE_R0).
  all: try (only [AFREE_R]: exact (ReplyBTopR_EXIT.btrx_AFREE_R AF rc fx)).
  all: try (only [AFREEN_R]: exact (ReplyBTopR_EXIT.btrx_AFREEN_R AF rc fx)).
  all: try (only [RO_ARx]: (intros ly S Hp W mem md H; exact (proj2 (proj2 H)))).
  all: try (only [HCTX_gse_loop]: (vm_compute; repeat (first [left; reflexivity | right]))).
  all: try (only [HCTX_gse_tail]: (vm_compute; repeat (first [left; reflexivity | right]))).
  all: try (only [PSTR]: (intros a _ H; inversion H)).
  all: try (only [HEND5P]: (intros a _ H; inversion H)).
  all: first [ assumption | btrg_inst rc fx | idtac ].
  Unshelve. all: first [ exact fx | exact rc | idtac ].
Qed.

