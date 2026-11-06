(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: new file holding code from lib/A/ReplyRINV_a12.v (419c9d7c02f), lib/A/ReplyRINV_a3.v, lib/A/ReplyRINV.v and lib/A/ReplyTopXRI.v (8da615a239d) and lib/B/ReplyRINVB.v (f908a004fd1), restated at image B's names and at lib/B/ReplyBTop.v's Context texts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRINVB_exit.v; 126 of its 183 lines of code are new or changed and 881 lines of the source are left out. *)
(* The two exit rows of the image-B composition ReplyBTop.replyb_TFIB_B_T_composed, each as a lemma whose statement is
   the row's Section hypothesis, at that composition's instance: MT := ReplyKfMeterB.MT_sec nsec_cf cf_kmax, both
   library budgets ReplyLSBSec.SEC_CALL KF_KC, LS := ReplyLS3B_inst.LSI with fr_CAP /\ fr_SEC, RINV := fr_RINV, the route
   R relation R := YA0nH.wle' tfibsegs RZ_cf, ARX := W_LLVMFuzzerTestOneInput_top_x.ARX rc.
   - btr_LS_exit_end_R: the exit-end model rule with its journal at R.  Its live and survivor conjuncts are
     ReplyLSIexitB_xR.LS_exit_end3e_xR (the rule at any R and any meter); its meter conjunct at MT_sec is
     ReplyLSBSec.fr_SEC_exit_end_a, which reads no journal (ReplyBTopLsiSec.btlsi_LS_exit_end_sec is the same
     composition with the strict journal).  No premise is left.
   - btr_LXRF_R: the relay_finish site block at R, W_bx_rf_x.lx_rf_site_xR at the instance.  Its relay_finish premise
     at R is W_relay_finish.pb_relay_finish_xR at the instance (its placement facts are that file's rf_*_fr lemmas, its
     free rules at R CfRBridgeRulesFreeRhB.AFREE_x_kf_rh / AFREEN_x_kf_rh from the free target, as the composition
     closes its own AFREE_R row).  Two premises are left: the free target ReplyAllocTargetsB.afree_target_replyB (the
     composition's own premise) and gestures_end's contract at R at the instance (GSE_R).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLS3B_inst ReplyB3LScap ReplyB3LS3e ReplyLSBo
  ReplyKfMeterB ReplyLSBSec ReplyKfCB ReplyBTopLsiSec ReplyLSIexitB_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs W_bx_defs_x W_bx_rf_x W_bx_inst
  W_LLVMFuzzerTestOneInput_exit_x W_contract_xR W_relay_finish W_palib TopX_RT_lock YCk0 CfRBridgeRulesB
  CfRBridgeRulesFreeRhB ReplyAllocTargetsB ReplyInstFactsB YD25cf ReplyRelroGeoB YD1vcf ReplyDriverCfB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames YGcfNsec YA0nH YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).

(* the instance's facts the two rows read *)
Lemma btrx_KC_OK : 240 <= ReplyKfCB.KF_KC.
Proof. unfold ReplyKfCB.KF_KC. lia. Qed.

Lemma btrx_BLKN : forall (rc : YM05.RunCeil) ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md p n,
  @W_LLVMFuzzerTestOneInput_top_x.ARX rc ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) -> 0 <= n.
Proof.
  intros rc ly S Hp W mem md p n H Hin.
  destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) _ TfibB) ly S Hp W mem md p n (proj1 H) Hin)
    as (_ & _ & _ & _ & _ & _ & Hn).
  first [ lia | pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)); lia ].
Qed.

(* ================================================================== LS_exit_end_R *)
Lemma btr_LS_exit_end_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ (cx : @lfcx rc) (t : Z) (m : lmod) (ly3 : alayout) (S3 : astate) (rest : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) (mem' : word → option byte) (md' : Model) (fpos k' C cap out : Z), LSs rc cx t m ly3 S3 → @Permutation (Z * Z) (ablocks TfibB ly3 S3) (@input_blks rc cx ++ model_blks m ++ rest) → @Permutation (Z * Z) (ablocks TfibB ly' S') (@input_blks rc cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) → frames S' = [(1, fpos)] → mo_le MT S3 S' C → C <= W_bx_defs.lx_exit_cost MT m → @ajournal_gx_xR rc tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) (G_fr_c TfibB) 0 [] LLVMF_STK (spZ (@c_regs rc cx)) (@lf_FP rc fr_FP_b cx) (@c_ly rc cx) (@c_S rc cx) [] (@c_W rc cx) (@c_mem rc cx) (@c_md rc cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' → cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) → 0 <= t <= OPS_MAX → fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out → @List.NoDup (Z * Z) (ablocks TfibB ly' S') → @Forall rentry (λ e : rentry, @Forall (list byte) (λ x : list byte, x ≠ []) (gse_keys e)) (lm_es m) → fr_live_post_b (@c_S rc cx) (stack_free_state 1 fpos S') k' ∧ fr_surv_b TfibB (@c_ly rc cx) (@c_S rc cx) (@c_W rc cx) (@c_mem rc cx) ly' (stack_free_state 1 fpos S') W' mem' ∧ mo_le MT (@c_S rc cx) (stack_free_state 1 fpos S') XS.
Proof.
  intros rc fx cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H HP3 HP' Hfr Hmo HC0 HJ Hcap Ht HFH HND Hk.
  destruct (ReplyBTopLsiSec.btlsec_parts rc NSEC KMAX ReplyKfCB.KF_KC cx t m ly3 S3 H) as (H3c & H3 & HO & HE & HS).
  (* the live and survivor conjuncts: the exit rule at R *)
  assert (X : ReplyB3LS3e.fr_live_post3_e ReplyLSBo.OUT_MAX4 (c_S cx) (stack_free_state 1 fpos S') k' /\
              ReplyB3LS3e.fr_surv_e TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem')
    by (eapply ReplyLSIexitB_xR.LS_exit_end3e_xR; first [eassumption | apply Z.le_refl]).
  destruct X as [X1 X2].
  (* the meter conjunct: relay_finish's room at the exit, then fr_SEC's bound at the call's end *)
  pose proof (ReplyBTopLsiSec.btlsi_LS_rf_room_sec rc fx NSEC KMAX ReplyKfCB.KF_KC btrx_KC_OK cx t m ly3 S3 H Ht)
    as Hroom.
  assert (X3 : NSEC (stack_free_state 1 fpos S') <= NSEC (c_S cx) + XS)
    by (eapply (ReplyLSBSec.fr_SEC_exit_end_a NSEC KMAX ReplyKfCB.KF_KC btrx_KC_OK);
        first [ exact (fun f s => eq_refl) | eassumption ]).
  split; [| split].
  - first [ exact X1
          | unfold YCfn_cf.fr_live_post_b; unfold ReplyB3LS3e.fr_live_post3_e in X1;
            change YCfn_cf.OUT_MAX with ReplyLSBo.OUT_MAX4; exact X1 ].
  - exact X2.
  - first [ exact X3 | change (NSEC (stack_free_state 1 fpos S') <= NSEC (c_S cx) + XS); exact X3 ].
  Unshelve. all: first [ exact fx | exact rc ].
Qed.

(* ================================================================== LXRF_R *)
(* the free rules at R at the instance, from the free target (the composition's AFREE_R closer, and its free(NULL)
   twin) *)
Ltac btrx_free_fact AF fx rc :=
  first [ exact (AF fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
        | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf
        | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B
        | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B)
        | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl)
        | assumption ].

Lemma btrx_AFREE_R (AF : ReplyAllocTargetsB.afree_target_replyB) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_cf_rule_c_xR fx rc tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) MT CfRBridgeRulesB.RP_cf (@YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB) YCk0.CTX_AFREE (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
  intros rc fx.
  first [ solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; btrx_free_fact AF fx rc]
        | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; btrx_free_fact AF fx rc] ].
Qed.

Lemma btrx_AFREEN_R (AF : ReplyAllocTargetsB.afree_target_replyB) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_null_cf_rule_c_xR fx rc tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) MT CfRBridgeRulesB.RP_cf (@YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB) YCk0.CTX_AFREE (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
  intros rc fx.
  first [ solve [eapply CfRBridgeRulesFreeRhB.AFREEN_x_kf_rh; btrx_free_fact AF fx rc]
        | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREEN_x_kf_rh; btrx_free_fact AF fx rc] ].
Qed.

(* relay_finish's G at R (RF_G ++ G_SL) lies in G_fr_c *)
Lemma btrx_RF_G_ok : forall (rc : YM05.RunCeil),
  gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG).
Proof.
  intros rc. apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB)); [| exact W_LLVMFuzzerTestOneInput_top_x.GX_ok].
  intros a Ha. apply inG_app in Ha as [Ha | Ha].
  - eapply W_LLVMFuzzerTestOneInput_exit_x.HG_RFc; first [ exact (W_bx_inst.bxi_XR_HGM TfibB) | exact Ha ].
  - exact (c_HG_SL TfibB a Ha).
Qed.

(* relay_finish's contract at R at the instance: W_relay_finish.pb_relay_finish_xR *)
Lemma btrx_RF_R (AF : ReplyAllocTargetsB.afree_target_replyB)
  (GSE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.gse_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end)) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.rf_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG AG_THREAD_UP AG_LISTEN YCk0.CTX_AFREE (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_relay_finish).
Proof.
  intros rc fx.
  pose proof (btrx_AFREE_R AF rc fx) as AFREE_R. pose proof (btrx_AFREEN_R AF rc fx) as AFREEN_R.
  pose proof (GSE_R rc fx) as GSE. pose proof (btrx_BLKN rc) as BLKN. pose proof (btrx_RF_G_ok rc) as HGRF.
  (* g_thread_up and g_listen at the walk's placement (W_relay_finish's rf_GTU_fr / rf_GL_fr) *)
  assert (HV1 : @pa_val rc fr_prog_listing (@PB_fr rc) (A_OBJ 1) = AG_THREAD_UP)
    by (eapply eq_trans; [eapply W_relay_finish.rf_GTU_fr | reflexivity]).
  assert (HH8 : @pa_val rc fr_prog_listing (@PB_fr rc) (A_HI 8) + 248 = AG_LISTEN)
    by (eapply eq_trans; [eapply W_relay_finish.rf_GL_fr | reflexivity]).
  eapply W_relay_finish.pb_relay_finish_xR.
  try instantiate (RO := @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB).
  all: first
    [ exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws | exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0
    | exact BLKN | exact W_palib.pb_palib_tfib | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | exact HGRF
    | exact TopX_RT_lock.topx_ALOCK_W | exact TopX_RT_lock.topx_AUNLOCK_W
    | exact HV1 | exact HH8
    | exact AFREE_R | exact AFREEN_R | exact GSE
    | exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))
    | exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))
    | exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))
    | solve [intros ly S Hp W mem md HX; exact (proj2 (proj2 HX))]
    | solve [intros a _ HX; inversion HX]
    | eapply W_relay_finish.rf_HV3_fr | eapply W_relay_finish.rf_HV4_fr | eapply W_relay_finish.rf_HV5_fr
    | eapply W_relay_finish.rf_HH5_fr | eapply W_relay_finish.rf_HH7_fr | eapply W_relay_finish.rf_RGAL_fr
    | eapply W_relay_finish.rf_HIGO_fr | eapply W_relay_finish.rf_HSEPO_fr | eapply W_relay_finish.rf_HPLAINO_fr
    | eapply W_relay_finish.rf_HE5R_fr | eapply W_relay_finish.rf_HROMO_tfib | eapply W_relay_finish.rf_HWSEGE_fr
    | solve [rewrite <- HV1, <- HH8; first [ eapply W_relay_finish.rf_HIG_fr | eapply W_relay_finish.rf_HSEPG_fr
                                     | eapply W_relay_finish.rf_HPLAIN_fr | eapply W_relay_finish.rf_HWSEG_fr
                                     | eapply W_relay_finish.rf_HROMG_fr ]]
    | solve [rewrite <- HH8; first [ eapply W_relay_finish.rf_HROMG_fr | eapply W_relay_finish.rf_HSEPO_fr ]] ].
  Unshelve. all: first [ exact fx | exact rc ].
Qed.

Lemma btr_LXRF_R (AF : ReplyAllocTargetsB.afree_target_replyB)
  (GSE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.gse_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end)) :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_bx_defs_x.lx_rf_site_S_xR fx rc tfib_sink_head TfibB MT (λ _ : Z, XS) REPLYB_RO_LO REPLYB_RO_HI fr_live_pre_b (@LIBROOM_fr CfParams_reply) RLV (G_fr_c TfibB) fr_FP_b [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (LSs rc) CfRBridgeRulesB.RP_cf (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
  intros rc fx.
  pose proof (btrx_RF_R AF GSE_R rc fx) as RF_R. pose proof (btrx_BLKN rc) as BLKN.
  eapply W_bx_rf_x.lx_rf_site_xR.
  try instantiate (MMAX := CfParamsReply.fr_MMAX).
  (* the walk's unused budget XN_LIB and invariant RINV: the composition's *)
  all: first
    [ exact (fun _ : Z => XS) | exact ReplyRINVB.fr_RINV
    | exact RF_R | exact BLKN
    | exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws | exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0
    | exact W_LLVMFuzzerTestOneInput_top_x.GX_ok | exact (c_HG_SL TfibB) | exact (fun S k => iff_refl _)
    | exact (W_bx_inst.bxi_XRF_ERRNO TfibB W_LLVMFuzzerTestOneInput_top_x.top_HEV)
    | solve [ eapply W_bx_inst.bxi_XRF_ROM_OUT; first [ exact TfibB_syms | exact W_LLVMFuzzerTestOneInput_top_x.top_HEV ] ]
    | exact (ReplyBTopLsiSec.btlsi_LS_rf_room_sec rc fx NSEC KMAX ReplyKfCB.KF_KC btrx_KC_OK)
    | solve [intros a _ HX; inversion HX]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.HGs; exact (W_bx_inst.bxi_XR_HGM TfibB) ]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.HG_RFc; exact (W_bx_inst.bxi_XR_HGM TfibB) ]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.XRF_Gcells; exact (W_bx_inst.bxi_XR_HGM TfibB) ]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.XRF_JTAB_ROM ]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.XRF_END5 ]
    | solve [ eapply W_LLVMFuzzerTestOneInput_exit_x.LS_rf_mok_x;
              first [ exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX)
                    | exact (ReplyBTopLsiSec.btlsi_LS_exit_budget_sec rc fx NSEC KMAX ReplyKfCB.KF_KC btrx_KC_OK) ] ]
    | exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc))
    | exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc))
    | exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) ].
  Unshelve. all: first [ exact fx | exact rc | exact (fun _ : Z => XS) | exact ReplyRINVB.fr_RINV ].
Qed.
