(* Made by a Theorem Labs lane (2026-10-31): THE IMAGE-B COMPOSITION at KF-COUNT's MT_sec and route R.  TFIB_B_T
   (lib/A/ReplyTFIB.v) for plugin-hostd/fuzz_reply.asan-ubsan, from the B top at R (lib/B/W_LLVMFuzzerTestOneInput_top_x.v
   fr_contract_top_xR, R := wle' tfibsegs RZ_cf) through the B cf driver (lib/B/ReplyDriverCfB.v replyb_tfib_b_of_top_x_sec).
   The image-B twin of lib/A/ReplyATopX.v's shape: the count nsec := YGcfNames.nsec_cf with KMAX := CfParams_reply's
   cf_kmax (2 ^ 23), MT := ReplyKfMeterB.MT_sec nsec KMAX, both library budgets ReplyLSBSec.SEC_CALL KF_KC, and the LS
   instance a Theorem Labs lane's LSI with fr_CAP /\ fr_SEC (lib/B/ReplyBTopLsiSec.v), whose btlsi_*_sec rules close the LS
   rows (B's LSI alone has no fr_SEC, so the LS rows' meter conjuncts hold only at this instance).
   Each obligation of fr_contract_top_xR at these parameters that no existing B lemma closes is a Section hypothesis
   below, in the text a probe of the built top_x printed; the cf allocator's realizers are the theorem's two premises
   (lib/B/ReplyAllocTargetsB.v's targets; the free one is the primed afree_realizes_cf_rh).
   proves no function (kind: composition). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_G YD1u YD1ucf W_palib
  W_check_bounded W_check_shape_done W_check_no_loss_read ReplyRINVB_add W_rg_place W_relay_src_c ReplyRINVBHead
  ReplyRINVB_write ReplyRINVB_exit ReplyRINVB_gone ReplyRINVB_rm_a12 ReplyBTopLsiCnt ReplyBTopLsi ReplyB3TrPeakCnlW8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB ReplyBTopLsiSec
  ReplyRINVB_rmsrc ReplyBTopRiRmRr ReplyBTopCntRm ReplyBTopCntDr TopX_LIT ReplyAllocTargetsB TopX_INTRIN_memcpy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB2 TopxTLFB W_ERRL_x TopX_RELAY TopX_SNP TopX_CSE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyDeallocInstB TopX_XE_LIT ReplyGoneRB ReplyBTopR_OA ReplyBTopR_LP ReplyBTopR_RE ReplyBTopR_EXIT ReplyBTopR_SR ReplyBTopR_RELAY ReplyBTopR_DRAIN2 ReplyBTopR_GSE ReplyBTopR_LD ReplyBTopX_HP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB_gone_ls TopxEntry TopX_RT_B2 ReplyClosedB
  CfRBridgeRulesB CfRStrndup CfRBridgeRulesRhTopB CfRBridgeRulesFreeRhB W_frame_flag_cf ReplyInstFactsB YD1vcf.
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

Section btop.
(* the driver's instance facts at nsec := nsec_cf, KMAX := cf_kmax, XN := SEC_CALL KF_KC *)
Let XNS_NN : 0 <= XS. Proof. vm_compute. discriminate. Qed.
Let KC_OK : 240 <= ReplyKfCB.KF_KC. Proof. unfold ReplyKfCB.KF_KC. lia. Qed.
Let NSEC_HULL : forall S, NSEC S <= KMAX -> @cf_hull_ok CfParams_reply S := fun S H => H.
Let NSEC_START : NSEC init_state + 12 + 4 * XS <= KMAX. Proof. vm_compute. discriminate. Qed.
(* the obligations of fr_contract_top_xR at the parameters above that the proof does not close, in top_x's order,
   each for every rc, fx (a probe's text) *)

Theorem replyb_TFIB_B_T_composed :
  ReplyAllocTargetsB.amalloc_target_replyB ->
  ReplyAllocTargetsB.afree_target_replyB ->
  TFIB_B_T.
Proof.
  intros AM AF.
  refine (replyb_tfib_b_of_top_x_sec NSEC KMAX XS YGcfNsec.nsec_malloc_cf YGcfNsec.nsec_free_cf XNS_NN NSEC_HULL
    NSEC_START (fun rc fx => _) (fun rc => AM YK11.fx0 rc) (fun rc => AF YK11.fx0 rc)).
  Set Generate Goal Names.
  eapply (@W_LLVMFuzzerTestOneInput_top_x.fr_contract_top_xR fx rc YE2k.tfib_sink_head MT (fun _ => XS) (fun _ => XS)
    REPLYB_RO_LO REPLYB_RO_HI YCfn_cf.fr_live_pre_b YCfn_cf.fr_live_post_b (YCfn_cf.fr_surv_b YD2l.TfibB)
    (LIBROOM_fr (cp := CfParamsReply.CfParams_reply)) RLV YCfn_cf.fr_FP_b (LSs rc) ReplyRINVB.fr_RINV).
  instantiate (gn_pk := ReplyB3LScnt.pk_gone (rc := rc)).
  instantiate (RO := (@YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB)).
  (* each obligation closed by an existing lemma, by its top_x binder name *)
  try (only [RP_NP]: solve [first [ exact (fun S k => iff_refl _) ]]).
  try (only [NPF]: solve [first [ intros S f H; eapply YGcfRoomLive.room_live_set_fs; exact H ]]).
  try (only [RI_head_nout]: solve [first [ eapply W_LLVMFuzzerTestOneInput_top_x.top_RI_head_nout_fr | apply ReplyRINVB.RI_head_nout_holds_b ]]).
  try (only [LS_head_nout]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_head_nout_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_head_skip]: solve [first [ eapply W_LLVMFuzzerTestOneInput_top_x.top_RI_head_skip_fr | apply ReplyRINVB.RI_head_skip_holds_b ]]).
  try (only [LS_head_skip]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_head_skip_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [TL]: solve [first [ exact W_palib.pb_palib_tfib ]]).
  try (only [TLF]: solve [first [ exact (TopxTLFB.topx_TLF_B_all rc fx) ]]).
  try (only [MLAW]: solve [first [ exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) ]]).
  try (only [FFL]: solve [first [ exact (fun ly S Hp W mem md cid pos H => W_frame_flag_cf.frame_flag_lawP_x_ARX ly S Hp W mem md cid pos (conj (proj1 H) (proj1 (proj2 H)))) ]]).
  try (only [ERRL_x]: solve [first [ exact (W_ERRL_x.errno_law_x_TfibB_all rc fx (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)) ]]).
  try (only [HRO]: solve [first [ solve [eapply W_LLVMFuzzerTestOneInput_G.c_rom_out; first [exact TfibB_syms | exact W_LLVMFuzzerTestOneInput_top_x.top_HEV | exact (c_HKEPT TfibB TfibB_syms W_LLVMFuzzerTestOneInput_top_x.top_HEV) | assumption]] | exact (@W_LLVMFuzzerTestOneInput_G.c_rom_out fx rc TfibB TfibB_syms W_LLVMFuzzerTestOneInput_top_x.top_HEV) ]]).
  try (only [AIL]: solve [first [ eapply YD1u.tfib_AIL; exact TfibB_syms | eapply YD1ucf.tfib_AIL; exact TfibB_syms ]]).
  try (only [CB_x]: solve [first [ eapply W_check_bounded.pb_check_bounded_x; first [exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws | exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0 | exact W_palib.pb_palib_tfib | exact W_check_bounded.cb_objs_apart_fr] ]]).
  try (only [AMEMCPY_x]: solve [first [ exact (@TopX_INTRIN_memcpy.topx_AMEMCPY_W fx rc) | exact (@TopX_INTRIN_memcpy.topx_AMEMCPY_W rc fx) | exact TopX_INTRIN_memcpy.topx_AMEMCPY_W ]]).
  try (only [CSD_x]: solve [first [ exact (W_check_shape_done.pb_check_shape_done_x TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) W_LLVMFuzzerTestOneInput_top_x.ARX_laws W_palib.pb_palib_tfib) ]]).
  try (only [MO_FR]: solve [first [ exact (fun s f => ReplyKfMeterB.MT_sec_set_fs NSEC KMAX (fun f0 s0 => eq_refl) f s) | intros s f; apply ReplyKfMeterB.MT_sec_set_fs; intros f0 s0; reflexivity ]]).
  try (only [GSHV_x]: solve [first [ eapply TopxImageB2.topx_GSHV_x_B ]]).
  try (only [XE_LIT_S_x]: solve [first [ exact (TopX_XE_LIT.topx_XE_LIT_S_x rc fx) ]]).
  try (only [FPCOV]: solve [first [ exact (fun regs ly S W mem b H => TopxEntry.fr_FP_b_cov regs ly S W mem b H) ]]).
  try (only [LS_pro_oa]: solve [first [ exact (ReplyBTopLsiSec.btlsi_LS_pro_oa_sec rc fx NSEC KMAX ReplyKfCB.KF_KC KC_OK (fun _ => XS) (fun n => Z.le_refl _) REPLYB_RO_LO REPLYB_RO_HI (@LIBROOM_fr CfParams_reply) RLV (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)) ]]).
  try (only [RI_pro]: solve [first [ exact (ReplyRINVB_exit.RI_pro_btop rc fx MT (fun _ => XS)) ]]).
  try (only [LS_pro]: solve [first [ exact (ReplyBTopLsiSec.btlsi_LS_pro_sec rc fx NSEC KMAX ReplyKfCB.KF_KC KC_OK (fun _ => XS) (fun n => Z.le_refl _) REPLYB_RO_LO REPLYB_RO_HI (@LIBROOM_fr CfParams_reply) RLV (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)) ]]).
  try (only [LS_cnt_pro]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_pro rc fx) ]]).
  try (only [LS_exit_budget]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_exit_budget_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_exit_slots]: solve [first [ exact (ReplyRINVB_exit.RI_exit_slots_btop rc fx) ]]).
  try (only [RI_exit_ends]: solve [first [ exact (ReplyRINVB_exit.RI_exit_ends_btop_restated rc fx) ]]).
  try (only [LS_exit_cnt]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_exit_cnt_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_exit_cap]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_exit_cap_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnt_exit]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_exit rc fx _) ]]).
  try (only [FP_SINK]: solve [first [ eapply TopxImageB2.topx_FP_SINK_B ]]).
  try (only [RSRC_x]: solve [first [ exact (TopX_RELAY.topx_RSRC_x_all rc fx) ]]).
  try (only [CNLR_x]: solve [first [ exact (W_check_no_loss_read.pb_check_no_loss_read_x TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) W_LLVMFuzzerTestOneInput_top_x.ARX_laws W_palib.pb_palib_tfib) ]]).
  try (only [RI_drain_skip]: solve [first [ exact (ReplyRINVB_exit.RI_drain_skip_btop rc fx) ]]).
  try (only [RI_drain_step]: solve [first [ exact (ReplyRINVB_exit.RI_drain_step_btop_restated rc fx) ]]).
  try (only [DR_CNT_grow]: solve [first [ exact (ReplyBTopCntDr.btcnt_DR_CNT_grow_kh rc fx) ]]).
  try (only [RI_src]: solve [first [ exact (ReplyRINVBHead.RI_src_b rc fx) ]]).
  try (only [RI_fds]: solve [first [ apply ReplyRINVB_rm_a12.RI_fds_holds | apply ReplyLSBDrainPre.RI_fds_holds ]]).
  try (only [RI_pair]: solve [first [ exact (ReplyRINVBHead.RI_pair_b rc fx) ]]).
  try (only [RI_gone]: solve [first [ intros cx t m H; exact (proj2 (proj2 (proj2 H))) ]]).
  try (only [LS_drain_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_drain_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnl_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_cnl_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_drain_skip]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_drain_skip_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_drain_step]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_drain_step_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [DR_CNT_cnl]: solve [first [ exact ReplyB3TrPeakCnlW8.DR_CNT_cnl_B ]]).
  try (only [LS_cnt_drain]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_drain rc fx _) ]]).
  try (only [RI_close]: solve [first [ exact (ReplyRINVBHead.RI_close_b rc fx) ]]).
  try (only [RI_eintr]: solve [first [ exact (ReplyRINVBHead.RI_eintr_b rc fx) ]]).
  try (only [RI_sendmax]: solve [first [ exact (ReplyRINVBHead.RI_sendmax_b rc fx) ]]).
  try (only [RI_default]: solve [first [ exact (ReplyRINVBHead.RI_default_b rc fx) ]]).
  try (only [LS_close]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_close_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_eintr]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_eintr_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_sendmax]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_sendmax_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_default]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_default_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_add_pre]: solve [first [ exact (@ReplyRINVB_add.RI_add_pre_B rc) ]]).
  try (only [RI_add_open]: solve [first [ exact (@ReplyRINVB_add.RI_add_open_B rc) ]]).
  try (only [RI_add_none]: solve [first [ exact (@ReplyRINVB_add.RI_add_none_B rc) ]]).
  try (only [LS_add_room]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_add_room_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_add_open]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_add_open_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_add_none]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_add_none_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnt_add]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_add rc fx _) ]]).
  try (only [RI_write_skip]: solve [first [ exact (@ReplyRINVB_write.RI_write_skip_b rc) ]]).
  try (only [LS_write_skip]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_write_skip_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_write_push]: solve [first [ exact (@ReplyRINVB_write.RI_write_push_b rc) ]]).
  try (only [LS_write_room]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_write_room_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_write_push]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_write_push_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnt_write]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_write rc fx _) ]]).
  try (only [RRDS_x]: solve [first [ exact (TopX_RELAY.topx_RRDS_x_all rc fx) ]]).
  try (only [RGP_x]: solve [first [ exact W_rg_place.fr_rg_place_b ]]).
  try (only [RI_rm_found]: solve [first [ exact (ReplyRINVB_rm_a12.RI_rm_found_holds (rc := rc)) ]]).
  try (only [RI_rm_rr_pair]: solve [first [ exact (ReplyBTopRiRmRr.btri_RI_rm_rr_pair rc fx) | eapply ReplyBTopRiRmRr.btri_RI_rm_rr_pair ]]).
  try (only [RI_rm_src]: solve [first [ exact (@ReplyRINVB_rmsrc.RI_rm_src_holds fx rc) | exact (@ReplyRINVB_rmsrc.RI_rm_src_holds rc fx) | eapply ReplyRINVB_rmsrc.RI_rm_src_holds ]]).
  try (only [LS_rm_rr_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_rm_rr_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_rm_cnl_pre]: solve [first [ exact (ReplyRINVB_rm_a12.RI_rm_cnl_pre_K14_holds (rc := rc)) ]]).
  try (only [LS_rm_cnl_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_rm_cnl_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_rm_cshe_pre]: solve [first [ exact (ReplyRINVB_rm_a12.RI_rm_cshe_pre_nz_holds (rc := rc)) ]]).
  try (only [LS_rm_cshe_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_rm_cshe_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_rm_csd]: solve [first [ exact (ReplyRINVB_rm_a12.RI_rm_csd_gn_holds (rc := rc)) ]]).
  try (only [LS_rm_sr_pre]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_rm_sr_pre_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [RI_rm_step]: solve [first [ exact (ReplyRINVB_rm_a12.RI_rm_step_holds (rc := rc)) ]]).
  try (only [LS_rm_step]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_rm_step_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnt_remove]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_remove rc fx _) ]]).
  try (only [RM_CNT_cnl]: solve [first [ exact (ReplyBTopCntRm.btcnt_RM_CNT_cnl rc fx) ]]).
  try (only [RM_CNT_cshe]: solve [first [ exact (ReplyBTopCntRm.btcnt_RM_CNT_cshe rc fx) ]]).
  try (only [RM_CNT_sr]: solve [first [ exact (ReplyBTopCntRm.btcnt_RM_CNT_sr rc fx) ]]).
  try (only [ASTRNLEN_x]: solve [first [ exact TopX_RT_B2.topx_ASTRNLEN_B_W | exact (@TopX_RT_B2.topx_ASTRNLEN_B_W fx rc) ]]).
  try (only [CSE_x]: solve [first [ exact TopX_CSE.topx_CSE_W ]]).
  try (only [RI_event_step]: solve [first [ exact (ReplyRINVB_exit.RI_event_step_btop rc fx) ]]).
  try (only [LS_event_malloc]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_event_malloc_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_event_relay]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_event_relay_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_event_free]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_event_free_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_event_step]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_LS_event_step_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [LS_cnt_event]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_event rc fx _) ]]).
  try (only [SNP_x]: solve [first [ exact TopX_SNP.topx_SNP_W ]]).
  try (only [HGOTG_x]: solve [first [ eapply TopxImageB2.topx_HGOTG_x_B ]]).
  try (only [GN_LIT_GES_x]: solve [first [ exact (TopX_LIT.topx_GN_LIT_GES_x rc fx) ]]).
  try (only [GN_LIT_FMT_x]: solve [first [ exact (TopX_LIT.topx_GN_LIT_FMT_x rc fx) ]]).
  try (only [GN_RI_pairs_x]: solve [first [ exact (ReplyRINVB_gone.GN_RI_pairs_x rc fx) ]]).
  try (only [GN_RI_read_x]: solve [first [ exact (ReplyRINVB_gone.GN_RI_read_x rc fx) ]]).
  try (only [GN_RI_step_x]: solve [first [ exact (ReplyRINVB_gone_ls.GN_RI_step_x_sec rc fx NSEC KMAX ReplyKfCB.KF_KC KC_OK) ]]).
  try (only [GN_RI_end_x]: solve [first [ exact (ReplyRINVB_gone_ls.GN_RI_end_x_sec rc fx NSEC KMAX ReplyKfCB.KF_KC KC_OK) ]]).
  try (only [CNT_gone_rig]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_CNT_gone_rig rc fx) ]]).
  try (only [LS_cnt_gone]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_LS_cnt_gone rc fx _) ]]).
  try (only [CNT_gone_step]: solve [first [ exact (ReplyBTopLsiCnt.btlsi_CNT_gone_step rc fx) ]]).
  try (only [GN_LS_rig_x]: solve [first [ solve [unshelve eapply (ReplyBTopLsiSec.btlsi_GN_LS_rig_x_sec rc fx); first [ exact KC_OK | exact YGcfNames.nsec_cf | exact ReplyKfCB.KF_KC | assumption | apply Z.le_refl ]] ]]).
  try (only [R_refl]: solve [first [ exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle'_refl ]]).
  try (only [R_trans]: solve [first [ exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle'_trans ]]).
  try (only [WLE_R]: solve [first [ exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle_wle' ]]).
  try (only [OA_R]: solve [first [ exact (ReplyBTopR_OA.btr_OA_R (ReplyBTopR_SR.btr_SR_R ReplyBTopR_LD.btr_LD_R) rc fx) ]]).
  try (only [LP_R]: solve [first [ exact (ReplyBTopR_LP.btr_LP_R rc fx) ]]).
  try (only [RO_ARx]: solve [first [ intros ly S Hp W mem md H; exact (proj2 (proj2 H)) ]]).
  try (only [AMALLOC_R]: solve [first [ solve [eapply CfRBridgeRulesRhTopB.AMA_x_kf_rh; first [ exact (AM fx rc) | exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] | solve [unshelve eapply CfRBridgeRulesRhTopB.AMA_x_kf_rh; first [ exact (AM fx rc) | exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] ]]).
  try (only [AFREE_R]: solve [first [ solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; first [ exact (AM fx rc) | exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; first [ exact (AM fx rc) | exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] ]]).
  try (only [RE_R]: solve [first [ exact (ReplyBTopR_RE.btr_RE_R rc fx) ]]).
  try (only [DRAIN_R]: solve [first [ exact (ReplyBTopR_DRAIN2.btr_DRAIN_R rc fx) ]]).
  try (only [CNL_dr_R]: solve [first [ exact (ReplyBTopR_DRAIN2.btr_CNL_dr_R ReplyBTopR_LD.btr_LD_R rc fx) ]]).
  try (only [RR_R]: solve [first [ exact (ReplyBTopR_RELAY.btr_RR_R AF ReplyBTopR_DRAIN2.btr_DRAIN_R ReplyBTopR_GSE.btrg_GE_R rc fx) ]]).
  try (only [CNL_rm_R]: solve [first [ exact (ReplyBTopR_RELAY.btr_CNL_rm_R ReplyBTopR_LP.btr_LP_R ReplyBTopR_LD.btr_LDROP_R rc fx) ]]).
  try (only [CSHE_R]: solve [first [ exact (ReplyBTopR_RELAY.btr_CSHE_R ReplyBTopX_HP.btx_HP_x ReplyBTopR_LD.btr_LDROP_R rc fx) ]]).
  try (only [SR_R]: solve [first [ exact (ReplyBTopR_SR.btr_SR_R ReplyBTopR_LD.btr_LD_R rc fx) ]]).
  try (only [RIG_R]: solve [first [ exact (ReplyBTopR_RELAY.btr_RIG_R AF ReplyBTopR_DRAIN2.btr_DRAIN_R ReplyBTopR_GSE.btrg_GE_R rc fx) ]]).
  try (only [GN_CNL_R]: solve [first [ exact (ReplyGoneRB.gn_cnl_R rc fx (ReplyBTopR_RELAY.btr_CNL_rm_R ReplyBTopR_LP.btr_LP_R ReplyBTopR_LD.btr_LDROP_R rc fx)) ]]).
  try (only [GN_CSHE_R]: solve [first [ exact (ReplyGoneRB.gn_cshe_R rc fx (ReplyBTopR_RELAY.btr_CSHE_R ReplyBTopX_HP.btx_HP_x ReplyBTopR_LD.btr_LDROP_R rc fx)) ]]).
  try (only [LXRF_R]: solve [first [ exact (ReplyBTopR_EXIT.btr_LXRF_R AF (ReplyBTopR_GSE.btrg_GSE_R AF) rc fx) ]]).
  try (only [LS_exit_end_R]: solve [first [ exact (ReplyBTopR_EXIT.btr_LS_exit_end_R rc fx) ]]).
  (* the rest are this Section's hypotheses *)
Qed.
(* the two allocator targets are proved: malloc ReplyClosedB.reply_amalloc_target_B, free (primed)
   ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all *)
Theorem replyb_TFIB_B_T : TFIB_B_T.
Proof.
  exact (replyb_TFIB_B_T_composed ReplyClosedB.reply_amalloc_target_B ReplyDeallocInstB.afree_realizes_cf_rh_replyB_all).
Qed.
End btop.
