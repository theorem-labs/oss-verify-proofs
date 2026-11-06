(* fuzz_reply image B: ReplyBTop's two gone-arm callee rows at route R, GN_CNL_R and GN_CSHE_R, each as ONE lemma at
   EXACTLY ReplyBTop's Context text (MT := ReplyKfMeterB.MT_sec nsec_cf cf_kmax, ARx := top_x's ARX, RP := RP_cf,
   R := wle' tfibsegs RZ_cf), from ReplyBTop's own route-R rows CNL_rm_R / CSHE_R (the callee's R spec at every G that
   gx_ok admits).
   Each slot j < 4 of the gone arm calls check_no_loss / check_shape_ends at its own G, gn_Gs j: one 32-byte range
   inside g_s, so inside top_x's G_fr_c (gx_ok by gx_ok_sub over top_x's GX_ok and G's c_HGs, as top_x's strict
   GN_CNL / GN_CSHE take it). The R row at that G is then GN_CNL_R / GN_CSHE_R's slot j, so the two rows close with
   no premise beyond the two R rows ReplyBTop already has open.
   proves no function (kind: composition of existing specs). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_G YD1u YD1ucf W_palib W_check_bounded W_check_shape_done W_check_no_loss_read ReplyRINVB_add W_rg_place W_relay_src_c ReplyRINVBHead ReplyRINVB_write ReplyRINVB_exit ReplyRINVB_gone ReplyRINVB_rm_a12 ReplyBTopLsiCnt ReplyBTopLsi ReplyB3TrPeakCnlW8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB ReplyRINVB_rmsrc ReplyAllocTargetsB TopX_INTRIN_memcpy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB2 TopxTLFB W_ERRL_x TopX_RELAY TopX_SNP TopX_CSE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB_gone_ls TopxEntry TopX_RT_B2 ReplyClosedB CfRBridgeRulesB CfRStrndup CfRBridgeRulesRhTopB CfRBridgeRulesFreeRhB W_frame_flag_cf ReplyInstFactsB YD1vcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive YGcfNames YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_x W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_top_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep.

Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).

(* every slot's G is inside top_x's G_fr_c, so gx_ok *)
Lemma gn_Gs_gx_ok : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (j : nat), (j < 4)%nat ->
  gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (W_LLVMFuzzerTestOneInput_gone_base.gn_Gs j).
Proof.
intros rc fx j Hj. apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB)); [|exact (W_LLVMFuzzerTestOneInput_top_x.GX_ok)].
intros a Ha. apply (c_HGs TfibB). unfold W_LLVMFuzzerTestOneInput_gone_base.gn_Gs in Ha.
apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha.
clear - Ha Hj. unfold ASRC in *. lia.
Qed.

(* GN_CNL_R from CNL_rm_R (ReplyBTop's two rows) *)
Theorem gn_cnl_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  (∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cnl_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G fr_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_no_loss)) ->
  @W_LLVMFuzzerTestOneInput_gone_base_x.GN_CNL_xR fx rc tfib_sink_head TfibB MT [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) fr_MMAX CfRBridgeRulesB.RP_cf (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
intros rc fx CNL j Hj. exact (CNL _ (gn_Gs_gx_ok rc fx j Hj)).
Qed.

(* GN_CSHE_R from CSHE_R (ReplyBTop's two rows) *)
Theorem gn_cshe_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  (∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cshe_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_shape_ends)) ->
  @W_LLVMFuzzerTestOneInput_gone_base_x.GN_CSHE_xR fx rc tfib_sink_head TfibB MT [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) CfRBridgeRulesB.RP_cf (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
intros rc fx CSHE j Hj. exact (CSHE _ (gn_Gs_gx_ok rc fx j Hj)).
Qed.
