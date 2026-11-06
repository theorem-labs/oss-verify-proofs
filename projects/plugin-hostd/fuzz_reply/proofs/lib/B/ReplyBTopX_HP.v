(* ReplyBTopX_HP: ReplyBTop's Section hypothesis HP_x (lib/B/ReplyBTop.v, the strict has_prefix contract at top_x's
   relation ARX) as a lemma whose statement is that hypothesis's text.  It is the generic walk
   W_has_prefix_x.pb_has_prefix_x (image B's copy of lib/A/W_has_prefix.v) at B := TfibB, PST := [], ARx := top_x's
   ARX, with top_x's laws ARX_laws and the two site contracts top_x already has at ARX: strlen
   (TopX_RT_B2.topx_ASTRLEN_B_W) and bcmp (TopX_CSE.topx_ABCMP_W), as ReplyBTopR_RELAY.v takes them. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x TopX_RT_B2 TopX_CSE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_has_prefix_x.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.

Lemma btx_HP_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  W_contract_x.hp_spec_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_has_prefix).
Proof.
  intros rc fx.
  eapply W_has_prefix_x.pb_has_prefix_x.
  - exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws.
  - exact TopX_RT_B2.topx_ASTRLEN_B_W.
  - exact TopX_CSE.topx_ABCMP_W.
Qed.
