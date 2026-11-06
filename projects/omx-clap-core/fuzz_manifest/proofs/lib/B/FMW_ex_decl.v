(* G4.ExDecl, IMAGE B: ex_seg_P (FMW_ex_base.v:191), expected's declaration body from EX_P (0x814cc) on fm.asan-ubsan,
   composed from the sub-segments of FMW_ex_decl_base.v: P -> D1 (spaces) -> D2 (name) -> D3 (spaces after ':') ->
   D3c (strchr) -> D4 (strncmp) -> D5 (plain) -> D6 -> {EX_T, EX_R}, every "continue" through B's shared block
   EX_JUMP / EX_NEXT -> EX_L (FMW_ex_decl_n.v). B twin of lib/A/FMW_ex_decl.v (06d82004dc3). The UBSan guards on these
   paths and the file that refutes each: 0x8151c (d1), 0x81578 and 0x815d4 (d2), 0x81604 and 0x81628 (d3), 0x816b0
   (d5), 0x816a0 (n). ex_seg_R (B's FMW_ex_ret.v) and ex_seg_T (the tok lane) are hypotheses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05 YG0v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require
  FMW_ex_decl_n FMW_ex_decl_p FMW_ex_decl_d1 FMW_ex_decl_d2 FMW_ex_decl_d3 FMW_ex_decl_d3c FMW_ex_decl_d4
  FMW_ex_decl_d5 FMW_ex_decl_d6.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis PLAIN : plain_spec tfibsegs B.
Hypothesis SEG_R : ex_seg_R B.
Hypothesis SEG_T : ex_seg_T B.

Theorem ex_seg_P_holds : ex_seg_P B.
Proof.
  pose proof (FMW_ex_decl_n.decl_N_holds B) as HN.
  pose proof (FMW_ex_decl_n.decl_J_holds B) as HJ.
  assert (H6 : dseg_D6 B) by (eapply FMW_ex_decl_d6.decl_D6_holds; eassumption).
  assert (H5 : dseg_D5 B) by (eapply FMW_ex_decl_d5.decl_D5_holds; eassumption).
  assert (H4 : dseg_D4 B) by (eapply FMW_ex_decl_d4.decl_D4_holds; eassumption).
  assert (H3c : dseg_D3c B) by (eapply FMW_ex_decl_d3c.decl_D3c_holds; eassumption).
  assert (H3 : dseg_D3 B) by (eapply FMW_ex_decl_d3.decl_D3_holds; eassumption).
  assert (H2 : dseg_D2 B) by (eapply FMW_ex_decl_d2.decl_D2_holds; eassumption).
  assert (H1 : dseg_D1 B) by (eapply FMW_ex_decl_d1.decl_D1_holds; eassumption).
  eapply FMW_ex_decl_p.decl_P_holds; eassumption.
Qed.
End W.

Check ex_seg_P_holds.
Print Assumptions ex_seg_P_holds.
