(* G4.ExDecl: ex_seg_P (FMW_ex_base.v:177), expected's declaration body from EX_P (0x81344) on, composed from the
   sub-segments of FMW_ex_decl_base.v: P -> D1 (spaces) -> D2 (name) -> D3 (spaces after ':') -> D3c (strchr) ->
   D4 (strncmp) -> D5 (plain) -> D6 -> {EX_L, EX_R, EX_T}. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05 YG0v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require
  FMW_ex_decl_p FMW_ex_decl_d1 FMW_ex_decl_d2 FMW_ex_decl_d3 FMW_ex_decl_d3c FMW_ex_decl_d4 FMW_ex_decl_d5
  FMW_ex_decl_d6.

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
