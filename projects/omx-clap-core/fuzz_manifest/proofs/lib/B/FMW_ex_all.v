(* G4, IMAGE B: expected_spec for fm.asan-ubsan (B twin of lib/A/FMW_ex_all.v, 06d82004dc3), every segment of FMW_ex_base.v discharged: only the shared Section hypotheses
   (TfibLib, fm_img_facts) and the callee contracts (strlen, strchr, strncmp, bcmp, plain) are left. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import
FMW_lib FMW_ex_base FMW_ex_ret FMW_ex_top FMW_ex_entry FMW_ex_head FMW_ex_decl FMW_ex_tok.
Import ListNotations.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis BCMP : abcmp_realizes tfibsegs B PC_bcmp.
Hypothesis PLAIN : plain_spec tfibsegs B.

Let SEG_R : ex_seg_R B := ex_seg_R_holds B.
Let SEG_T : ex_seg_T B := ex_seg_T_holds B IMG STRLEN BCMP SEG_R.
Let SEG_P : ex_seg_P B := ex_seg_P_holds B IMG STRCHR STRNCMP PLAIN SEG_R SEG_T.
Let SEG_HEAD : ex_seg_head B := ex_seg_head_holds B IMG STRNCMP SEG_R.
Let SEG_ENTRY : ex_seg_entry B := ex_seg_entry_holds B TL IMG STRLEN STRCHR STRNCMP SEG_R.

Theorem expected_spec_holds : expected_spec tfibsegs B.
Proof. exact (expected_spec_of_segs B SEG_HEAD SEG_P SEG_ENTRY). Qed.
End W.

Print Assumptions expected_spec_holds.
