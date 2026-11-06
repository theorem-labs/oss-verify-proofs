(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInv SjS1Lem SjS1Bytes SjS1Ghost SjVCPre SjS1VC SjS1Pre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP Require Import S1P_defs S1G_vcs S1G_ok_a S1G_ok_b S1G_ok_c S1G_ok_d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Theorem S1G_GV_ok : forall d, Forall (SG.vc_holds SG (s1_gp d)) S1G_GV.
Proof.
  intros d. unfold S1G_GV.
  repeat apply Forall_cons; try apply Forall_nil.
  - exact (S1G_vc_0_ok d).
  - exact (S1G_vc_1_ok d).
  - exact (S1G_vc_2_ok d).
  - exact (S1G_vc_3_ok d).
  - exact (S1G_vc_4_ok d).
  - exact (S1G_vc_5_ok d).
  - exact (S1G_vc_6_ok d).
  - exact (S1G_vc_7_ok d).
  - exact (S1G_vc_8_ok d).
  - exact (S1G_vc_9_ok d).
  - exact (S1G_vc_10_ok d).
  - exact (S1G_vc_11_ok d).
  - exact (S1G_vc_12_ok d).
  - exact (S1G_vc_13_ok d).
  - exact (S1G_vc_14_ok d).
  - exact (S1G_vc_15_ok d).
  - exact (S1G_vc_16_ok d).
  - exact (S1G_vc_17_ok d).
  - exact (S1G_vc_18_ok d).
  - exact (S1G_vc_19_ok d).
  - exact (S1G_vc_20_ok d).
  - exact (S1G_vc_21_ok d).
  - exact (S1G_vc_22_ok d).
  - exact (S1G_vc_23_ok d).
  - exact (S1G_vc_24_ok d).
  - exact (S1G_vc_25_ok d).
  - exact (S1G_vc_26_ok d).
  - exact (S1G_vc_27_ok d).
  - exact (S1G_vc_28_ok d).
  - exact (S1G_vc_29_ok d).
  - exact (S1G_vc_30_ok d).
  - exact (S1G_vc_31_ok d).
  - exact (S1G_vc_32_ok d).
  - exact (S1G_vc_33_ok d).
  - exact (S1G_vc_34_ok d).
  - exact (S1G_vc_35_ok d).
  - exact (S1G_vc_36_ok d).
  - exact (S1G_vc_37_ok d).
  - exact (S1G_vc_38_ok d).
  - exact (S1G_vc_39_ok d).
  - exact (S1G_vc_40_ok d).
  - exact (S1G_vc_41_ok d).
  - exact (S1G_vc_42_ok d).
  - exact (S1G_vc_43_ok d).
  - exact (S1G_vc_44_ok d).
  - exact (S1G_vc_45_ok d).
  - exact (S1G_vc_46_ok d).
  - exact (S1G_vc_47_ok d).
  - exact (S1G_vc_48_ok d).
  - exact (S1G_vc_49_ok d).
  - exact (S1G_vc_50_ok d).
  - exact (S1G_vc_51_ok d).
  - exact (S1G_vc_52_ok d).
  - exact (S1G_vc_53_ok d).
  - exact (S1G_vc_54_ok d).
  - exact (S1G_vc_55_ok d).
  - exact (S1G_vc_56_ok d).
  - exact (S1G_vc_57_ok d).
  - exact (S1G_vc_58_ok d).
  - exact (S1G_vc_59_ok d).
  - exact (S1G_vc_60_ok d).
  - exact (S1G_vc_61_ok d).
  - exact (S1G_vc_62_ok d).
  - exact (S1G_vc_63_ok d).
  - exact (S1G_vc_64_ok d).
Qed.
