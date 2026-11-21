(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the forest is stated once per CONFIG_RSEQ layout (modules R1 and R0, read through TREE_rsb and TREES_rsb), over certificates whose hand-off, join and loop states MainRegen's collector computes in the build. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanMainLib AsanMainDefs AsanMainTree
  AsanMainCertLib AsanMainItab StartupHSAsan AsanMainCertErr AsanMainCertP5h0 AsanMainCertR4 AsanMainCertR5 AsanMainCertRSEGh0 AsanMainCertBIGRh0 AsanMainCertSROOMh0 PlanRegen MainRegen.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)
Module R1.
Import AsanMainCertBIGRh0.R1.
Import AsanMainCertErr.R1.
Import AsanMainCertP5h0.R1.
Import AsanMainCertR4.R1.
Import AsanMainCertR5.R1.
Import AsanMainCertRSEGh0.R1.
Import AsanMainCertSROOMh0.R1.

Section WithBig.

  Variable KWT0 : mtree.

  Hypothesis KW_ok0 : mtree_ok 1 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0 = true.

  Variable CPOS : nat -> mtree.

  Hypothesis CPOS_ok : forall h, mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan true) h) ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QCfgLen, 0 + 1, QMAX)]) (CPOS h) = true.

Definition TREE (h i : nat) : mtree :=
  match h, i with
  | 0%nat, 0%nat => TREE_h0_r0
  | 0%nat, 1%nat => TREE_h0_r1
  | 0%nat, 2%nat => TREE_h0_r2
  | 0%nat, 3%nat => TREE_h0_r3
  | 0%nat, 4%nat => TREE_h0_r4
  | 0%nat, 5%nat => (TREE_P5_h0 (MSplit QFlen 0 TREE_A_h0 (MSplit QFlen 5 TREE_B_h0 (MSplit QRoom (-1) TREE_C_h0 (MSplit QFlen 65535 (TREE_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0)) (MClass ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0))))))
  | _, _ => MEmpty 0
  end.

Lemma tree_ok_h0_r5 : mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan true) 0) (root_class 5) (TREE 0 5) = true.
Proof. cbv delta [TREE]; cbv beta iota; apply ok_P5_h0; apply mtree_ok_split; [exact ok_A_h0 | apply mtree_ok_split; [exact ok_B_h0 | apply mtree_ok_split; [exact ok_C_h0 | apply mtree_ok_split; [exact (ok_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0) (ok_SROOMS_h0 TREE_BIGR_h0 TREE_BIGR_h0_lvl ok_BIGR_h0)) | apply mtree_ok_class; [vm_compute; reflexivity | exact KW_ok0]]]]]. Qed.

Lemma TREES : forall h ch i, (HS_asan true) h = Some ch -> (i < 6)%nat ->
  mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan true) h) (root_class i) (TREE h i) = true.
Proof.
  intros h ch i Hh Hi. destruct h as [|h]; [| destruct h; discriminate Hh].
  destruct i as [|[|[|[|[|[|i]]]]]]; [exact tree_ok_h0_r0 | exact tree_ok_h0_r1 | exact tree_ok_h0_r2 | exact tree_ok_h0_r3
      | exact tree_ok_h0_r4 | exact tree_ok_h0_r5 | lia].
Qed.

End WithBig.
End R1.
Module R0.
Import AsanMainCertBIGRh0.R0.
Import AsanMainCertErr.R0.
Import AsanMainCertP5h0.R0.
Import AsanMainCertR4.R0.
Import AsanMainCertR5.R0.
Import AsanMainCertRSEGh0.R0.
Import AsanMainCertSROOMh0.R0.

Section WithBig.

  Variable KWT0 : mtree.

  Hypothesis KW_ok0 : mtree_ok 0 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0 = true.

  Variable CPOS : nat -> mtree.

  Hypothesis CPOS_ok : forall h, mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan false) h) ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QCfgLen, 0 + 1, QMAX)]) (CPOS h) = true.

Definition TREE (h i : nat) : mtree :=
  match h, i with
  | 0%nat, 0%nat => TREE_h0_r0
  | 0%nat, 1%nat => TREE_h0_r1
  | 0%nat, 2%nat => TREE_h0_r2
  | 0%nat, 3%nat => TREE_h0_r3
  | 0%nat, 4%nat => TREE_h0_r4
  | 0%nat, 5%nat => (TREE_P5_h0 (MSplit QFlen 0 TREE_A_h0 (MSplit QFlen 5 TREE_B_h0 (MSplit QRoom (-1) TREE_C_h0 (MSplit QFlen 65535 (TREE_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0)) (MClass ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0))))))
  | _, _ => MEmpty 0
  end.

Lemma tree_ok_h0_r5 : mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan false) 0) (root_class 5) (TREE 0 5) = true.
Proof. cbv delta [TREE]; cbv beta iota; apply ok_P5_h0; apply mtree_ok_split; [exact ok_A_h0 | apply mtree_ok_split; [exact ok_B_h0 | apply mtree_ok_split; [exact ok_C_h0 | apply mtree_ok_split; [exact (ok_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0) (ok_SROOMS_h0 TREE_BIGR_h0 TREE_BIGR_h0_lvl ok_BIGR_h0)) | apply mtree_ok_class; [vm_compute; reflexivity | exact KW_ok0]]]]]. Qed.

Lemma TREES : forall h ch i, (HS_asan false) h = Some ch -> (i < 6)%nat ->
  mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan false) h) (root_class i) (TREE h i) = true.
Proof.
  intros h ch i Hh Hi. destruct h as [|h]; [| destruct h; discriminate Hh].
  destruct i as [|[|[|[|[|[|i]]]]]]; [exact tree_ok_h0_r0 | exact tree_ok_h0_r1 | exact tree_ok_h0_r2 | exact tree_ok_h0_r3
      | exact tree_ok_h0_r4 | exact tree_ok_h0_r5 | lia].
Qed.

End WithBig.
End R0.

(* The forest at the launch's CONFIG_RSEQ layout [rsb]: each layout's trees, with the KW subtree
   [AsanMainCertKWClosed] closes. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWClosed.
Definition TREE_rsb (rsb : bool) : nat -> nat -> mtree :=
  if rsb then R1.TREE AsanMainCertKWClosed.R1.KWT else R0.TREE AsanMainCertKWClosed.R0.KWT.
Lemma TREES_rsb : forall rsb h ch i, HS_asan rsb h = Some ch -> (i < 6)%nat ->
  mtree_ok (rseq_z rsb) KCm BFUELm FUELm ITmD 0 0 (HSA (HS_asan rsb) h) (root_class i) (TREE_rsb rsb h i) = true.
Proof. intros [|]; [exact (R1.TREES _ AsanMainCertKWClosed.R1.KW_ok) | exact (R0.TREES _ AsanMainCertKWClosed.R0.KW_ok)]. Qed.
