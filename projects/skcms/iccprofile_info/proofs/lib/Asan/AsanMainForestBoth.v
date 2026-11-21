(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the forest is stated once per CONFIG_RSEQ layout (modules R1 and R0, read through TREE_rsb and TREES_rsb), over certificates whose hand-off, join and loop states MainRegen's collector computes in the build. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth
  AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth AsanMainCertErrBoth AsanMainCertP5h0Both AsanMainCertR4Both AsanMainCertR5Both AsanMainCertRSEGh0Both AsanMainCertSROOMh0Both AsanMainCertBIGRh0Both PlanRegen MainRegenBoth.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)
Module R1.
Import AsanMainCertBIGRh0Both.R1.
Import AsanMainCertErrBoth.R1.
Import AsanMainCertP5h0Both.R1.
Import AsanMainCertR4Both.R1.
Import AsanMainCertR5Both.R1.
Import AsanMainCertRSEGh0Both.R1.
Import AsanMainCertSROOMh0Both.R1.

Section WithBig.

  Variable KWT0 : mtree.

  Hypothesis KW_ok0 : mtree_ok 1 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0 = true.

  Variable CPOS : nat -> mtree.

  Hypothesis CPOS_ok : forall h, mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both true) h) ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QCfgLen, 0 + 1, QMAX)]) (CPOS h) = true.

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

Lemma tree_ok_h0_r5 : mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both true) 0) (root_class 5) (TREE 0 5) = true.
Proof. cbv delta [TREE]; cbv beta iota; apply ok_P5_h0; apply mtree_ok_split; [exact ok_A_h0 | apply mtree_ok_split; [exact ok_B_h0 | apply mtree_ok_split; [exact ok_C_h0 | apply mtree_ok_split; [exact (ok_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0) (ok_SROOMS_h0 TREE_BIGR_h0 TREE_BIGR_h0_lvl ok_BIGR_h0)) | apply mtree_ok_class; [vm_compute; reflexivity | exact KW_ok0]]]]]. Qed.

Lemma TREES : forall h ch i, (HS_both true) h = Some ch -> (i < 6)%nat ->
  mtree_ok 1 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both true) h) (root_class i) (TREE h i) = true.
Proof.
  intros h ch i Hh Hi. destruct h as [|h]; [| destruct h; discriminate Hh].
  destruct i as [|[|[|[|[|[|i]]]]]]; [exact tree_ok_h0_r0 | exact tree_ok_h0_r1 | exact tree_ok_h0_r2 | exact tree_ok_h0_r3
      | exact tree_ok_h0_r4 | exact tree_ok_h0_r5 | lia].
Qed.

End WithBig.
End R1.
Module R0.
Import AsanMainCertBIGRh0Both.R0.
Import AsanMainCertErrBoth.R0.
Import AsanMainCertP5h0Both.R0.
Import AsanMainCertR4Both.R0.
Import AsanMainCertR5Both.R0.
Import AsanMainCertRSEGh0Both.R0.
Import AsanMainCertSROOMh0Both.R0.

Section WithBig.

  Variable KWT0 : mtree.

  Hypothesis KW_ok0 : mtree_ok 0 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) KWT0 = true.

  Variable CPOS : nat -> mtree.

  Hypothesis CPOS_ok : forall h, mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both false) h) ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QCfgLen, 0 + 1, QMAX)]) (CPOS h) = true.

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

Lemma tree_ok_h0_r5 : mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both false) 0) (root_class 5) (TREE 0 5) = true.
Proof. cbv delta [TREE]; cbv beta iota; apply ok_P5_h0; apply mtree_ok_split; [exact ok_A_h0 | apply mtree_ok_split; [exact ok_B_h0 | apply mtree_ok_split; [exact ok_C_h0 | apply mtree_ok_split; [exact (ok_RSEG_h0 (TREE_SROOMS_h0 TREE_BIGR_h0) (ok_SROOMS_h0 TREE_BIGR_h0 TREE_BIGR_h0_lvl ok_BIGR_h0)) | apply mtree_ok_class; [vm_compute; reflexivity | exact KW_ok0]]]]]. Qed.

Lemma TREES : forall h ch i, (HS_both false) h = Some ch -> (i < 6)%nat ->
  mtree_ok 0 KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both false) h) (root_class i) (TREE h i) = true.
Proof.
  intros h ch i Hh Hi. destruct h as [|h]; [| destruct h; discriminate Hh].
  destruct i as [|[|[|[|[|[|i]]]]]]; [exact tree_ok_h0_r0 | exact tree_ok_h0_r1 | exact tree_ok_h0_r2 | exact tree_ok_h0_r3
      | exact tree_ok_h0_r4 | exact tree_ok_h0_r5 | lia].
Qed.

End WithBig.
End R0.

(* The forest at the launch's CONFIG_RSEQ layout [rsb]: each layout's trees, with the KW subtree
   [AsanMainCertKWClosedBoth] closes. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWClosedBoth.
Definition TREE_rsb (rsb : bool) : nat -> nat -> mtree :=
  if rsb then R1.TREE AsanMainCertKWClosedBoth.R1.KWT else R0.TREE AsanMainCertKWClosedBoth.R0.KWT.
Lemma TREES_rsb : forall rsb h ch i, HS_both rsb h = Some ch -> (i < 6)%nat ->
  mtree_ok (rseq_z rsb) KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both rsb) h) (root_class i) (TREE_rsb rsb h i) = true.
Proof. intros [|]; [exact (R1.TREES _ AsanMainCertKWClosedBoth.R1.KW_ok) | exact (R0.TREES _ AsanMainCertKWClosedBoth.R0.KW_ok)]. Qed.
