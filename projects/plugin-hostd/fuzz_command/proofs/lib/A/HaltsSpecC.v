(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/HaltsSpecX.v for fuzz_grant: the library shape is grant_shape (each call returns 0 and writes nothing), so cgif's lemmas for its file-writing shape are replaced by the one-line case of grant_shape; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/HaltsSpecG.v for fuzz_command, whose library shape is cmd_shape (ag_shape checksum_shape: each call returns 0 and writes nothing); names and module paths changed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YO0i YO0f YM02 YM05 YO05 YO09 YO06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import HaltsKitB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdShape.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Definition exits02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma in02_0 : In (Z_to_bv 64 0) exits02. Proof. left. reflexivity. Qed.
Lemma in02_2 : In (Z_to_bv 64 2) exits02. Proof. right. left. reflexivity. Qed.
Lemma shape_ok_ex : forall z fs, z = 0 \/ z = 2 -> shape_ok exits02 (ex z fs).
Proof. intros z fs [-> | ->]; unfold ex; apply shape_ok_exit; [apply in02_0 | apply in02_2]. Qed.
Lemma shape_ok_wr : forall ch bs T, shape_ok exits02 T -> shape_ok exits02 (wr ch bs T).
Proof. intros ch bs T H. unfold wr. apply shape_ok_emit; [apply trace_ok_writes | exact H]. Qed.
Lemma shape_ok_diag : forall msg fs, shape_ok exits02 (diag msg fs).
Proof. intros msg fs. unfold diag. apply shape_ok_wr. apply shape_ok_ex. right. reflexivity. Qed.
Lemma shape_ok_lib_iter : forall pl j K, (forall fs, shape_ok exits02 (K fs)) ->
  forall fs, shape_ok exits02 (lib_iter (LS:=cmd_shape) pl j K fs).
Proof.
  intros pl j K HK. induction j as [|j IH]; intros fs; cbn.
  - apply HK.
  - apply IH.
Qed.
Lemma shape_ok_run_tail : forall m fs, shape_ok exits02 (run_tail m fs).
Proof. intros [|m] fs; cbn; [apply shape_ok_ex; left; reflexivity | apply shape_ok_wr; apply shape_ok_ex; left; reflexivity]. Qed.
Lemma shape_ok_run_shape : forall pl k fs, shape_ok exits02 (run_shape (LS:=cmd_shape) pl k fs).
Proof.
  intros pl [|k] fs; cbn.
  - apply shape_ok_ex. left; reflexivity.
  - apply shape_ok_wr. apply shape_ok_lib_iter. intros fs'. apply shape_ok_run_tail.
Qed.
Lemma shape_ok_leaf_shape : forall data fs r, shape_ok exits02 (leaf_shape data fs r).
Proof.
  intros data fs [d s]. unfold leaf_shape. cbn [fst]. destruct d; try apply shape_ok_diag.
  - destruct (count_mode data); apply shape_ok_ex; [left | right]; reflexivity.
  - apply shape_ok_wr. apply shape_ok_ex. left; reflexivity.
Qed.
Lemma shape_ok_leaf_shapeX : forall data fs r, shape_ok exits02 (leaf_shapeX (LS:=cmd_shape) data fs r).
Proof.
  intros data fs [d s]. unfold leaf_shapeX. cbn [fst]. destruct d; try apply (shape_ok_leaf_shape data fs (_, s)).
  apply shape_ok_run_shape.
Qed.
Lemma shape_ok_SPEC_dir : forall p fs, shape_ok exits02 (SPEC_dir p fs).
Proof. intros p fs. unfold SPEC_dir. apply shape_ok_tset. intros [b s]. cbn [fst]. destruct b; apply shape_ok_diag. Qed.
Lemma shape_ok_SPECX_loaded : forall data fs, shape_ok exits02 (SPECX_loaded (LS:=cmd_shape) data fs).
Proof. intros data fs. unfold SPECX_loaded. apply shape_ok_tset. intros r. apply shape_ok_leaf_shapeX. Qed.
Theorem SPECX_shape_ok : forall inp, shape_ok exits02 (SPECX (LS:=cmd_shape) inp).
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a0 [|p [|x l]]]; try apply shape_ok_diag.
  destruct (classify_open p (in_fs inp)).
  - apply shape_ok_diag.
  - apply shape_ok_alt2; [apply shape_ok_diag | apply shape_ok_SPEC_dir].
  - apply shape_ok_alt2; [apply shape_ok_diag | apply shape_ok_SPECX_loaded].
Qed.
End s.
