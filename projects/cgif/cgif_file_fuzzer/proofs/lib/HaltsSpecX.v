(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YO0i YO0f YM02 YM05 YO05 YO09 YO06 YI16 YI17.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import HaltsKitB.
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
Lemma shape_ok_unlink : forall fs A B, shape_ok exits02 A -> shape_ok exits02 B -> shape_ok exits02 (unlink_shape fs A B).
Proof.
  intros fs A B HA HB. unfold unlink_shape. destruct (fs_under fs sink_path); [exact HA|].
  destruct (Fs.fs_lookup fs sink_path); [apply shape_ok_alt2; assumption | exact HA].
Qed.
Lemma shape_ok_openat : forall fs A B, shape_ok exits02 A -> shape_ok exits02 B -> shape_ok exits02 (openat_shape fs A B).
Proof.
  intros fs A B HA HB. unfold openat_shape. destruct (fs_under fs sink_path); [exact HA | apply shape_ok_alt2; assumption].
Qed.
Lemma shape_ok_ff_unl : forall K fs, (forall l, shape_ok exits02 (K l)) -> shape_ok exits02 (ff_unl K fs).
Proof. intros K fs HK. unfold ff_unl, ff_leaf. apply shape_ok_unlink; apply HK. Qed.
Lemma shape_ok_ff_libk : forall pl fs K, (forall l, shape_ok exits02 (K l)) -> shape_ok exits02 (ff_libk pl fs K).
Proof.
  intros pl fs K HK. unfold ff_libk. destruct (ff_cfg (zbytes pl)) as [[[g loops] rest]|]; [| apply HK].
  destruct (g_opens g); [apply shape_ok_openat; apply shape_ok_ff_unl; exact HK | apply shape_ok_ff_unl; exact HK].
Qed.
Lemma shape_ok_lib_iter : forall pl j K, (forall fs, shape_ok exits02 (K fs)) ->
  forall fs, shape_ok exits02 (lib_iter (LS:=ff_lib_shape) pl j K fs).
Proof.
  intros pl j K HK. induction j as [|j IH]; intros fs; cbn.
  - apply HK.
  - apply shape_ok_ff_libk. intros l. apply IH.
Qed.
Lemma shape_ok_run_tail : forall m fs, shape_ok exits02 (run_tail m fs).
Proof. intros [|m] fs; cbn; [apply shape_ok_ex; left; reflexivity | apply shape_ok_wr; apply shape_ok_ex; left; reflexivity]. Qed.
Lemma shape_ok_run_shape : forall pl k fs, shape_ok exits02 (run_shape (LS:=ff_lib_shape) pl k fs).
Proof.
  intros pl [|k] fs; cbn.
  - apply shape_ok_ex. left; reflexivity.
  - apply shape_ok_ff_libk. intros l. apply shape_ok_wr. apply shape_ok_lib_iter. intros fs'. apply shape_ok_run_tail.
Qed.
Lemma shape_ok_leaf_shape : forall data fs r, shape_ok exits02 (leaf_shape data fs r).
Proof.
  intros data fs [d s]. unfold leaf_shape. cbn [fst]. destruct d; try apply shape_ok_diag.
  - destruct (count_mode data); apply shape_ok_ex; [left | right]; reflexivity.
  - apply shape_ok_wr. apply shape_ok_ex. left; reflexivity.
Qed.
Lemma shape_ok_leaf_shapeX : forall data fs r, shape_ok exits02 (leaf_shapeX (LS:=ff_lib_shape) data fs r).
Proof.
  intros data fs [d s]. unfold leaf_shapeX. cbn [fst]. destruct d; try apply (shape_ok_leaf_shape data fs (_, s)).
  apply shape_ok_run_shape.
Qed.
Lemma shape_ok_SPEC_dir : forall p fs, shape_ok exits02 (SPEC_dir p fs).
Proof. intros p fs. unfold SPEC_dir. apply shape_ok_tset. intros [b s]. cbn [fst]. destruct b; apply shape_ok_diag. Qed.
Lemma shape_ok_SPECX_loaded : forall data fs, shape_ok exits02 (SPECX_loaded (LS:=ff_lib_shape) data fs).
Proof. intros data fs. unfold SPECX_loaded. apply shape_ok_tset. intros r. apply shape_ok_leaf_shapeX. Qed.
Theorem SPECX_shape_ok : forall inp, shape_ok exits02 (SPECX (LS:=ff_lib_shape) inp).
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a0 [|p [|x l]]]; try apply shape_ok_diag.
  destruct (classify_open p (in_fs inp)).
  - apply shape_ok_diag.
  - apply shape_ok_alt2; [apply shape_ok_diag | apply shape_ok_SPEC_dir].
  - apply shape_ok_alt2; [apply shape_ok_diag | apply shape_ok_SPECX_loaded].
Qed.
End s.
