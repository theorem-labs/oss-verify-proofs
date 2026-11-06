(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ShapeAlg Spec BigintSpec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ue_cfg (fdata : list byte) : Z :=
  (bv_unsigned (nth 0 fdata (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 fdata (Z_to_bv 8 0))) mod 32768.

Definition ue_payload (fdata : list byte) : list byte := skipn (Z.to_nat (6 + ue_cfg fdata)) fdata.
Definition ue_header_ok (fdata : list byte) : Prop :=
  Z.of_nat (length fdata) < MAX_INPUT /\ 6 + ue_cfg fdata <= Z.of_nat (length fdata).

Definition ue_reach_ok (P : list byte -> Prop) (inp : ProcInput) : Prop :=
  forall a0s path fdata,
    in_argv inp = [a0s; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
    fs_lookup (in_fs inp) path = Some fdata -> ue_header_ok fdata -> P (ue_payload fdata).

Definition t_body_k (K : TSet) (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? 6)%nat then t_die msg_short fs
  else
    let b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)) in
    let b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)) in
    let cfg := (b0 + 256 * b1)%Z in
    let config_len := Z.to_nat (cfg mod 32768) in
    if (len <? 6 + config_len)%nat then t_die msg_overrun fs
    else K.
Definition spec_k (K : TSet) (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_die (msg_read_error path) fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body_k K data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

Lemma list_byte_eqb_true : forall p q, list_byte_eqb p q = true -> p = q.
Proof.
  induction p as [|a p IH]; intros [|b q]; cbn; try discriminate; [reflexivity|].
  intros H. apply Bool.andb_true_iff in H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1.
  f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma list_byte_eqb_neq : forall p q, p <> q -> list_byte_eqb p q = false.
Proof. intros p q H. destruct (list_byte_eqb p q) eqn:E; [exfalso; apply H; apply list_byte_eqb_true; exact E | reflexivity]. Qed.

