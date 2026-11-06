(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec SpecGen.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require ShapeAlgBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition line_ht (neg : bool) : list byte :=
  if neg then [Z_to_bv 8 45; Z_to_bv 8 49; Z_to_bv 8 10] else [Z_to_bv 8 48; Z_to_bv 8 10].
Fixpoint lines_ht (neg : bool) (calls : nat) : list byte :=
  match calls with O => [] | S c => line_ht neg ++ lines_ht neg c end.

Definition ht_payload_len (data : list byte) : nat := (length data - HDR_MIN - config_len data)%nat.
Definition ht_calls (data : list byte) : nat :=
  match config_len data with O => 1%nat | _ => S (Z.to_nat (byte_at data 2 mod 4)) end.
Definition ht_neg (data : list byte) : bool := (ht_payload_len data <? 11)%nat.
(* [comment removed for export] *)
Definition ht_status (data : list byte) : Z := 0%Z.

Definition t_target_ht (data : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (W 1 (lines_ht (ht_neg data) (ht_calls data))) (t_exit (exit_code (ht_status data)) fs).

(* [comment removed for export] *)
Definition spec_ht : list (list byte) -> Fs.Fs -> TSet := spec_g t_target_ht.

(* [comment removed for export] *)
Lemma t_target_ht_split : forall data fs,
  t_eq (t_emit (W 1 (line_ht (ht_neg data)))
          (t_emit (W 1 (lines_ht (ht_neg data) (pred (ht_calls data)))) (t_exit (exit_code (ht_status data)) fs)))
       (t_target_ht data fs).
Proof.
  intros data fs. unfold t_target_ht.
  assert (E : exists c, ht_calls data = S c) by (unfold ht_calls; destruct (config_len data); eexists; reflexivity).
  destruct E as (c & ->). cbn [pred lines_ht]. unfold W. rewrite map_app.
  apply t_eq_sym. exact (ShapeAlgBase.t_emit_app _ _ _).
Qed.
