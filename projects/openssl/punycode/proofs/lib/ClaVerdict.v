(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition MAX_INPUT : Z := 67108864.
Definition HDR_MIN : nat := 6%nat.

(* [comment removed for export] *)
Definition byte_at (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_word (data : list byte) : Z := byte_at data 0 + 256 * byte_at data 1.
Definition config_len (data : list byte) : nat := Z.to_nat (cfg_word data mod 32768).

(* [comment removed for export] *)
Definition body_pre_target (data : list byte) : bool :=
  let len := length data in
  (MAX_INPUT <=? Z.of_nat len) || (len <? HDR_MIN)%nat || (len <? HDR_MIN + config_len data)%nat.

(* [comment removed for export] *)
Inductive drv_case : Type :=
| DcUsage                                   (* [comment removed for export] *)
| DcNoOpen (path : list byte)               (* [comment removed for export] *)
| DcDir (path : list byte)                  (* [comment removed for export] *)
| DcFile (path : list byte) (data : list byte).   (* [comment removed for export] *)

Definition drv_classify (argv : list (list byte)) (fs0 : Fs) : drv_case :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then DcNoOpen path
      else if path_eqb path [] then DcNoOpen path
      else if path_eqb path dot_path then DcDir path
      else match fs_lookup fs0 path with
           | None => DcNoOpen path
           | Some data => DcFile path data
           end
  | _ => DcUsage
  end.

Definition drv_verdict (argv : list (list byte)) (fs0 : Fs) : bool :=
  match drv_classify argv fs0 with
  | DcFile _ data => body_pre_target data
  | _ => true
  end.

(* [comment removed for export] *)
Definition cla_verdict (f : FinProcInput) : bool := drv_verdict (fin_argv f) (in_fs (to_proc_input f)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma drv_classify_usage : forall argv fs0,
  length argv <> 2%nat -> drv_classify argv fs0 = DcUsage.
Proof.
  intros [|a [|p [|c r]]] fs0 H; cbn [drv_classify length] in *; try reflexivity. exfalso; apply H; reflexivity.
Qed.

Lemma drv_classify_two : forall argv fs0 c,
  drv_classify argv fs0 = c -> c <> DcUsage -> exists a0 path, argv = [a0; path].
Proof.
  intros [|a [|p [|d r]]] fs0 c H Hc; cbn [drv_classify] in H; try (subst c; exfalso; apply Hc; reflexivity).
  exists a, p. reflexivity.
Qed.

Section TwoArgs.
  Variables (a0 path : list byte) (fs0 : Fs).

  Lemma drv_classify_toolong :
    (4096 <= length path)%nat -> drv_classify [a0; path] fs0 = DcNoOpen path.
  Proof. intros H. cbn [drv_classify]. destruct (Nat.leb_spec 4096 (length path)); [reflexivity|lia]. Qed.

  Lemma drv_classify_empty :
    path = [] -> drv_classify [a0; path] fs0 = DcNoOpen path.
  Proof. intros ->. reflexivity. Qed.

  Lemma drv_classify_dot :
    path = dot_path -> drv_classify [a0; path] fs0 = DcDir path.
  Proof. intros ->. reflexivity. Qed.

  Hypothesis Hlen : (length path < 4096)%nat.
  Hypothesis Hne : path <> [].
  Hypothesis Hnd : path <> dot_path.

  Lemma path_eqb_neq : forall p q : list byte, p <> q -> path_eqb p q = false.
  Proof.
    intros p q H. destruct (path_eqb p q) eqn:E; [|reflexivity].
    exfalso. apply H. apply path_eqb_eq. exact E.
  Qed.

  Lemma drv_classify_absent :
    fs_lookup fs0 path = None -> drv_classify [a0; path] fs0 = DcNoOpen path.
  Proof.
    intros H. cbn [drv_classify]. destruct (Nat.leb_spec 4096 (length path)); [lia|].
    rewrite (path_eqb_neq _ _ Hne), (path_eqb_neq _ _ Hnd), H. reflexivity.
  Qed.

  Lemma drv_classify_file : forall data,
    fs_lookup fs0 path = Some data -> drv_classify [a0; path] fs0 = DcFile path data.
  Proof.
    intros data H. cbn [drv_classify]. destruct (Nat.leb_spec 4096 (length path)); [lia|].
    rewrite (path_eqb_neq _ _ Hne), (path_eqb_neq _ _ Hnd), H. reflexivity.
  Qed.
End TwoArgs.

(* [comment removed for export] *)
Lemma drv_classify_DcFile_inv : forall argv fs0 path data,
  drv_classify argv fs0 = DcFile path data ->
  exists a0, argv = [a0; path] /\ (length path < 4096)%nat /\ path <> [] /\ path <> dot_path
             /\ fs_lookup fs0 path = Some data.
Proof.
  intros [|a [|p [|d r]]] fs0 path data H; cbn [drv_classify] in H; try discriminate.
  destruct (Nat.leb_spec 4096 (length p)); [discriminate|].
  destruct (path_eqb p []) eqn:E1; [discriminate|].
  destruct (path_eqb p dot_path) eqn:E2; [discriminate|].
  destruct (fs_lookup fs0 p) eqn:E3; [|discriminate].
  injection H as <- <-. exists a. repeat split; try assumption.
  - intros ->. rewrite path_eqb_refl in E1. discriminate.
  - intros ->. rewrite path_eqb_refl in E2. discriminate.
Qed.

Lemma drv_classify_DcDir_inv : forall argv fs0 path,
  drv_classify argv fs0 = DcDir path -> exists a0, argv = [a0; path] /\ path = dot_path.
Proof.
  intros [|a [|p [|d r]]] fs0 path H; cbn [drv_classify] in H; try discriminate.
  destruct (Nat.leb_spec 4096 (length p)); [discriminate|].
  destruct (path_eqb p []) eqn:E1; [discriminate|].
  destruct (path_eqb p dot_path) eqn:E2.
  - injection H as <-. exists a. split; [reflexivity|]. apply path_eqb_eq. exact E2.
  - destruct (fs_lookup fs0 p); discriminate.
Qed.

Lemma drv_classify_DcNoOpen_inv : forall argv fs0 path,
  drv_classify argv fs0 = DcNoOpen path ->
  exists a0, argv = [a0; path]
    /\ ((4096 <= length path)%nat
        \/ ((length path < 4096)%nat /\ path = [])
        \/ ((length path < 4096)%nat /\ path <> [] /\ path <> dot_path /\ fs_lookup fs0 path = None)).
Proof.
  intros [|a [|p [|d r]]] fs0 path H; cbn [drv_classify] in H; try discriminate.
  destruct (Nat.leb_spec 4096 (length p)).
  - injection H as <-. exists a. split; [reflexivity|]. left. assumption.
  - destruct (path_eqb p []) eqn:E1.
    + injection H as <-. exists a. split; [reflexivity|]. right; left. split; [assumption|].
      apply path_eqb_eq. exact E1.
    + destruct (path_eqb p dot_path) eqn:E2; [discriminate|].
      destruct (fs_lookup fs0 p) eqn:E3; [discriminate|].
      injection H as <-. exists a. split; [reflexivity|]. right; right.
      repeat split; try assumption.
      * intros ->. rewrite path_eqb_refl in E1. discriminate.
      * intros ->. rewrite path_eqb_refl in E2. discriminate.
Qed.

(* [comment removed for export] *)
Lemma body_pre_target_false_iff : forall data,
  body_pre_target data = false <->
  (Z.of_nat (length data) < MAX_INPUT /\ (HDR_MIN <= length data)%nat
   /\ (HDR_MIN + config_len data <= length data)%nat).
Proof.
  intros data. unfold body_pre_target.
  rewrite !Bool.orb_false_iff, Z.leb_gt, !Nat.ltb_ge. tauto.
Qed.

Lemma body_pre_target_true_iff : forall data,
  body_pre_target data = true <->
  (MAX_INPUT <= Z.of_nat (length data) \/ (length data < HDR_MIN)%nat
   \/ (length data < HDR_MIN + config_len data)%nat).
Proof.
  intros data. unfold body_pre_target.
  rewrite !Bool.orb_true_iff, Z.leb_le, !Nat.ltb_lt. tauto.
Qed.

(* [comment removed for export] *)
Lemma config_len_bound : forall data, Z.of_nat (config_len data) < 32768.
Proof.
  intros data. unfold config_len.
  pose proof (Z.mod_pos_bound (cfg_word data) 32768 ltac:(lia)). rewrite Z2Nat.id; lia.
Qed.

Lemma cfg_word_range : forall data, 0 <= cfg_word data < 65536.
Proof.
  intros data. unfold cfg_word, byte_at.
  pose proof (bv_unsigned_in_range 8 (nth 0 data (Z_to_bv 8 0))) as H0.
  pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as H1.
  change (bv_modulus 8) with 256 in H0, H1. lia.
Qed.

Lemma lor_shiftl8_add : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 ->
  Z.lor b0 (Z.shiftl b1 8) = b0 + 256 * b1.
Proof.
  intros b0 b1 H0 H1.
  assert (Hd : Z.land b0 (Z.shiftl b1 8) = 0).
  { apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8).
    - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
    - rewrite (Z.bits_above_log2 b0); [reflexivity|lia|].
      destruct (Z.eq_dec b0 0) as [->|]; [cbn; lia|].
      apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact Hd.
  rewrite <- Z.add_nocarry_lxor by exact Hd.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma config_len_land : forall data,
  Z.of_nat (config_len data) = Z.land (Z.lor (byte_at data 0) (Z.shiftl (byte_at data 1) 8)) 32767.
Proof.
  intros data. unfold config_len, cfg_word.
  pose proof (bv_unsigned_in_range 8 (nth 0 data (Z_to_bv 8 0))) as H0.
  pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as H1.
  change (bv_modulus 8) with 256 in H0, H1. unfold byte_at.
  rewrite lor_shiftl8_add by lia.
  change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. change (2 ^ 15) with 32768.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cla_verdict_false_iff : forall f,
  cla_verdict f = false <->
  exists path data, drv_classify (fin_argv f) (in_fs (to_proc_input f)) = DcFile path data /\ body_pre_target data = false.
Proof.
  intros f. unfold cla_verdict, drv_verdict.
  destruct (drv_classify (fin_argv f) (in_fs (to_proc_input f))) as [|p|p|p d] eqn:E; split;
    try (intros H; discriminate H); try (intros (path & data & H & _); discriminate H).
  - intros H. exists p, d. auto.
  - intros (path & data & H & H'). injection H as -> ->. exact H'.
Qed.

Lemma cla_verdict_true_cases : forall f,
  cla_verdict f = true <->
  match drv_classify (fin_argv f) (in_fs (to_proc_input f)) with
  | DcFile _ data => body_pre_target data = true
  | _ => True
  end.
Proof.
  intros f. unfold cla_verdict, drv_verdict.
  destruct (drv_classify (fin_argv f) (in_fs (to_proc_input f))); tauto.
Qed.
