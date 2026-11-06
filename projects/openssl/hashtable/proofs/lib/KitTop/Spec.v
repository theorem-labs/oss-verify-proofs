(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg.
From OSSVerify.Proofs.openssl.hashtable.lib Require Export ClaVerdict.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition s2b (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

Definition exit_code (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
Definition t_die (msg : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (W 2 msg) (t_exit (exit_code 2) fs).

Definition msg_usage (argv0 : list byte) : list byte :=
  s2b "usage: " ++ argv0 ++ s2b " INPUT" ++ [Z_to_bv 8 10].
Definition msg_cannot_open (path : list byte) : list byte :=
  s2b "cli: cannot open " ++ path ++ [Z_to_bv 8 10].
Definition msg_read_error (path : list byte) : list byte :=
  s2b "cli: read error on " ++ path ++ [Z_to_bv 8 10].
Definition msg_oom : list byte := s2b "cli: out of memory" ++ [Z_to_bv 8 10].
Definition msg_refused : list byte :=
  s2b "cli: input >= 67108864 bytes, refused" ++ [Z_to_bv 8 10].
Definition msg_short : list byte :=
  s2b "cli: input shorter than header" ++ [Z_to_bv 8 10].
Definition msg_overrun : list byte :=
  s2b "cli: config_len overruns input" ++ [Z_to_bv 8 10].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

(* [comment removed for export] *)
Fixpoint neg_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 45 :: Z_to_bv 8 49 :: Z_to_bv 8 10 :: neg_lines k
  end.

(* [comment removed for export] *)
Definition rc_lines (payload_len calls : nat) : list byte :=
  if (payload_len <? 8)%nat then neg_lines calls else zero_lines calls.

(* [comment removed for export] *)
Definition msg_hardstack : list byte :=
  s2b "Hard stack size limit is too small" ++ [Z_to_bv 8 10].

(* [comment removed for export] *)
Definition t_target (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  let cfg := cfg_word data in
  let clen := config_len data in
  let counting := (32768 <=? cfg)%Z in
  let payload_len := (len - HDR_MIN - clen)%nat in
  let calls := match clen with O => 1%nat | _ => S (Z.to_nat (byte_at data 2 mod 4)) end in
  let status := (if counting then 0 else if (payload_len <? 8)%nat then 1 else 0)%Z in
  let run := t_emit (W 1 (rc_lines payload_len calls)) (t_exit (exit_code status) fs) in
  let body := match payload_len with
              | O => run
              | _ => t_alt2 (t_exit (exit_code (if counting then 0 else 2)) fs) run
              end in
  t_alt2 (t_emit (W 2 msg_hardstack) (t_exit (exit_code 1) fs)) body.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? HDR_MIN)%nat then t_die msg_short fs
  else if (len <? HDR_MIN + config_len data)%nat then t_die msg_overrun fs
  else t_target data fs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t_opened (data : list byte) (fs : Fs.Fs) : TSet :=
  t_body data fs.

(* [comment removed for export] *)
Definition t_opened_dir (path : list byte) (fs : Fs.Fs) : TSet :=
  t_die (msg_read_error path) fs.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match drv_classify argv fs0 with
  | DcUsage => t_die (msg_usage (hd [] argv)) fs0
  | DcNoOpen path => t_die (msg_cannot_open path) fs0           (* [comment removed for export] *)
  | DcDir path => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
  | DcFile path data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_body_pre (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? HDR_MIN)%nat then t_die msg_short fs
  else t_die msg_overrun fs.

Lemma t_body_pre_target : forall data fs,
  body_pre_target data = true -> t_body data fs = t_body_pre data fs.
Proof.
  intros data fs H. unfold t_body, t_body_pre, body_pre_target in *.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [reflexivity|].
  destruct (length data <? HDR_MIN)%nat; [reflexivity|].
  cbn [orb] in H. rewrite H. reflexivity.
Qed.

Lemma t_body_target : forall data fs,
  body_pre_target data = false -> t_body data fs = t_target data fs.
Proof.
  intros data fs H. unfold t_body, body_pre_target in *.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [discriminate H|].
  destruct (length data <? HDR_MIN)%nat; [discriminate H|].
  cbn [orb] in H. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_body_split : forall data fs,
  t_body data fs = if body_pre_target data then t_body_pre data fs else t_target data fs.
Proof.
  intros data fs. destruct (body_pre_target data) eqn:H;
    [apply t_body_pre_target | apply t_body_target]; exact H.
Qed.

(* [comment removed for export] *)
Lemma t_body_refused : forall data fs,
  (MAX_INPUT <= Z.of_nat (length data))%Z -> t_body data fs = t_die msg_refused fs.
Proof.
  intros data fs H. unfold t_body. rewrite (proj2 (Z.leb_le _ _) H). reflexivity.
Qed.

Lemma t_body_short : forall data fs,
  (Z.of_nat (length data) < MAX_INPUT)%Z -> (length data < HDR_MIN)%nat ->
  t_body data fs = t_die msg_short fs.
Proof.
  intros data fs H1 H2. unfold t_body.
  rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Nat.ltb_lt _ _) H2). reflexivity.
Qed.

Lemma t_body_overrun : forall data fs,
  (Z.of_nat (length data) < MAX_INPUT)%Z -> (HDR_MIN <= length data)%nat ->
  (length data < HDR_MIN + config_len data)%nat ->
  t_body data fs = t_die msg_overrun fs.
Proof.
  intros data fs H1 H2 H3. unfold t_body.
  rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Nat.ltb_ge _ _) H2), (proj2 (Nat.ltb_lt _ _) H3).
  reflexivity.
Qed.

Lemma t_body_to_target : forall data fs,
  (Z.of_nat (length data) < MAX_INPUT)%Z -> (HDR_MIN <= length data)%nat ->
  (HDR_MIN + config_len data <= length data)%nat ->
  t_body data fs = t_target data fs.
Proof.
  intros data fs H1 H2 H3. apply t_body_target. apply body_pre_target_false_iff. auto.
Qed.

(* [comment removed for export] *)
Lemma spec_usage : forall argv fs0,
  length argv <> 2%nat -> spec argv fs0 = t_die (msg_usage (hd [] argv)) fs0.
Proof. intros argv fs0 H. unfold spec. rewrite (drv_classify_usage _ _ H). reflexivity. Qed.

Lemma spec_noopen : forall argv fs0 path,
  drv_classify argv fs0 = DcNoOpen path -> spec argv fs0 = t_die (msg_cannot_open path) fs0.
Proof. intros argv fs0 path H. unfold spec. rewrite H. reflexivity. Qed.

Lemma spec_dir : forall argv fs0 path,
  drv_classify argv fs0 = DcDir path ->
  spec argv fs0 = t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0).
Proof. intros argv fs0 path H. unfold spec. rewrite H. reflexivity. Qed.

Lemma spec_file : forall argv fs0 path data,
  drv_classify argv fs0 = DcFile path data ->
  spec argv fs0 = t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0).
Proof. intros argv fs0 path data H. unfold spec. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spec_verdict_true : forall argv fs0,
  drv_verdict argv fs0 = true ->
  spec argv fs0 =
  match drv_classify argv fs0 with
  | DcUsage => t_die (msg_usage (hd [] argv)) fs0
  | DcNoOpen path => t_die (msg_cannot_open path) fs0
  | DcDir path => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
  | DcFile path data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body_pre data fs0)
  end.
Proof.
  intros argv fs0 H. unfold spec, drv_verdict in *.
  destruct (drv_classify argv fs0); try reflexivity.
  unfold t_opened. rewrite (t_body_pre_target _ _ H). reflexivity.
Qed.
