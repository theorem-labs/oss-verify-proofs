(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
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
Definition msg_refused : list byte :=
  s2b "cli: input >= 67108864 bytes, refused" ++ [Z_to_bv 8 10].
Definition msg_short : list byte :=
  s2b "cli: input shorter than header" ++ [Z_to_bv 8 10].
Definition msg_overrun : list byte :=
  s2b "cli: config_len overruns input" ++ [Z_to_bv 8 10].

(* [comment removed for export] *)
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.
Definition HDR_MIN : nat := 6%nat.

(* [comment removed for export] *)
Definition cfg_word (data : list byte) : Z :=
  (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z.
Definition config_len (data : list byte) : nat := Z.to_nat (cfg_word data mod 32768).
Definition counting (data : list byte) : bool := (32768 <=? cfg_word data)%Z.
(* [comment removed for export] *)
Definition calls_of (data : list byte) : nat :=
  match config_len data with
  | O => 1%nat
  | _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4))
  end.
Definition payload_len (data : list byte) : nat := (length data - HDR_MIN - config_len data)%nat.

(* [comment removed for export] *)
Definition lib_lines (data : list byte) : list byte := zero_lines (calls_of data).
Definition lib_status (data : list byte) : Z := 0%Z.

(* [comment removed for export] *)
Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? HDR_MIN)%nat then t_die msg_short fs
  else if (len <? HDR_MIN + config_len data)%nat then t_die msg_overrun fs
  else t_emit (W 1 (lib_lines data)) (t_exit (exit_code (lib_status data)) fs).

(* [comment removed for export] *)
Definition t_opened (data : list byte) (fs : Fs.Fs) : TSet := t_body data fs.

(* [comment removed for export] *)
Definition t_opened_dir (path : list byte) (fs : Fs.Fs) : TSet :=
  t_die (msg_read_error path) fs.

Definition dot_path : list byte := [Z_to_bv 8 46].

Fixpoint list_byte_eqb (p q : list byte) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && list_byte_eqb p' q'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0      (* [comment removed for export] *)
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0   (* [comment removed for export] *)
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0                     (* [comment removed for export] *)
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma list_byte_eqb_refl : forall p, list_byte_eqb p p = true.
Proof. induction p as [|a p IH]; [reflexivity|]. cbn. rewrite IH. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true -> p = q.
Proof.
  induction p as [|a p IH]; intros [|b q] H; try reflexivity; try discriminate.
  cbn in H. apply andb_prop in H as [H1 H2]. f_equal; [|apply IH; exact H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq. exact H1.
Qed.

(* [comment removed for export] *)
Example t_body_ex1 : forall fs,
  t_body (map (Z_to_bv 8) [0; 0; 51; 0; 0; 0]%Z) fs = t_emit (W 1 (zero_lines 1)) (t_exit (exit_code 0) fs).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Example t_body_ex2 : forall fs,
  t_body (map (Z_to_bv 8) [1; 0; 51; 0; 0; 0; 0]%Z) fs = t_emit (W 1 (zero_lines 4)) (t_exit (exit_code 0) fs).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Example t_body_ex3 : forall fs,
  t_body (map (Z_to_bv 8) [2; 0; 51; 0; 0; 0; 0]%Z) fs = t_die msg_overrun fs.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Example t_body_ex4 : forall fs, t_body (map (Z_to_bv 8) [2; 0; 51; 0; 0]%Z) fs = t_die msg_short fs.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Example t_body_ex5 : forall fs,
  t_body (map (Z_to_bv 8) [0; 128; 51; 0; 0; 0; 7]%Z) fs = t_emit (W 1 (zero_lines 1)) (t_exit (exit_code 0) fs).
Proof. reflexivity. Qed.
