(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition s2b (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

Definition exit_code (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
Definition t_die (msg : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (W 2 msg) (t_exit (exit_code 2) fs).

Definition nl : list byte := [Z_to_bv 8 10].
Definition msg_usage (argv0 : list byte) : list byte := s2b "usage: " ++ argv0 ++ s2b " INPUT" ++ nl.
Definition msg_cannot_open (path : list byte) : list byte := s2b "cli: cannot open " ++ path ++ nl.
Definition msg_read_error (path : list byte) : list byte := s2b "cli: read error on " ++ path ++ nl.
Definition msg_refused : list byte := s2b "cli: input >= 67108864 bytes, refused" ++ nl.
Definition msg_short : list byte := s2b "cli: input shorter than header" ++ nl.
Definition msg_overrun : list byte := s2b "cli: config_len overruns input" ++ nl.

(* [comment removed for export] *)
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.

(* [comment removed for export] *)
Definition cfg_word (data : list byte) : Z :=
  (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z.
Definition config_len (data : list byte) : nat := Z.to_nat (cfg_word data mod 32768).
Definition n_calls (data : list byte) : nat :=
  match config_len data with
  | O => 1%nat
  | _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4))
  end.

(* [comment removed for export] *)
Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? 6)%nat then t_die msg_short fs
  else if (len <? 6 + config_len data)%nat then t_die msg_overrun fs
  else t_emit (W 1 (zero_lines (n_calls data))) (t_exit (exit_code 0) fs).

(* [comment removed for export] *)
Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0          (* [comment removed for export] *)
      else if path_eqb path [] then t_die (msg_cannot_open path) fs0              (* [comment removed for export] *)
      else if path_is_dirref path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_die (msg_read_error path) fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0                              (* [comment removed for export] *)
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.
