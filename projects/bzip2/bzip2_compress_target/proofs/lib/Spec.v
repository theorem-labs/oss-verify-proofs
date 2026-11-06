(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ShapeAlg.
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
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dot_path : list byte := [Z_to_bv 8 46].

Fixpoint list_byte_eqb (p q : list byte) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && list_byte_eqb p' q'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
