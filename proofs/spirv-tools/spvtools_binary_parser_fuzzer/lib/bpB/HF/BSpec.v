(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BShapeAlg.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition s2b (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

Definition exit_code (z : Z) : word := Z_to_bv 64 z.

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

Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.

Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? 6)%nat then t_die msg_short fs
  else
    let b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)) in
    let b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)) in
    let b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0)) in
    let cfg := (b0 + 256 * b1)%Z in
    let config_len := Z.to_nat (cfg mod 32768) in
    if (len <? 6 + config_len)%nat then t_die msg_overrun fs
    else
      let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
      t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs).

Definition t_opened (data : list byte) (fs : Fs.Fs) : TSet := t_body data fs.

Definition t_opened_dir (path : list byte) (fs : Fs.Fs) : TSet :=
  t_die (msg_read_error path) fs.

Definition dot_path : list byte := [Z_to_bv 8 46].

Fixpoint list_byte_eqb (p q : list byte) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && list_byte_eqb p' q'
  | _, _ => false
  end.

Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.
