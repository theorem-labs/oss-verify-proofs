(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ShapeAlg Spec.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition t_body04 (data : list byte) (fs : Fs.Fs) : TSet :=
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

(* [comment removed for export] *)
Definition t_opened04 (data : list byte) (fs : Fs.Fs) : TSet := t_body04 data fs.

(* [comment removed for export] *)
Definition t_opened_dir04 (path : list byte) (fs : Fs.Fs) : TSet := t_die (msg_read_error path) fs.

(* [comment removed for export] *)
Definition spec04 (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0      (* [comment removed for export] *)
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0   (* [comment removed for export] *)
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir04 path fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0                     (* [comment removed for export] *)
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened04 data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
