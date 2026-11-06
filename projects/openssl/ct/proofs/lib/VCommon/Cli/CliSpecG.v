(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import ShapeAlg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Cli Require Import CliVerdict.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition s2b (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition nl : list byte := [Z_to_bv 8 10].

(* [comment removed for export] *)
Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

(* [comment removed for export] *)
Definition t_die (msg : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (W 2 msg) (t_exit (Z_to_bv 64 2) fs).

Definition msg_usage (argv0 : list byte) : list byte :=
  s2b "usage: " ++ argv0 ++ s2b " INPUT" ++ nl.
Definition msg_cannot_open (p : list byte) : list byte :=
  s2b "cli: cannot open " ++ p ++ nl.
Definition msg_read_error (p : list byte) : list byte :=
  s2b "cli: read error on " ++ p ++ nl.
Definition msg_refused : list byte :=
  s2b "cli: input >= 67108864 bytes, refused" ++ nl.
Definition msg_short : list byte :=
  s2b "cli: input shorter than header" ++ nl.
Definition msg_overrun : list byte :=
  s2b "cli: config_len overruns input" ++ nl.

(* [comment removed for export] *)
Definition t_bodyG (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := Z.of_nat (length data) in
  if (MAX_INPUT <=? len)%Z then t_die msg_refused fs
  else if (len <? 6)%Z then t_die msg_short fs
  else if (len <? 6 + cfg_len data)%Z then t_die msg_overrun fs
  else t_nil.

(* [comment removed for export] *)
Definition specG (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; p] =>
      if (4096 <=? length p)%nat then t_die (msg_cannot_open p) fs0          (* [comment removed for export] *)
      else if path_eqb p [] then t_die (msg_cannot_open p) fs0              (* [comment removed for export] *)
      else if path_eqb p dot_path then                                       (* [comment removed for export] *)
        t_alt2 (t_die (msg_cannot_open p) fs0)                               (* [comment removed for export] *)
               (t_die (msg_read_error p) fs0)                                (* [comment removed for export] *)
      else match fs_lookup fs0 p with
           | None => t_die (msg_cannot_open p) fs0                           (* [comment removed for export] *)
           | Some data => t_alt2 (t_die (msg_cannot_open p) fs0)             (* [comment removed for export] *)
                                 (t_bodyG data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.
