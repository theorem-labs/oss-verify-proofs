(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition MAX_INPUT : Z := 67108864%Z.

(* [comment removed for export] *)
Definition cfg_word (data : list byte) : Z :=
  (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z.
Definition cfg_len (data : list byte) : Z := (cfg_word data mod 32768)%Z.

(* [comment removed for export] *)
Definition V_data (data : list byte) : bool :=
  (Z.of_nat (length data) <? 6 + cfg_len data)%Z || (MAX_INPUT <=? Z.of_nat (length data))%Z.

Definition V (argv : list (list byte)) (fs : Fs) : bool :=
  match argv with
  | [_; p] =>
      (4096 <=? length p)%nat || path_eqb p [] || path_eqb p dot_path ||
      match fs_lookup fs p with
      | None => true
      | Some data => V_data data
      end
  | _ => true
  end.
