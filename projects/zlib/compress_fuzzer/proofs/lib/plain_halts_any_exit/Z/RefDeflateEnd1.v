(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition dstatus_ok (st : Z) : Prop :=
  st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.

Definition pcT (k : nat) : Z := nth k [0x17d50; 0x17d68; 0x17d80; 0x17d98; 0x17db0] 0.
Definition offT (k : nat) : Z := nth k [16; 120; 112; 96] 0.
Definition raT (k : nat) : Z := nth k [0x17d60; 0x17d78; 0x17d90; 0x17da8] 0.

Section Entry.

Local Ltac stcase :=
  lazymatch goal with
  | |- _ mod _ = 0 => subst; vm_compute; reflexivity
  | |- _ mod _ <> 0 => subst; vm_compute; discriminate
  | |- ~ (_ mod _ = 0) => subst; vm_compute; discriminate
  | |- 113 < _ => lia
  | |- ~ (113 < _) => lia
  | |- 68 >= _ => lia
  | |- ~ (68 >= _) => lia
  end.
End Entry.

Section Tests.
End Tests.

Section Fin.

Definition dend_rc (st : Z) : Z := if st =? BUSY_STATE then Z_DATA_ERROR else Z_OK.
End Fin.
