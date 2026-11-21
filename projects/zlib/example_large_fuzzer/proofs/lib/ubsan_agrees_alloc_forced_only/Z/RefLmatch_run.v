(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable ds : deflate_state.
Local Notation w := (ds_window ds).
Local Notation pv := (ds_prev ds).
Local Notation WL := (arr_len (ds_window ds)).
Local Notation PL := (arr_len (ds_prev ds)).
Local Notation strstart := (ds_strstart ds).
Local Notation strend := (ds_strstart ds + 258).
Hypothesis Hwb : forall i, 0 <= i < WL -> 0 <= arr_get w i < 256.
Hypothesis Hpb : forall i, 0 <= i < PL -> 0 <= arr_get pv i < 65536.
Hypothesis Hsp : 32 <= sp /\ sp <= 2 ^ 63.
(* [comment removed for export] *)
Hypothesis Hstr : 0 <= strstart /\ strstart + 258 < WL /\ WL <= 2 ^ 31.
Hypothesis Hwm : 0 <= ds_w_mask ds < PL /\ PL <= 2 ^ 31.
Hypothesis Hpl : 1 <= ds_prev_length ds <= 258.
Hypothesis Hnice : 0 <= ds_nice_match ds <= 258.
Hypothesis Hlook : 0 <= ds_lookahead ds < 2 ^ 31.
Hypothesis Hgood : 0 <= ds_good_match ds < 2 ^ 31.
Hypothesis Hchain : 0 <= ds_max_chain_length ds < 2 ^ 31.
Hypothesis Hwsz : 262 <= ds_w_size ds < 2 ^ 31.

(* [comment removed for export] *)
Definition LF : franges := [(sp - 32, 32); (S + 176, 4)].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Let F1 : nat -> Z -> Z := fun f => match f with 0%nat => wb w | _ => pb pv end.
Let HF0 : forall x, 0 <= F1 0%nat x < 256 := fun x => wb_range w x.
Let HF1 : forall x, 0 <= F1 1%nat x < 65536 := fun x => pb_range pv x.

Let wb_eqI : forall i j, arr_get w i = arr_get w j -> wb w i = wb w j := wb_eqI w.
Let wb_neI : forall i j, 0 <= i < WL -> 0 <= j < WL -> arr_get w i <> arr_get w j -> wb w i <> wb w j
  := wb_neI w Hwb.
Let wb_get : forall i, 0 <= i < WL -> wb w i = arr_get w i := wb_get w Hwb.
Let pb_get : forall i, 0 <= i < PL -> pb pv i = arr_get pv i := pb_get pv Hpb.

Local Ltac norm_idx :=
  repeat match goal with
  | |- context [?x + Zpos ?a + Zpos ?b] =>
      let c := eval vm_compute in (Zpos a + Zpos b) in
      replace (x + Zpos a + Zpos b) with (x + c) by lia
  end.

End Walk.

(* [comment removed for export] *)
