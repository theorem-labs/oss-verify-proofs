(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec HeapIface LibIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10ExitAx_u Pm10DrvLibL_u Pm10ExitHandlers_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition REG_J : Z * Z := (0x63404, 0xc4aa8)%Z.
Definition REG_C : Z * Z := (0x63404, 0xc4aa0)%Z.

Definition lib_hs_ok (hs : list (Z * Z)) : Prop :=
  hs = [] \/ hs = [REG_J] \/ hs = [REG_C] \/ hs = [REG_J; REG_C] \/ hs = [REG_C; REG_J].

Lemma lib_hs_handlers : forall hs, lib_hs_ok hs ->
  Z.of_nat (length hs) <= 31 /\ (forall fx : PropExec.FPState, Forall (fun h => @handler_ok fx (fun _ => True) (fst h) (snd h)) hs).
Proof.
  intros hs H. unfold lib_hs_ok, REG_J, REG_C in H.
  destruct H as [->|[->|[->|[->| ->]]]]; (split; [cbn; lia|]); intros fx;
    repeat (constructor; [cbn [fst snd]; apply handler_ret; lia|]); constructor.
Qed.

Lemma lib_exit_ok_of_cells_c : forall LSt : lib_statics,
  (forall (g : ls_state LSt) (M : word -> option byte), ls_ok LSt g M ->
     exists hs, lib_hs_ok hs /\ atexit_state M (DRV_ATEXIT :: hs)) ->
  lib_exit_ok LSt.
Proof.
  intros LSt H g M OK. destruct (H g M OK) as (hs & Hhs & A).
  destruct (lib_hs_handlers hs Hhs) as (Hlen & Hh).
  exists hs. split; [exact Hlen|]. split; [exact Hh | exact A].
Qed.

Lemma lib_hs_ok_j : lib_hs_ok [REG_J].
Proof. unfold lib_hs_ok. right; left; reflexivity. Qed.
