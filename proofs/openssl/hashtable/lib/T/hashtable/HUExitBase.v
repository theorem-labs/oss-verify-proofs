(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  WsegFast PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Export SumWalkTac RefNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x31e000 : word) 221184%nat = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.  (* [comment removed for export] *)

Lemma store_ok_data : forall m (a : word) n,
  (0x31e000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x354000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x31e000 : word) a 221184%nat n 0x31e000 0x354000);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x351d7b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x3521b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31eda8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31ecc0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31ee98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31edb0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31ecb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31ebd0)) (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2c1738) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2670)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x32efa0) 1%nat = Some [Z_to_bv 8 0]                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x351b3c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x351b48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x31e5c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31e5c8)) (* [comment removed for export] *)
  /\ file_clean mem 0x31ecc0 (Z_to_bv 64 0) (Z_to_bv 64 0).                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
