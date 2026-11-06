(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.openssl.hashtable.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  WsegFast PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.openssl.hashtable.lib Require Export SumWalkTac RefNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x2d8000 : word) 221184%nat = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.  (* [comment removed for export] *)

Lemma store_ok_data : forall m (a : word) n,
  (0x2d8000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x30e000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x2d8000 : word) a 221184%nat n 0x2d8000 0x30e000);
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
  rdn RSEGS mem (Z_to_bv 64 0x30c1eb) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x30c620) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2d9218) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d9130)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2d9308) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d9220)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2d9128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d9040)) (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x27bb90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xddc28)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2e9410) 1%nat = Some [Z_to_bv 8 0]                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x30bfac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x30bfb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2d8be0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d8be0)) (* [comment removed for export] *)
  /\ file_clean mem 0x2d9130 (Z_to_bv 64 0) (Z_to_bv 64 0).                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
