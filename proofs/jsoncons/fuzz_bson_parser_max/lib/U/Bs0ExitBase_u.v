(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
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
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Export SumWalkTac RefNodes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0xb8000 : word) 208896%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0xb8000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xeb000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0xb8000 : word) a 208896%nat n 0xb8000 0xeb000);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


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
  rdn RSEGS mem (Z_to_bv 64 0xea253) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xea798) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xea788) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xb84d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb83f0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xb83e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8300)).
End FPX_2.
 (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
