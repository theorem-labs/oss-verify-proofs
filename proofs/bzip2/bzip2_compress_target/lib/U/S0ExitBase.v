(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Export SumWalkTac RefNodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0WsegData.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x33000 : word) 208896%nat = true.
Proof. exact (wseg_fast_sound _ _ _ S0WsegData.wseg_fast_data). Qed.  (* [comment removed for export] *)

Lemma store_ok_data : forall m (a : word) n,
  (0x33000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x66000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x33000 : word) a 208896%nat n 0x33000 0x66000);
    [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
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
  rdn RSEGS mem (Z_to_bv 64 0x64473) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x64898) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x33f88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33ea0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x34078) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33f90)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x33e98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33db0))  (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33ea0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33ea0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33ea0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33ea0 + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33ea0 + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
