(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Export SumWalkTac RefNodes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Reloc RelocImg.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require ExitBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23Reloc V23RelocImg.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Export AgentNodesG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23ExitBase () := "C6ARocqVerifyHarness?AgentSubmission6Common4Musl8ExitBase=store_ok_dataC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_data".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma store_ok_data : forall m (a : word) n,
  (0x127000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x159000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23ExitBase ()) ["VP2"] "p;2g0000j20Tg0017g0022'0o"). Qed.
End VP2.

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
  rdn RSEGS mem (Z_to_bv 64 0x158463) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x1588a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x158890) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x127e98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x127db0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x127da8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x127cc0)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
