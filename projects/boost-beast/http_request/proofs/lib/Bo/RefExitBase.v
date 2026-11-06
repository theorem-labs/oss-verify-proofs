(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
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
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Export SumWalkTac RefNodes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ref_wseg_files : wseg_ok RSEGS (0x123ef0 : word) 480%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ref_wseg_crt : wseg_ok RSEGS (0x129e60 : word) 8160%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ref_wseg_tail : wseg_ok RSEGS (0x65ee40 : word) 152000%nat = true.
Proof. vm_compute. reflexivity. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma store_ok_data : forall m (a : word) n,
  ((0x123ef0 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x1240d0)
   \/ (0x129e60 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x12be40)
   \/ (0x65ee40 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x684000))%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n [[Hlo Hhi] | [[Hlo Hhi] | [Hlo Hhi]]].
  - eapply (store_ok_window RSEGS m (0x123ef0 : word) a 480%nat n 0x123ef0 0x1240d0);
      [reflexivity | reflexivity | lia | exact ref_wseg_files | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0x129e60 : word) a 8160%nat n 0x129e60 0x12be40);
      [reflexivity | reflexivity | lia | exact ref_wseg_crt | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0x65ee40 : word) a 152000%nat n 0x65ee40 0x684000);
      [reflexivity | reflexivity | lia | exact ref_wseg_tail | exact Hlo | exact Hhi].
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
  rdn RSEGS mem (Z_to_bv 64 0x681a83) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x681ee8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x1241b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1240d0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x1240c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123fe0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x123fd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123ef0)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
