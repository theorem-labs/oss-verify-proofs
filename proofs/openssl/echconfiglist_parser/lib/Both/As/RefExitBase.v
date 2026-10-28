(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Export SumWalkTac RefNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import WsegFast.   (* [comment removed for export] *)
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
Lemma ref_wseg_files : wseg_ok RSEGS (0x5edca8 : word) 744%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.
Lemma ref_wseg_crt : wseg_ok RSEGS (0x6a6640 : word) 8192%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.
Lemma ref_wseg_tail : wseg_ok RSEGS (0xbdcf40 : word) 159936%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.

Lemma store_ok_data : forall m (a : word) n,
  ((0x5edca8 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x5edf90)
   \/ (0x6a6640 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x6a8640)
   \/ (0xbdcf40 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0xc04000))%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n [[Hlo Hhi]|[[Hlo Hhi]|[Hlo Hhi]]].
  - eapply (store_ok_window RSEGS m (0x5edca8 : word) a 744%nat n 0x5edca8 0x5edf90);
      [reflexivity | reflexivity | lia | exact ref_wseg_files | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0x6a6640 : word) a 8192%nat n 0x6a6640 0x6a8640);
      [reflexivity | reflexivity | lia | exact ref_wseg_crt | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0xbdcf40 : word) a 159936%nat n 0xbdcf40 0xc04000);
      [reflexivity | vm_compute; reflexivity | lia | exact ref_wseg_tail | exact Hlo | exact Hhi].
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
  rdn RSEGS mem (Z_to_bv 64 0xc01f23) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xc02388) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5ede80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5edd98)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5edf70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5ede88)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5edd90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5edca8)). (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_cells (mem : word -> option byte) (ax : bool) : Prop :=
  if ax then
       rdn RSEGS mem (Z_to_bv 64 0xc01cf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc01cf8))
    /\ rdn RSEGS mem (Z_to_bv 64 0xc01ce8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
    /\ rdn RSEGS mem (Z_to_bv 64 0xc01cf8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn RSEGS mem (Z_to_bv 64 0xc01d00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x55e508))
    /\ rdn RSEGS mem (Z_to_bv 64 0xc01e00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ef154))
    /\ rdn RSEGS mem (Z_to_bv 64 0xbdcf54) 1%nat = Some [Z_to_bv 8 0]
  else rdn RSEGS mem (Z_to_bv 64 0xc01cf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition stdin_clean (mem : word -> option byte) : Prop :=
  file_clean mem 0x5edd98 (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma osl_byte_ex : forall mem : word -> option byte, exists bi : byte, rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1%nat = Some [bi].
Proof.
  intros mem. cbn [rdn]. destruct (mem (Z_to_bv 64 0xbdd420)) as [b|].
  - exists b. reflexivity.
  - exists (Z_to_bv 8 0).
    replace (seg_rom RSEGS (Z_to_bv 64 0xbdd420)) with (Some (Z_to_bv 8 0) : option byte); [reflexivity|].
    symmetry. apply (@bool_decide_eq_true_1 _ _). vm_cast_no_check (@eq_refl bool true).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
