(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import WsegFast.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ref_wseg_files : wseg_ok RSEGS (0x5b4848 : word) 744%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.
Lemma ref_wseg_crt : wseg_ok RSEGS (0x673000 : word) 8192%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.
Lemma ref_wseg_tail : wseg_ok RSEGS (0xba9900 : word) 157440%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.

Lemma store_ok_data : forall m (a : word) n,
  ((0x5b4848 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x5b4b30)
   \/ (0x673000 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x675000)
   \/ (0xba9900 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0xbd0000))%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n [[Hlo Hhi]|[[Hlo Hhi]|[Hlo Hhi]]].
  - eapply (store_ok_window RSEGS m (0x5b4848 : word) a 744%nat n 0x5b4848 0x5b4b30);
      [reflexivity | reflexivity | lia | exact ref_wseg_files | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0x673000 : word) a 8192%nat n 0x673000 0x675000);
      [reflexivity | reflexivity | lia | exact ref_wseg_crt | exact Hlo | exact Hhi].
  - eapply (store_ok_window RSEGS m (0xba9900 : word) a 157440%nat n 0xba9900 0xbd0000);
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
  rdn RSEGS mem (Z_to_bv 64 0xbce8e3) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xbced48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5b4a20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5b4938)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5b4b10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5b4a28)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5b4930) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5b4848)). (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_cells (mem : word -> option byte) (ax : bool) : Prop :=
  if ax then
       rdn RSEGS mem (Z_to_bv 64 0xbce6b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbce6b8))
    /\ rdn RSEGS mem (Z_to_bv 64 0xbce6a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
    /\ rdn RSEGS mem (Z_to_bv 64 0xbce6b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn RSEGS mem (Z_to_bv 64 0xbce6c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x524ef8))
    /\ rdn RSEGS mem (Z_to_bv 64 0xbce7c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f422c))
    /\ rdn RSEGS mem (Z_to_bv 64 0xba9914) 1%nat = Some [Z_to_bv 8 0]
  else rdn RSEGS mem (Z_to_bv 64 0xbce6b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition stdin_clean (mem : word -> option byte) : Prop :=
  file_clean mem 0x5b4938 (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma osl_byte_ex : forall mem : word -> option byte, exists bi : byte, rdn RSEGS mem (Z_to_bv 64 0xba9de0) 1%nat = Some [bi].
Proof.
  intros mem. cbn [rdn]. destruct (mem (Z_to_bv 64 0xba9de0)) as [b|].
  - exists b. reflexivity.
  - exists (Z_to_bv 8 0).
    replace (seg_rom RSEGS (Z_to_bv 64 0xba9de0)) with (Some (Z_to_bv 8 0) : option byte); [reflexivity|].
    symmetry. apply (@bool_decide_eq_true_1 _ _). vm_cast_no_check (@eq_refl bool true).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
