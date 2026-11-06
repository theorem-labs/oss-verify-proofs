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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import WsegFast.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x2dc000 : word) 217088%nat = true.
Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

Lemma store_ok_data : forall m (a : word) n,
  (0x2dc000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x311000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x2dc000 : word) a 217088%nat n 0x2dc000 0x311000);
    [reflexivity | vm_compute; reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].   (* [comment removed for export] *)
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
  rdn RSEGS mem (Z_to_bv 64 0x30f70b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x30fb40) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2dc798) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2dc6b0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2dc888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2dc7a0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2dc6a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2dc5c0)). (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_cells (mem : word -> option byte) (ax : bool) : Prop :=
  if ax then
       rdn RSEGS mem (Z_to_bv 64 0x30f4d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30f4e0))
    /\ rdn RSEGS mem (Z_to_bv 64 0x30f4d0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
    /\ rdn RSEGS mem (Z_to_bv 64 0x30f4e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn RSEGS mem (Z_to_bv 64 0x30f4e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26f030))
    /\ rdn RSEGS mem (Z_to_bv 64 0x30f5e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xddd28))
    /\ rdn RSEGS mem (Z_to_bv 64 0x2ec904) 1%nat = Some [Z_to_bv 8 0]
  else rdn RSEGS mem (Z_to_bv 64 0x30f4d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition stdin_clean (mem : word -> option byte) : Prop :=
  file_clean mem 0x2dc6b0 (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma osl_byte_ex : forall mem : word -> option byte, exists bi : byte, rdn RSEGS mem (Z_to_bv 64 0x2ecb38) 1%nat = Some [bi].
Proof.
  intros mem. cbn [rdn]. destruct (mem (Z_to_bv 64 0x2ecb38)) as [b|].
  - exists b. reflexivity.
  - exists (Z_to_bv 8 0).
    replace (seg_rom RSEGS (Z_to_bv 64 0x2ecb38)) with (Some (Z_to_bv 8 0) : option byte); [reflexivity|].
    symmetry. apply (@bool_decide_eq_true_1 _ _). vm_cast_no_check (@eq_refl bool true).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
