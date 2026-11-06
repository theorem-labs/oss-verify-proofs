(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PATX : Z := 0x10e5a0.          (* [comment removed for export] *)
Definition PATX_LOCK : Z := 0x10e5a4.     (* [comment removed for export] *)
Definition PATX_SLOT : Z := 0x10e5a8.     (* [comment removed for export] *)
Definition PATX_HEAD : Z := 0x10e5b0.     (* [comment removed for export] *)
Definition PATX_BUILTIN : Z := 0x10e5b8.  (* [comment removed for export] *)
Definition PATX_F2 : Z := 0x10e5d0.       (* [comment removed for export] *)
Definition PATX_A0 : Z := 0x10e6c0.       (* [comment removed for export] *)
Definition PATX_A2 : Z := 0x10e6d0.       (* [comment removed for export] *)
Definition PATX_END : Z := 0x10e7c0.      (* [comment removed for export] *)
Definition PATEXIT : Z := 0xbdd6c.       (* [comment removed for export] *)
Definition PCXA_ATEXIT : Z := 0xbdca4.   (* [comment removed for export] *)
Definition PFUNCS_ON_EXIT : Z := 0xbdbd8. (* [comment removed for export] *)
Definition PCALL_THUNK : Z := 0xbde30.   (* [comment removed for export] *)
Definition PAEF_GUARD : Z := 0x3bd9c.    (* [comment removed for export] *)
Definition PIN_CB : Z := 0xec2b4.        (* [comment removed for export] *)
Definition PIOS_DTOR_F : Z := 0x80124.   (* [comment removed for export] *)
Definition PIOS_DTOR_A : Z := 0xec5f8.   (* [comment removed for export] *)
Definition PNEED_LOCKS_ROW : Z := 0x10e7e8. (* [comment removed for export] *)
Definition ATEXIT_STACK : Z := 48.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition patx_table (n f1 a1 f2 a2 : Z) (m : mem) : Prop :=
  rw_cells usegs m 0x10e5a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)]      (* [comment removed for export] *)
  /\ rw_cells usegs m 0x10e5b0 [C8 (Z_to_bv 64 0x10e5b8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x80124); C8 (Z_to_bv 64 f1)] (* [comment removed for export] *)
  /\ rw_cells usegs m 0x10e5d0 [C8 (Z_to_bv 64 f2)]                                                                    (* [comment removed for export] *)
  /\ rw_cells usegs m 0x10e6c0 [C8 (Z_to_bv 64 0xec5f8); C8 (Z_to_bv 64 a1)]                                           (* [comment removed for export] *)
  /\ rw_cells usegs m 0x10e6d0 [C8 (Z_to_bv 64 a2)].                                                                   (* [comment removed for export] *)

Definition patexit_main (m : mem) : Prop := patx_table 1 0 0 0 0 m.

Definition pincb (cb : Z) (m : mem) : Prop := rw_cells usegs m 0xec2b4 [C1 (Z_to_bv 8 cb)].

(* [comment removed for export] *)
Definition patx_addr (a : Z) : Prop :=
  (0x10e5a0 <= a < 0x10e5b0) \/ (0x10e5b0 <= a < 0x10e5d8) \/ (0x10e6c0 <= a < 0x10e6d8).
Definition pincb_addr (a : Z) : Prop := 0xec2b4 <= a < 0xec2b5.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold patx_addr, pincb_addr in *; cbn in Ha; lia].

Lemma patx_table_agree : forall (P : Z -> Prop) n f1 a1 f2 a2 m m',
  magree usegs P m m' -> (forall a, patx_addr a -> P a) -> patx_table n f1 a1 f2 a2 m -> patx_table n f1 a1 f2 a2 m'.
Proof.
  intros P n f1 a1 f2 a2 m m' AG HP (A1 & A2 & A3 & A4 & A5).
  split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4| tr AG HP A5].
Qed.

Lemma patx_table_munch : forall W n f1 a1 f2 a2 m m',
  munch W m m' -> wmono usegs m m' -> (forall a, patx_addr a -> outside W a) -> patx_table n f1 a1 f2 a2 m -> patx_table n f1 a1 f2 a2 m'.
Proof.
  intros W n f1 a1 f2 a2 m m' MU WM HW. apply (patx_table_agree _ _ _ _ _ _ _ _ (magree_of_munch usegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha.
Qed.

Lemma patexit_main_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, patx_addr a -> P a) -> patexit_main m -> patexit_main m'.
Proof. intros P m m' AG HP H. exact (patx_table_agree _ _ _ _ _ _ _ _ AG HP H). Qed.

Lemma pincb_agree : forall (P : Z -> Prop) cb m m',
  magree usegs P m m' -> (forall a, pincb_addr a -> P a) -> pincb cb m -> pincb cb m'.
Proof. intros P cb m m' AG HP A. unfold pincb in *. tr AG HP A. Qed.

Lemma pincb_munch : forall W cb m m',
  munch W m m' -> wmono usegs m m' -> (forall a, pincb_addr a -> outside W a) -> pincb cb m -> pincb cb m'.
Proof.
  intros W cb m m' MU WM HW. apply (pincb_agree _ _ _ _ (magree_of_munch usegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma patx_addr_range : forall a, patx_addr a -> 0x10e5a0 <= a < 0x10e6d8.
Proof. intros a Ha. unfold patx_addr in Ha. lia. Qed.
Lemma pincb_addr_range : forall a, pincb_addr a -> a = 0xec2b4.
Proof. intros a Ha. unfold pincb_addr in Ha. lia. Qed.
