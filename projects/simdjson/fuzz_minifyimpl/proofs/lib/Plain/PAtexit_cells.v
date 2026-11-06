(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PATX : Z := 0x103a70.          (* [comment removed for export] *)
Definition PATX_LOCK : Z := 0x103a74.     (* [comment removed for export] *)
Definition PATX_SLOT : Z := 0x103a78.     (* [comment removed for export] *)
Definition PATX_HEAD : Z := 0x103a80.     (* [comment removed for export] *)
Definition PATX_BUILTIN : Z := 0x103a88.  (* [comment removed for export] *)
Definition PATX_F2 : Z := 0x103aa0.       (* [comment removed for export] *)
Definition PATX_A0 : Z := 0x103b90.       (* [comment removed for export] *)
Definition PATX_A2 : Z := 0x103ba0.       (* [comment removed for export] *)
Definition PATX_END : Z := 0x103c90.      (* [comment removed for export] *)
Definition PATEXIT : Z := 0xb3538.       (* [comment removed for export] *)
Definition PCXA_ATEXIT : Z := 0xb3470.   (* [comment removed for export] *)
Definition PFUNCS_ON_EXIT : Z := 0xb33a4. (* [comment removed for export] *)
Definition PCALL_THUNK : Z := 0xb35fc.   (* [comment removed for export] *)
Definition PAEF_GUARD : Z := 0x3bc9c.    (* [comment removed for export] *)
Definition PIN_CB : Z := 0xe1784.        (* [comment removed for export] *)
Definition PIOS_DTOR_F : Z := 0x758f0.   (* [comment removed for export] *)
Definition PIOS_DTOR_A : Z := 0xe1ac8.   (* [comment removed for export] *)
Definition PNEED_LOCKS_ROW : Z := 0x103cb8. (* [comment removed for export] *)
Definition ATEXIT_STACK : Z := 48.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition patx_table (n f1 a1 f2 a2 : Z) (m : mem) : Prop :=
  rw_cells psegs m 0x103a70 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)]      (* [comment removed for export] *)
  /\ rw_cells psegs m 0x103a80 [C8 (Z_to_bv 64 0x103a88); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x758f0); C8 (Z_to_bv 64 f1)] (* [comment removed for export] *)
  /\ rw_cells psegs m 0x103aa0 [C8 (Z_to_bv 64 f2)]                                                                    (* [comment removed for export] *)
  /\ rw_cells psegs m 0x103b90 [C8 (Z_to_bv 64 0xe1ac8); C8 (Z_to_bv 64 a1)]                                           (* [comment removed for export] *)
  /\ rw_cells psegs m 0x103ba0 [C8 (Z_to_bv 64 a2)].                                                                   (* [comment removed for export] *)

Definition patexit_main (m : mem) : Prop := patx_table 1 0 0 0 0 m.

Definition pincb (cb : Z) (m : mem) : Prop := rw_cells psegs m 0xe1784 [C1 (Z_to_bv 8 cb)].

(* [comment removed for export] *)
Definition patx_addr (a : Z) : Prop :=
  (0x103a70 <= a < 0x103a80) \/ (0x103a80 <= a < 0x103aa8) \/ (0x103b90 <= a < 0x103ba8).
Definition pincb_addr (a : Z) : Prop := 0xe1784 <= a < 0xe1785.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold patx_addr, pincb_addr in *; cbn in Ha; lia].

Lemma patx_table_agree : forall (P : Z -> Prop) n f1 a1 f2 a2 m m',
  magree psegs P m m' -> (forall a, patx_addr a -> P a) -> patx_table n f1 a1 f2 a2 m -> patx_table n f1 a1 f2 a2 m'.
Proof.
  intros P n f1 a1 f2 a2 m m' AG HP (A1 & A2 & A3 & A4 & A5).
  split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4| tr AG HP A5].
Qed.

Lemma patx_table_munch : forall W n f1 a1 f2 a2 m m',
  munch W m m' -> wmono psegs m m' -> (forall a, patx_addr a -> outside W a) -> patx_table n f1 a1 f2 a2 m -> patx_table n f1 a1 f2 a2 m'.
Proof.
  intros W n f1 a1 f2 a2 m m' MU WM HW. apply (patx_table_agree _ _ _ _ _ _ _ _ (magree_of_munch psegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha.
Qed.

Lemma patexit_main_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, patx_addr a -> P a) -> patexit_main m -> patexit_main m'.
Proof. intros P m m' AG HP H. exact (patx_table_agree _ _ _ _ _ _ _ _ AG HP H). Qed.

Lemma pincb_agree : forall (P : Z -> Prop) cb m m',
  magree psegs P m m' -> (forall a, pincb_addr a -> P a) -> pincb cb m -> pincb cb m'.
Proof. intros P cb m m' AG HP A. unfold pincb in *. tr AG HP A. Qed.

Lemma pincb_munch : forall W cb m m',
  munch W m m' -> wmono psegs m m' -> (forall a, pincb_addr a -> outside W a) -> pincb cb m -> pincb cb m'.
Proof.
  intros W cb m m' MU WM HW. apply (pincb_agree _ _ _ _ (magree_of_munch psegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma patx_addr_range : forall a, patx_addr a -> 0x103a70 <= a < 0x103ba8.
Proof. intros a Ha. unfold patx_addr in Ha. lia. Qed.
Lemma pincb_addr_range : forall a, pincb_addr a -> a = 0xe1784.
Proof. intros a Ha. unfold pincb_addr in Ha. lia. Qed.
