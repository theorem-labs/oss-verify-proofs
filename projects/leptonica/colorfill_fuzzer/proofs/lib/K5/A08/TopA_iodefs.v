(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcdb80, [C8 (Z_to_bv 64 0xc7838); C8 (Z_to_bv 64 0xbe73c)])              (* [comment removed for export] *)
  ; (0xd3630, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc89b8, [C8 (Z_to_bv 64 0x8d9a4); C8 (Z_to_bv 64 0x3bfc8)])              (* [comment removed for export] *)
  ; (0xcbcf0, [C8 (Z_to_bv 64 0xd04c8)])                                        (* [comment removed for export] *)
  ; (0xcbdc8, [C8 (Z_to_bv 64 0xb8584); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcca58, [C8 (Z_to_bv 64 0xcbcf0); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcca78, [C8 (Z_to_bv 64 0xd07c0); C8 (Z_to_bv 64 0xd26c0)])              (* [comment removed for export] *)
  ; (0xccb00, [C8 (Z_to_bv 64 0xc89c8); C8 (Z_to_bv 64 0xc89b8)])              (* [comment removed for export] *)
  ; (0xcdb40, [C8 (Z_to_bv 64 0xcdb40)])                                        (* [comment removed for export] *)
  ; (0xcdba8, [C8 (Z_to_bv 64 0xc1a80); C8 (Z_to_bv 64 0xbe970); C8 (Z_to_bv 64 0xc1a9c)])  (* [comment removed for export] *)
  ; (0xd3590, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1678fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x167c20, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10cc1, 10)     (* [comment removed for export] *)
  ; (0x14db8, 4)      (* [comment removed for export] *)
  ; (0x160c0, 128)    (* [comment removed for export] *)
  ; (0x1a80f, 33)     (* [comment removed for export] *)
  ; (0x1eed7, 21)     (* [comment removed for export] *)
  ; (0x1eeec, 23)     (* [comment removed for export] *)
  ; (0x21480, 128)    (* [comment removed for export] *)
  ; (0x224b3, 7)      (* [comment removed for export] *)
  ; (0x27b58, 16)     (* [comment removed for export] *)
  ; (0x5f83c0, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcdb80, 0xcdb90); (0xd3630, 0xd3638);
    (0xc89b8, 0xc89c8); (0xcbcf0, 0xcbcf8); (0xcbdc8, 0xcbdd8); (0xcca58, 0xcca68); (0xcca78, 0xcca88); (0xccb00, 0xccb10);
    (0xcdb40, 0xcdb48); (0xcdba8, 0xcdbc0); (0xd3590, 0xd3594); (0x1678fc, 0x1678fd); (0x167c20, 0x167c21) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc asegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
