(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x1c5b08, [C8 (Z_to_bv 64 0x1bc27c)]); (0x1c5b20, [C8 (Z_to_bv 64 0x1ae608)])              (* [comment removed for export] *)
  ; (0x1d6970, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x1bd440, [C8 (Z_to_bv 64 0xe7d1c); C8 (Z_to_bv 64 0x90214)])              (* [comment removed for export] *)
  ; (0x1c3ad8, [C8 (Z_to_bv 64 0x1c8578)])                                        (* [comment removed for export] *)
  ; (0x1c3bb0, [C8 (Z_to_bv 64 0x1a66ec); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x1c4850, [C8 (Z_to_bv 64 0x1c3ad8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x1c4870, [C8 (Z_to_bv 64 0x1c8870); C8 (Z_to_bv 64 0x1d59f0)])              (* [comment removed for export] *)
  ; (0x1c4a48, [C8 (Z_to_bv 64 0x1bd450); C8 (Z_to_bv 64 0x1bd440)])              (* [comment removed for export] *)
  ; (0x1c5ac0, [C8 (Z_to_bv 64 0x1c5ac0)])                                        (* [comment removed for export] *)
  ; (0x1c5b60, [C8 (Z_to_bv 64 0x1b4c58); C8 (Z_to_bv 64 0x1ae960); C8 (Z_to_bv 64 0x1b4c78)])  (* [comment removed for export] *)
  ; (0x1d68d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x26ac3c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x26af60, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x1149b, 10)     (* [comment removed for export] *)
  ; (0x17742, 4)      (* [comment removed for export] *)
  ; (0x19300, 128)    (* [comment removed for export] *)
  ; (0x20360, 33)     (* [comment removed for export] *)
  ; (0x27cb9, 21)     (* [comment removed for export] *)
  ; (0x27cce, 23)     (* [comment removed for export] *)
  ; (0x2b740, 128)    (* [comment removed for export] *)
  ; (0x2d671, 7)      (* [comment removed for export] *)
  ; (0x2de38, 16)     (* [comment removed for export] *)
  ; (0x6fb700, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x1c5b08, 0x1c5b10); (0x1c5b20, 0x1c5b28); (0x1d6970, 0x1d6978);
    (0x1bd440, 0x1bd450); (0x1c3ad8, 0x1c3ae0); (0x1c3bb0, 0x1c3bc0); (0x1c4850, 0x1c4860); (0x1c4870, 0x1c4880); (0x1c4a48, 0x1c4a58);
    (0x1c5ac0, 0x1c5ac8); (0x1c5b60, 0x1c5b78); (0x1d68d0, 0x1d68d4); (0x26ac3c, 0x26ac3d); (0x26af60, 0x26af61) ].

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
