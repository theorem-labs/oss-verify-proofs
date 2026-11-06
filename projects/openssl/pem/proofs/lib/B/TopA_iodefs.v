(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5df8a0, [C8 (Z_to_bv 64 0x565f04); C8 (Z_to_bv 64 0x55a240); C8 (Z_to_bv 64 0x55a6a0)])  (* [comment removed for export] *)
  ; (0x69cbf0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x566f58, [C8 (Z_to_bv 64 0x1eef1c); C8 (Z_to_bv 64 0x194a94); C8 (Z_to_bv 64 0x1ee498)])  (* [comment removed for export] *)
  ; (0x5dc728, [C8 (Z_to_bv 64 0x5e2ca8)])                                        (* [comment removed for export] *)
  ; (0x5dc808, [C8 (Z_to_bv 64 0x553640); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5dd4b8, [C8 (Z_to_bv 64 0x5dc728); C8 (Z_to_bv 64 0x1edff4)])              (* [comment removed for export] *)
  ; (0x5de788, [C8 (Z_to_bv 64 0x5e2fa0); C8 (Z_to_bv 64 0x69bc60)])              (* [comment removed for export] *)
  ; (0x5de7d0, [C8 (Z_to_bv 64 0x566f70); C8 (Z_to_bv 64 0x566f58)])              (* [comment removed for export] *)
  ; (0x5df840, [C8 (Z_to_bv 64 0x5df840)])                                        (* [comment removed for export] *)
  ; (0x5df8d8, [C8 (Z_to_bv 64 0x55da78); C8 (Z_to_bv 64 0x55a91c); C8 (Z_to_bv 64 0x55da98)])  (* [comment removed for export] *)
  ; (0x69cb50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x730ebc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x7311e0, [C1 (Z_to_bv 8 0)])                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x5df860, [C8 (Z_to_bv 64 0x55f108)])        (* [comment removed for export] *)
  ; (0x730f65, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x5dde38, [C8 (Z_to_bv 64 0x1fb31c)])        (* [comment removed for export] *)
  ; (0x5dde50, [C8 (Z_to_bv 64 0x1fb83c)])        (* [comment removed for export] *)
  ; (0x5de0a0, [C8 (Z_to_bv 64 0x31deec)])        (* [comment removed for export] *)
  ; (0x5dde70, [C8 (Z_to_bv 64 0x2654dc)])        (* [comment removed for export] *)
  ; (0x5dde78, [C8 (Z_to_bv 64 0x265744)])        (* [comment removed for export] *)
  ; (0x730f66, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x730f67, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121e9, 10)     (* [comment removed for export] *)
  ; (0x1d92d, 4)      (* [comment removed for export] *)
  ; (0x21100, 128)    (* [comment removed for export] *)
  ; (0x2ef6a, 33)     (* [comment removed for export] *)
  ; (0x3d1e5, 21)     (* [comment removed for export] *)
  ; (0x3d1fa, 23)     (* [comment removed for export] *)
  ; (0x44580, 128)    (* [comment removed for export] *)
  ; (0x48d54, 7)      (* [comment removed for export] *)
  ; (0x113510, 16)     (* [comment removed for export] *)
  ; (0xbc1980, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5df8a0, 0x5df8b8); (0x69cbf0, 0x69cbf8);
    (0x566f58, 0x566f70); (0x5dc728, 0x5dc730); (0x5dc808, 0x5dc818); (0x5dd4b8, 0x5dd4c8); (0x5de788, 0x5de798); (0x5de7d0, 0x5de7e0);
    (0x5df840, 0x5df848); (0x5df8d8, 0x5df8f0); (0x69cb50, 0x69cb54); (0x730ebc, 0x730ebd); (0x7311e0, 0x7311e1);
    (0x5df860, 0x5df868); (0x730f65, 0x730f66); (0x5dde38, 0x5dde40); (0x5dde50, 0x5dde58); (0x5de0a0, 0x5de0a8); (0x5dde70, 0x5dde78); (0x5dde78, 0x5dde80);
    (0x730f66, 0x730f67); (0x730f67, 0x730f68) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
