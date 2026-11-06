(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xe5da0, [C8 (Z_to_bv 64 0xdfa44); C8 (Z_to_bv 64 0xd6948)])              (* [comment removed for export] *)
  ; (0xede70, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x1821e2, [C1 (Z_to_bv 8 1)])    (* [comment removed for export] *)
  ; (0xe0bc8, [C8 (Z_to_bv 64 0x914c4); C8 (Z_to_bv 64 0x3f698)])              (* [comment removed for export] *)
  ; (0xe3f00, [C8 (Z_to_bv 64 0xe8ac8)])                                        (* [comment removed for export] *)
  ; (0xe3fd8, [C8 (Z_to_bv 64 0xd0790); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe4c68, [C8 (Z_to_bv 64 0xe3f00); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe4c88, [C8 (Z_to_bv 64 0xe8dc0); C8 (Z_to_bv 64 0xecf00)])              (* [comment removed for export] *)
  ; (0xe4d10, [C8 (Z_to_bv 64 0xe0bd8); C8 (Z_to_bv 64 0xe0bc8)])              (* [comment removed for export] *)
  ; (0xe5d60, [C8 (Z_to_bv 64 0xe5d60)])                                        (* [comment removed for export] *)
  ; (0xe5dc8, [C8 (Z_to_bv 64 0xd9c8c); C8 (Z_to_bv 64 0xd6b7c); C8 (Z_to_bv 64 0xd9ca8)])  (* [comment removed for export] *)
  ; (0xeddd0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x18213c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x182460, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d35, 10)     (* [comment removed for export] *)
  ; (0x14f06, 4)      (* [comment removed for export] *)
  ; (0x16280, 192)    (* [comment removed for export] *)
  ; (0x1acad, 33)     (* [comment removed for export] *)
  ; (0x1f59e, 21)     (* [comment removed for export] *)
  ; (0x1f5b3, 23)     (* [comment removed for export] *)
  ; (0x21e40, 128)    (* [comment removed for export] *)
  ; (0x22edb, 7)      (* [comment removed for export] *)
  ; (0x2a260, 16)     (* [comment removed for export] *)
  ; (0x612c00, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xe5da0, 0xe5db0); (0xede70, 0xede78);
    (0x1821e2, 0x1821e3); (0xe0bc8, 0xe0bd8); (0xe3f00, 0xe3f08); (0xe3fd8, 0xe3fe8); (0xe4c68, 0xe4c78); (0xe4c88, 0xe4c98); (0xe4d10, 0xe4d20);
    (0xe5d60, 0xe5d68); (0xe5dc8, 0xe5de0); (0xeddd0, 0xeddd4); (0x18213c, 0x18213d); (0x182460, 0x182461) ].

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
