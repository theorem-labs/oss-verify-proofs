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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x1d1328, [C8 (Z_to_bv 64 0x1c7aa0)]); (0x1d1340, [C8 (Z_to_bv 64 0x1b9da8)])              (* [comment removed for export] *)
  ; (0x1e23f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x1c8c60, [C8 (Z_to_bv 64 0xe8080); C8 (Z_to_bv 64 0x90428)])              (* [comment removed for export] *)
  ; (0x1cf2f8, [C8 (Z_to_bv 64 0x1d3d98)])                                        (* [comment removed for export] *)
  ; (0x1cf3d0, [C8 (Z_to_bv 64 0x1b1e6c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x1d0070, [C8 (Z_to_bv 64 0x1cf2f8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x1d0090, [C8 (Z_to_bv 64 0x1d4090); C8 (Z_to_bv 64 0x1e1450)])              (* [comment removed for export] *)
  ; (0x1d0268, [C8 (Z_to_bv 64 0x1c8c70); C8 (Z_to_bv 64 0x1c8c60)])              (* [comment removed for export] *)
  ; (0x1d12e0, [C8 (Z_to_bv 64 0x1d12e0)])                                        (* [comment removed for export] *)
  ; (0x1d1380, [C8 (Z_to_bv 64 0x1c0454); C8 (Z_to_bv 64 0x1ba104); C8 (Z_to_bv 64 0x1c0474)])  (* [comment removed for export] *)
  ; (0x1e2350, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x2766bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x2769e0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x114bb, 10)     (* [comment removed for export] *)
  ; (0x177bb, 4)      (* [comment removed for export] *)
  ; (0x19380, 128)    (* [comment removed for export] *)
  ; (0x203bc, 33)     (* [comment removed for export] *)
  ; (0x27a98, 21)     (* [comment removed for export] *)
  ; (0x27aad, 23)     (* [comment removed for export] *)
  ; (0x2b540, 128)    (* [comment removed for export] *)
  ; (0x2d450, 7)      (* [comment removed for export] *)
  ; (0x2dc18, 16)     (* [comment removed for export] *)
  ; (0x707180, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x1d1328, 0x1d1330); (0x1d1340, 0x1d1348); (0x1e23f0, 0x1e23f8);
    (0x1c8c60, 0x1c8c70); (0x1cf2f8, 0x1cf300); (0x1cf3d0, 0x1cf3e0); (0x1d0070, 0x1d0080); (0x1d0090, 0x1d00a0); (0x1d0268, 0x1d0278);
    (0x1d12e0, 0x1d12e8); (0x1d1380, 0x1d1398); (0x1e2350, 0x1e2354); (0x2766bc, 0x2766bd); (0x2769e0, 0x2769e1) ].

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
