(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcc900, [C8 (Z_to_bv 64 0xc65ac); C8 (Z_to_bv 64 0xbd4b0)])              (* [comment removed for export] *)
  ; (0xd1ef0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc7730, [C8 (Z_to_bv 64 0x8d1a4); C8 (Z_to_bv 64 0x3b7c8)])              (* [comment removed for export] *)
  ; (0xcaa68, [C8 (Z_to_bv 64 0xcf248)])                                        (* [comment removed for export] *)
  ; (0xcab40, [C8 (Z_to_bv 64 0xb72f8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcb7d0, [C8 (Z_to_bv 64 0xcaa68); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcb7f0, [C8 (Z_to_bv 64 0xcf540); C8 (Z_to_bv 64 0xd0f80)])              (* [comment removed for export] *)
  ; (0xcb878, [C8 (Z_to_bv 64 0xc7740); C8 (Z_to_bv 64 0xc7730)])              (* [comment removed for export] *)
  ; (0xcc8c0, [C8 (Z_to_bv 64 0xcc8c0)])                                        (* [comment removed for export] *)
  ; (0xcc928, [C8 (Z_to_bv 64 0xc07f4); C8 (Z_to_bv 64 0xbd6e4); C8 (Z_to_bv 64 0xc0810)])  (* [comment removed for export] *)
  ; (0xd1e50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1661bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1664e0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10ca5, 10)     (* [comment removed for export] *)
  ; (0x14d1b, 4)      (* [comment removed for export] *)
  ; (0x16000, 128)    (* [comment removed for export] *)
  ; (0x1a731, 33)     (* [comment removed for export] *)
  ; (0x1edde, 21)     (* [comment removed for export] *)
  ; (0x1edf3, 23)     (* [comment removed for export] *)
  ; (0x21400, 128)    (* [comment removed for export] *)
  ; (0x2241c, 7)      (* [comment removed for export] *)
  ; (0x27558, 16)     (* [comment removed for export] *)
  ; (0x5f6c80, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcc900, 0xcc910); (0xd1ef0, 0xd1ef8);
    (0xc7730, 0xc7740); (0xcaa68, 0xcaa70); (0xcab40, 0xcab50); (0xcb7d0, 0xcb7e0); (0xcb7f0, 0xcb800); (0xcb878, 0xcb888);
    (0xcc8c0, 0xcc8c8); (0xcc928, 0xcc940); (0xd1e50, 0xd1e54); (0x1661bc, 0x1661bd); (0x1664e0, 0x1664e1) ].

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
