(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xca600, [C8 (Z_to_bv 64 0xc42b4); C8 (Z_to_bv 64 0xbb1b8)])              (* [comment removed for export] *)
  ; (0xcf570, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc5438, [C8 (Z_to_bv 64 0x8c780); C8 (Z_to_bv 64 0x3ae14)])              (* [comment removed for export] *)
  ; (0xc8770, [C8 (Z_to_bv 64 0xccf48)])                                        (* [comment removed for export] *)
  ; (0xc8848, [C8 (Z_to_bv 64 0xb5000); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc94d8, [C8 (Z_to_bv 64 0xc8770); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc94f8, [C8 (Z_to_bv 64 0xcd240); C8 (Z_to_bv 64 0xce600)])              (* [comment removed for export] *)
  ; (0xc9580, [C8 (Z_to_bv 64 0xc5448); C8 (Z_to_bv 64 0xc5438)])              (* [comment removed for export] *)
  ; (0xca5c0, [C8 (Z_to_bv 64 0xca5c0)])                                        (* [comment removed for export] *)
  ; (0xca628, [C8 (Z_to_bv 64 0xbe4fc); C8 (Z_to_bv 64 0xbb3ec); C8 (Z_to_bv 64 0xbe518)])  (* [comment removed for export] *)
  ; (0xcf4d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x16383c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x163b60, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10ca5, 10)     (* [comment removed for export] *)
  ; (0x14d07, 4)      (* [comment removed for export] *)
  ; (0x16000, 128)    (* [comment removed for export] *)
  ; (0x1a6c4, 33)     (* [comment removed for export] *)
  ; (0x1ed1a, 21)     (* [comment removed for export] *)
  ; (0x1ed2f, 23)     (* [comment removed for export] *)
  ; (0x212c0, 128)    (* [comment removed for export] *)
  ; (0x222bf, 7)      (* [comment removed for export] *)
  ; (0x26db0, 16)     (* [comment removed for export] *)
  ; (0x5f4300, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xca600, 0xca610); (0xcf570, 0xcf578);
    (0xc5438, 0xc5448); (0xc8770, 0xc8778); (0xc8848, 0xc8858); (0xc94d8, 0xc94e8); (0xc94f8, 0xc9508); (0xc9580, 0xc9590);
    (0xca5c0, 0xca5c8); (0xca628, 0xca640); (0xcf4d0, 0xcf4d4); (0x16383c, 0x16383d); (0x163b60, 0x163b61) ].

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
