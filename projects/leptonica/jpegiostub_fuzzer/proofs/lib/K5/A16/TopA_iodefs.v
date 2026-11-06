(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xca5c0, [C8 (Z_to_bv 64 0xc4270); C8 (Z_to_bv 64 0xbb174)])              (* [comment removed for export] *)
  ; (0xcf530, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc53f0, [C8 (Z_to_bv 64 0x8c7f8); C8 (Z_to_bv 64 0x3ae80)])              (* [comment removed for export] *)
  ; (0xc8728, [C8 (Z_to_bv 64 0xccf08)])                                        (* [comment removed for export] *)
  ; (0xc8800, [C8 (Z_to_bv 64 0xb4fbc); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc9490, [C8 (Z_to_bv 64 0xc8728); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc94b0, [C8 (Z_to_bv 64 0xcd200); C8 (Z_to_bv 64 0xce5c0)])              (* [comment removed for export] *)
  ; (0xc9538, [C8 (Z_to_bv 64 0xc5400); C8 (Z_to_bv 64 0xc53f0)])              (* [comment removed for export] *)
  ; (0xca580, [C8 (Z_to_bv 64 0xca580)])                                        (* [comment removed for export] *)
  ; (0xca5e8, [C8 (Z_to_bv 64 0xbe4b8); C8 (Z_to_bv 64 0xbb3a8); C8 (Z_to_bv 64 0xbe4d4)])  (* [comment removed for export] *)
  ; (0xcf490, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1637fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x163b20, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10cbe, 10)     (* [comment removed for export] *)
  ; (0x14d18, 4)      (* [comment removed for export] *)
  ; (0x16000, 128)    (* [comment removed for export] *)
  ; (0x1a6dc, 33)     (* [comment removed for export] *)
  ; (0x1ed38, 21)     (* [comment removed for export] *)
  ; (0x1ed4d, 23)     (* [comment removed for export] *)
  ; (0x21300, 128)    (* [comment removed for export] *)
  ; (0x222dd, 7)      (* [comment removed for export] *)
  ; (0x26e18, 16)     (* [comment removed for export] *)
  ; (0x5f42c0, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xca5c0, 0xca5d0); (0xcf530, 0xcf538);
    (0xc53f0, 0xc5400); (0xc8728, 0xc8730); (0xc8800, 0xc8810); (0xc9490, 0xc94a0); (0xc94b0, 0xc94c0); (0xc9538, 0xc9548);
    (0xca580, 0xca588); (0xca5e8, 0xca600); (0xcf490, 0xcf494); (0x1637fc, 0x1637fd); (0x163b20, 0x163b21) ].

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
