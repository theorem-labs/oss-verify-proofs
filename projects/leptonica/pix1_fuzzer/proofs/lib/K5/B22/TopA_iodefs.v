(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcaf00, [C8 (Z_to_bv 64 0xc4bb0); C8 (Z_to_bv 64 0xbbab4)])              (* [comment removed for export] *)
  ; (0xcfff0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc5d30, [C8 (Z_to_bv 64 0x8c930); C8 (Z_to_bv 64 0x3afc4)])              (* [comment removed for export] *)
  ; (0xc9068, [C8 (Z_to_bv 64 0xcd848)])                                        (* [comment removed for export] *)
  ; (0xc9140, [C8 (Z_to_bv 64 0xb58fc); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc9dd0, [C8 (Z_to_bv 64 0xc9068); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc9df0, [C8 (Z_to_bv 64 0xcdb40); C8 (Z_to_bv 64 0xcf080)])              (* [comment removed for export] *)
  ; (0xc9e78, [C8 (Z_to_bv 64 0xc5d40); C8 (Z_to_bv 64 0xc5d30)])              (* [comment removed for export] *)
  ; (0xcaec0, [C8 (Z_to_bv 64 0xcaec0)])                                        (* [comment removed for export] *)
  ; (0xcaf28, [C8 (Z_to_bv 64 0xbedf8); C8 (Z_to_bv 64 0xbbce8); C8 (Z_to_bv 64 0xbee14)])  (* [comment removed for export] *)
  ; (0xcff50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1642bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1645e0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10ca5, 10)     (* [comment removed for export] *)
  ; (0x14d1c, 4)      (* [comment removed for export] *)
  ; (0x16000, 128)    (* [comment removed for export] *)
  ; (0x1a6d9, 33)     (* [comment removed for export] *)
  ; (0x1ed2f, 21)     (* [comment removed for export] *)
  ; (0x1ed44, 23)     (* [comment removed for export] *)
  ; (0x21300, 128)    (* [comment removed for export] *)
  ; (0x222ff, 7)      (* [comment removed for export] *)
  ; (0x26ed0, 16)     (* [comment removed for export] *)
  ; (0x5f4d80, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcaf00, 0xcaf10); (0xcfff0, 0xcfff8);
    (0xc5d30, 0xc5d40); (0xc9068, 0xc9070); (0xc9140, 0xc9150); (0xc9dd0, 0xc9de0); (0xc9df0, 0xc9e00); (0xc9e78, 0xc9e88);
    (0xcaec0, 0xcaec8); (0xcaf28, 0xcaf40); (0xcff50, 0xcff54); (0x1642bc, 0x1642bd); (0x1645e0, 0x1645e1) ].

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
