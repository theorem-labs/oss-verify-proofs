(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xee640, [C8 (Z_to_bv 64 0xe82e8); C8 (Z_to_bv 64 0xdf1ec)])              (* [comment removed for export] *)
  ; (0xf6770, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x18aae2, [C1 (Z_to_bv 8 1)])    (* [comment removed for export] *)
  ; (0xe9468, [C8 (Z_to_bv 64 0x915c4); C8 (Z_to_bv 64 0x3f798)])              (* [comment removed for export] *)
  ; (0xec7a0, [C8 (Z_to_bv 64 0xf1368)])                                        (* [comment removed for export] *)
  ; (0xec878, [C8 (Z_to_bv 64 0xd9034); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xed508, [C8 (Z_to_bv 64 0xec7a0); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xed528, [C8 (Z_to_bv 64 0xf1660); C8 (Z_to_bv 64 0xf57e0)])              (* [comment removed for export] *)
  ; (0xed5b0, [C8 (Z_to_bv 64 0xe9478); C8 (Z_to_bv 64 0xe9468)])              (* [comment removed for export] *)
  ; (0xee600, [C8 (Z_to_bv 64 0xee600)])                                        (* [comment removed for export] *)
  ; (0xee668, [C8 (Z_to_bv 64 0xe2530); C8 (Z_to_bv 64 0xdf420); C8 (Z_to_bv 64 0xe254c)])  (* [comment removed for export] *)
  ; (0xf66d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x18aa3c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x18ad60, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d4d, 10)     (* [comment removed for export] *)
  ; (0x14f26, 4)      (* [comment removed for export] *)
  ; (0x162c0, 128)    (* [comment removed for export] *)
  ; (0x1accd, 33)     (* [comment removed for export] *)
  ; (0x1f5be, 21)     (* [comment removed for export] *)
  ; (0x1f5d3, 23)     (* [comment removed for export] *)
  ; (0x21e40, 128)    (* [comment removed for export] *)
  ; (0x22efb, 7)      (* [comment removed for export] *)
  ; (0x2a2c0, 16)     (* [comment removed for export] *)
  ; (0x61b500, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xee640, 0xee650); (0xf6770, 0xf6778);
    (0x18aae2, 0x18aae3); (0xe9468, 0xe9478); (0xec7a0, 0xec7a8); (0xec878, 0xec888); (0xed508, 0xed518); (0xed528, 0xed538); (0xed5b0, 0xed5c0);
    (0xee600, 0xee608); (0xee668, 0xee680); (0xf66d0, 0xf66d4); (0x18aa3c, 0x18aa3d); (0x18ad60, 0x18ad61) ].

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
