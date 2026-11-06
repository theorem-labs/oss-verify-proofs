(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xe3da0, [C8 (Z_to_bv 64 0xdda4c); C8 (Z_to_bv 64 0xd4950)])              (* [comment removed for export] *)
  ; (0xeb0b0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xdebd0, [C8 (Z_to_bv 64 0x9096c); C8 (Z_to_bv 64 0x3ed04)])              (* [comment removed for export] *)
  ; (0xe1f08, [C8 (Z_to_bv 64 0xe66e8)])                                        (* [comment removed for export] *)
  ; (0xe1fe0, [C8 (Z_to_bv 64 0xce798); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe2c70, [C8 (Z_to_bv 64 0xe1f08); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe2c90, [C8 (Z_to_bv 64 0xe69e0); C8 (Z_to_bv 64 0xea120)])              (* [comment removed for export] *)
  ; (0xe2d18, [C8 (Z_to_bv 64 0xdebe0); C8 (Z_to_bv 64 0xdebd0)])              (* [comment removed for export] *)
  ; (0xe3d60, [C8 (Z_to_bv 64 0xe3d60)])                                        (* [comment removed for export] *)
  ; (0xe3dc8, [C8 (Z_to_bv 64 0xd7c94); C8 (Z_to_bv 64 0xd4b84); C8 (Z_to_bv 64 0xd7cb0)])  (* [comment removed for export] *)
  ; (0xeb010, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x17f37c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x17f6a0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d25, 10)     (* [comment removed for export] *)
  ; (0x14f1b, 4)      (* [comment removed for export] *)
  ; (0x16280, 128)    (* [comment removed for export] *)
  ; (0x1ad2b, 33)     (* [comment removed for export] *)
  ; (0x1f629, 21)     (* [comment removed for export] *)
  ; (0x1f63e, 23)     (* [comment removed for export] *)
  ; (0x21ec0, 128)    (* [comment removed for export] *)
  ; (0x22f4a, 7)      (* [comment removed for export] *)
  ; (0x29b18, 16)     (* [comment removed for export] *)
  ; (0x60fe40, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xe3da0, 0xe3db0); (0xeb0b0, 0xeb0b8);
    (0xdebd0, 0xdebe0); (0xe1f08, 0xe1f10); (0xe1fe0, 0xe1ff0); (0xe2c70, 0xe2c80); (0xe2c90, 0xe2ca0); (0xe2d18, 0xe2d28);
    (0xe3d60, 0xe3d68); (0xe3dc8, 0xe3de0); (0xeb010, 0xeb014); (0x17f37c, 0x17f37d); (0x17f6a0, 0x17f6a1) ].

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
