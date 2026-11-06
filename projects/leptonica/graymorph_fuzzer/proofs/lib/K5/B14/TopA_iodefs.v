(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xec660, [C8 (Z_to_bv 64 0xe6314); C8 (Z_to_bv 64 0xdd218)])              (* [comment removed for export] *)
  ; (0xf39b0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xe7498, [C8 (Z_to_bv 64 0x90a20); C8 (Z_to_bv 64 0x3edb8)])              (* [comment removed for export] *)
  ; (0xea7d0, [C8 (Z_to_bv 64 0xeefa8)])                                        (* [comment removed for export] *)
  ; (0xea8a8, [C8 (Z_to_bv 64 0xd7060); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xeb538, [C8 (Z_to_bv 64 0xea7d0); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xeb558, [C8 (Z_to_bv 64 0xef2a0); C8 (Z_to_bv 64 0xf2a20)])              (* [comment removed for export] *)
  ; (0xeb5e0, [C8 (Z_to_bv 64 0xe74a8); C8 (Z_to_bv 64 0xe7498)])              (* [comment removed for export] *)
  ; (0xec620, [C8 (Z_to_bv 64 0xec620)])                                        (* [comment removed for export] *)
  ; (0xec688, [C8 (Z_to_bv 64 0xe055c); C8 (Z_to_bv 64 0xdd44c); C8 (Z_to_bv 64 0xe0578)])  (* [comment removed for export] *)
  ; (0xf3910, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x187c7c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x187fa0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d3d, 10)     (* [comment removed for export] *)
  ; (0x14f3b, 4)      (* [comment removed for export] *)
  ; (0x162c0, 128)    (* [comment removed for export] *)
  ; (0x1ad4b, 33)     (* [comment removed for export] *)
  ; (0x1f649, 21)     (* [comment removed for export] *)
  ; (0x1f65e, 23)     (* [comment removed for export] *)
  ; (0x21f00, 128)    (* [comment removed for export] *)
  ; (0x22f6a, 7)      (* [comment removed for export] *)
  ; (0x29b78, 16)     (* [comment removed for export] *)
  ; (0x618740, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xec660, 0xec670); (0xf39b0, 0xf39b8);
    (0xe7498, 0xe74a8); (0xea7d0, 0xea7d8); (0xea8a8, 0xea8b8); (0xeb538, 0xeb548); (0xeb558, 0xeb568); (0xeb5e0, 0xeb5f0);
    (0xec620, 0xec628); (0xec688, 0xec6a0); (0xf3910, 0xf3914); (0x187c7c, 0x187c7d); (0x187fa0, 0x187fa1) ].

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
