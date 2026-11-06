(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xed780, [C8 (Z_to_bv 64 0xe741c); C8 (Z_to_bv 64 0xdbe04)])              (* [comment removed for export] *)
  ; (0xf4ef0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x189265, [C1 (Z_to_bv 8 1)])    (* [comment removed for export] *)
  ; (0xed758, [C8 (Z_to_bv 64 0xe2214)])    (* [comment removed for export] *)
  ; (0xe85a0, [C8 (Z_to_bv 64 0x90d30); C8 (Z_to_bv 64 0x3f1b8)])              (* [comment removed for export] *)
  ; (0xeb8d8, [C8 (Z_to_bv 64 0xf00c8)])                                        (* [comment removed for export] *)
  ; (0xeb9b0, [C8 (Z_to_bv 64 0xd59a8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xec640, [C8 (Z_to_bv 64 0xeb8d8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xec660, [C8 (Z_to_bv 64 0xf03c0); C8 (Z_to_bv 64 0xf3f80)])              (* [comment removed for export] *)
  ; (0xec6e8, [C8 (Z_to_bv 64 0xe85b0); C8 (Z_to_bv 64 0xe85a0)])              (* [comment removed for export] *)
  ; (0xed740, [C8 (Z_to_bv 64 0xed740)])                                        (* [comment removed for export] *)
  ; (0xed7a8, [C8 (Z_to_bv 64 0xe15b8); C8 (Z_to_bv 64 0xdc038); C8 (Z_to_bv 64 0xe15d4)])  (* [comment removed for export] *)
  ; (0xf4e50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1891bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1894e0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d84, 10)     (* [comment removed for export] *)
  ; (0x14f49, 4)      (* [comment removed for export] *)
  ; (0x16340, 128)    (* [comment removed for export] *)
  ; (0x1acb5, 33)     (* [comment removed for export] *)
  ; (0x1f64f, 21)     (* [comment removed for export] *)
  ; (0x1f664, 23)     (* [comment removed for export] *)
  ; (0x21e00, 128)    (* [comment removed for export] *)
  ; (0x22e5e, 7)      (* [comment removed for export] *)
  ; (0x239d8, 16)     (* [comment removed for export] *)
  ; (0x619c80, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xed780, 0xed790); (0xf4ef0, 0xf4ef8);
    (0x189265, 0x189266); (0xed758, 0xed760); (0xe85a0, 0xe85b0); (0xeb8d8, 0xeb8e0); (0xeb9b0, 0xeb9c0); (0xec640, 0xec650); (0xec660, 0xec670); (0xec6e8, 0xec6f8);
    (0xed740, 0xed748); (0xed7a8, 0xed7c0); (0xf4e50, 0xf4e54); (0x1891bc, 0x1891bd); (0x1894e0, 0x1894e1) ].

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
