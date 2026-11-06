(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x10ea18, [C8 (Z_to_bv 64 0x1081f4); C8 (Z_to_bv 64 0xfabbc)])
  ; (0x112e30, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x109378, [C8 (Z_to_bv 64 0x9beec); C8 (Z_to_bv 64 0x44764)])
  ; (0x10caf8, [C8 (Z_to_bv 64 0x1112d8)])
  ; (0x10cbd0, [C8 (Z_to_bv 64 0xf4628); C8 (Z_to_bv 64 0)])
  ; (0x10d860, [C8 (Z_to_bv 64 0x10caf8); C8 (Z_to_bv 64 0)])
  ; (0x10d8d8, [C8 (Z_to_bv 64 0x1115d0); C8 (Z_to_bv 64 0x111e90)])
  ; (0x10d998, [C8 (Z_to_bv 64 0x109388); C8 (Z_to_bv 64 0x109378)])
  ; (0x10e9d8, [C8 (Z_to_bv 64 0x10e9d8)])
  ; (0x10ea38, [C8 (Z_to_bv 64 0x1006a4); C8 (Z_to_bv 64 0xfaf18); C8 (Z_to_bv 64 0x1006c0)])
  ; (0x112d90, [C4 (Z_to_bv 64 1)])
  ; (0x112dd8, [C1 (Z_to_bv 8 1)])
  ; (0x1a70fc, [C1 (Z_to_bv 8 1)])
  ; (0x1a7420, [C1 (Z_to_bv 8 0)])
  ; (0x109780, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1097e0); C8 (Z_to_bv 64 0xc59ac); C8 (Z_to_bv 64 0xc5b38); C8 (Z_to_bv 64 0xc5cc4); C8 (Z_to_bv 64 0x9cd44); C8 (Z_to_bv 64 0x9f334); C8 (Z_to_bv 64 0x9f4c4)])
  ; (0x109840, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1098c0); C8 (Z_to_bv 64 0xc5958); C8 (Z_to_bv 64 0x9cfa0); C8 (Z_to_bv 64 0x9f8d8); C8 (Z_to_bv 64 0xb2330); C8 (Z_to_bv 64 0xc4a1c); C8 (Z_to_bv 64 0xc51d0); C8 (Z_to_bv 64 0xc5d0c); C8 (Z_to_bv 64 0xc5e6c); C8 (Z_to_bv 64 0xc5fd4); C8 (Z_to_bv 64 0xc60c0)])
  ; (0x10d878, [C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0)])
  ; (0x10d890, [C8 (Z_to_bv 64 0x2d070)])
  ; (0x10e9f8, [C8 (Z_to_bv 64 0x1029d8); C8 (Z_to_bv 64 0x102908)])
  ; (0x1a71a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10d56, 10)
  ; (0x14e1e, 4)
  ; (0x16191, 17)
  ; (0x16180, 128)
  ; (0x1a9b2, 33)
  ; (0x1f09e, 21)
  ; (0x1f0b3, 23)
  ; (0x21800, 128)
  ; (0x228a4, 7)
  ; (0x228a4, 7)
  ; (0x2e6a8, 16)
  ; (0x637bc0, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x10ea18, 0x10ea28); (0x112e30, 0x112e38);
    (0x109378, 0x109388); (0x10caf8, 0x10cb00); (0x10cbd0, 0x10cbe0); (0x10d860, 0x10d870); (0x10d8d8, 0x10d8e8); (0x10d998, 0x10d9a8);
    (0x10e9d8, 0x10e9e0); (0x10ea38, 0x10ea50); (0x112d90, 0x112d94); (0x112dd8, 0x112dd9); (0x1a70fc, 0x1a70fd); (0x1a7420, 0x1a7421);
    (0x109780, 0x1097c0); (0x109840, 0x1098a0); (0x10d878, 0x10d890); (0x10d890, 0x10d898); (0x10e9f8, 0x10ea08); (0x1a71a6, 0x1a71a8) ].

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

Definition CLI_RO : list (Z * list cell) :=
  [ (0x109780, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1097e0); C8 (Z_to_bv 64 0xc59ac); C8 (Z_to_bv 64 0xc5b38); C8 (Z_to_bv 64 0xc5cc4); C8 (Z_to_bv 64 0x9cd44); C8 (Z_to_bv 64 0x9f334); C8 (Z_to_bv 64 0x9f4c4)])
  ; (0x109840, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1098c0); C8 (Z_to_bv 64 0xc5958); C8 (Z_to_bv 64 0x9cfa0); C8 (Z_to_bv 64 0x9f8d8); C8 (Z_to_bv 64 0xb2330); C8 (Z_to_bv 64 0xc4a1c); C8 (Z_to_bv 64 0xc51d0); C8 (Z_to_bv 64 0xc5d0c); C8 (Z_to_bv 64 0xc5e6c); C8 (Z_to_bv 64 0xc5fd4); C8 (Z_to_bv 64 0xc60c0)])
  ; (0x10d878, [C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0)])
  ; (0x10d890, [C8 (Z_to_bv 64 0x2d070)])
  ; (0x10e9f8, [C8 (Z_to_bv 64 0x1029d8); C8 (Z_to_bv 64 0x102908)])
  ; (0x1a71a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
