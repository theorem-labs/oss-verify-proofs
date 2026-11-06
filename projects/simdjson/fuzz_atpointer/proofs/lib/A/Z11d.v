(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x10cfe0, [C8 (Z_to_bv 64 0x1067d4); C8 (Z_to_bv 64 0xf919c)])
  ; (0x1113f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x107958, [C8 (Z_to_bv 64 0x9a0f0); C8 (Z_to_bv 64 0x44780)])
  ; (0x10b0d8, [C8 (Z_to_bv 64 0x10f8a0)])
  ; (0x10b1b0, [C8 (Z_to_bv 64 0xf2c08); C8 (Z_to_bv 64 0)])
  ; (0x10be40, [C8 (Z_to_bv 64 0x10b0d8); C8 (Z_to_bv 64 0)])
  ; (0x10bea0, [C8 (Z_to_bv 64 0x10fba0); C8 (Z_to_bv 64 0x110460)])
  ; (0x10bf60, [C8 (Z_to_bv 64 0x107968); C8 (Z_to_bv 64 0x107958)])
  ; (0x10cfa0, [C8 (Z_to_bv 64 0x10cfa0)])
  ; (0x10d000, [C8 (Z_to_bv 64 0xfec84); C8 (Z_to_bv 64 0xf94f8); C8 (Z_to_bv 64 0xfeca0)])
  ; (0x111350, [C4 (Z_to_bv 64 1)])
  ; (0x111398, [C1 (Z_to_bv 8 1)])
  ; (0x1a56bc, [C1 (Z_to_bv 8 1)])
  ; (0x1a59e0, [C1 (Z_to_bv 8 0)])
  ; (0x107d60, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x107dc0); C8 (Z_to_bv 64 0xc3b1c); C8 (Z_to_bv 64 0xc3ca8); C8 (Z_to_bv 64 0xc3e34); C8 (Z_to_bv 64 0x9aeb4); C8 (Z_to_bv 64 0x9d4a4); C8 (Z_to_bv 64 0x9d634)])
  ; (0x107e20, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x107ea0); C8 (Z_to_bv 64 0xc3ac8); C8 (Z_to_bv 64 0x9b110); C8 (Z_to_bv 64 0x9da48); C8 (Z_to_bv 64 0xb04a0); C8 (Z_to_bv 64 0xc2b8c); C8 (Z_to_bv 64 0xc3340); C8 (Z_to_bv 64 0xc3e7c); C8 (Z_to_bv 64 0xc3fdc); C8 (Z_to_bv 64 0xc4144); C8 (Z_to_bv 64 0xc4230)])
  ; (0x10be58, [C8 (Z_to_bv 64 0x2cd70)])
  ; (0x10cfc0, [C8 (Z_to_bv 64 0x100fb8); C8 (Z_to_bv 64 0x100ee8)])
  ; (0x1a5766, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10d2e, 10)
  ; (0x14e10, 4)
  ; (0x1618a, 17)
  ; (0x16180, 128)
  ; (0x1a977, 33)
  ; (0x1f056, 21)
  ; (0x1f06b, 23)
  ; (0x21740, 128)
  ; (0x2281a, 7)
  ; (0x2281a, 7)
  ; (0x2e3a8, 16)
  ; (0x636180, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x10cfe0, 0x10cff0); (0x1113f0, 0x1113f8);
    (0x107958, 0x107968); (0x10b0d8, 0x10b0e0); (0x10b1b0, 0x10b1c0); (0x10be40, 0x10be50); (0x10bea0, 0x10beb0); (0x10bf60, 0x10bf70);
    (0x10cfa0, 0x10cfa8); (0x10d000, 0x10d018); (0x111350, 0x111354); (0x111398, 0x111399); (0x1a56bc, 0x1a56bd); (0x1a59e0, 0x1a59e1);
    (0x107d60, 0x107da0); (0x107e20, 0x107e80); (0x10be58, 0x10be60); (0x10cfc0, 0x10cfd0); (0x1a5766, 0x1a5768) ].

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
  [ (0x107d60, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x107dc0); C8 (Z_to_bv 64 0xc3b1c); C8 (Z_to_bv 64 0xc3ca8); C8 (Z_to_bv 64 0xc3e34); C8 (Z_to_bv 64 0x9aeb4); C8 (Z_to_bv 64 0x9d4a4); C8 (Z_to_bv 64 0x9d634)])
  ; (0x107e20, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x107ea0); C8 (Z_to_bv 64 0xc3ac8); C8 (Z_to_bv 64 0x9b110); C8 (Z_to_bv 64 0x9da48); C8 (Z_to_bv 64 0xb04a0); C8 (Z_to_bv 64 0xc2b8c); C8 (Z_to_bv 64 0xc3340); C8 (Z_to_bv 64 0xc3e7c); C8 (Z_to_bv 64 0xc3fdc); C8 (Z_to_bv 64 0xc4144); C8 (Z_to_bv 64 0xc4230)])
  ; (0x10be58, [C8 (Z_to_bv 64 0x2cd70)])
  ; (0x10cfc0, [C8 (Z_to_bv 64 0x100fb8); C8 (Z_to_bv 64 0x100ee8)])
  ; (0x1a5766, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
