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
  [ (0x119960, [C8 (Z_to_bv 64 0x113154); C8 (Z_to_bv 64 0x105b1c)])
  ; (0x11e170, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x1142d8, [C8 (Z_to_bv 64 0x9b158); C8 (Z_to_bv 64 0x44880)])
  ; (0x117a58, [C8 (Z_to_bv 64 0x11c5e8)])
  ; (0x117b30, [C8 (Z_to_bv 64 0xff588); C8 (Z_to_bv 64 0)])
  ; (0x1187c0, [C8 (Z_to_bv 64 0x117a58); C8 (Z_to_bv 64 0)])
  ; (0x118820, [C8 (Z_to_bv 64 0x11c8e0); C8 (Z_to_bv 64 0x11d1e0)])
  ; (0x1188e0, [C8 (Z_to_bv 64 0x1142e8); C8 (Z_to_bv 64 0x1142d8)])
  ; (0x119920, [C8 (Z_to_bv 64 0x119920)])
  ; (0x119980, [C8 (Z_to_bv 64 0x10b604); C8 (Z_to_bv 64 0x105e78); C8 (Z_to_bv 64 0x10b620)])
  ; (0x11e0d0, [C4 (Z_to_bv 64 1)])
  ; (0x11e118, [C1 (Z_to_bv 8 1)])
  ; (0x1b243c, [C1 (Z_to_bv 8 1)])
  ; (0x1b2760, [C1 (Z_to_bv 8 0)])
  ; (0x1146e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x114740); C8 (Z_to_bv 64 0xcfbe8); C8 (Z_to_bv 64 0xcfd88); C8 (Z_to_bv 64 0xcff28); C8 (Z_to_bv 64 0x9c0a8); C8 (Z_to_bv 64 0x9f1e8); C8 (Z_to_bv 64 0x9f3d0)])
  ; (0x1147a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x114820); C8 (Z_to_bv 64 0xcfb94); C8 (Z_to_bv 64 0x9c348); C8 (Z_to_bv 64 0x9f824); C8 (Z_to_bv 64 0xb720c); C8 (Z_to_bv 64 0xceaa4); C8 (Z_to_bv 64 0xcf348); C8 (Z_to_bv 64 0xcff70); C8 (Z_to_bv 64 0xd00e4); C8 (Z_to_bv 64 0xd0258); C8 (Z_to_bv 64 0xd0344)])
  ; (0x1187d8, [C8 (Z_to_bv 64 0x2ca50)])
  ; (0x119940, [C8 (Z_to_bv 64 0x10d938); C8 (Z_to_bv 64 0x10d868)])
  ; (0x1b24e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10d51, 10)
  ; (0x14e33, 4)
  ; (0x161ae, 17)
  ; (0x16180, 128)
  ; (0x1a9a9, 33)
  ; (0x1efdb, 21)
  ; (0x1eff0, 23)
  ; (0x21740, 128)
  ; (0x2288e, 7)
  ; (0x2288e, 7)
  ; (0x2e088, 16)
  ; (0x642f00, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x119960, 0x119970); (0x11e170, 0x11e178);
    (0x1142d8, 0x1142e8); (0x117a58, 0x117a60); (0x117b30, 0x117b40); (0x1187c0, 0x1187d0); (0x118820, 0x118830); (0x1188e0, 0x1188f0);
    (0x119920, 0x119928); (0x119980, 0x119998); (0x11e0d0, 0x11e0d4); (0x11e118, 0x11e119); (0x1b243c, 0x1b243d); (0x1b2760, 0x1b2761);
    (0x1146e0, 0x114720); (0x1147a0, 0x114800); (0x1187d8, 0x1187e0); (0x119940, 0x119950); (0x1b24e6, 0x1b24e8) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).

Definition CLI_RO : list (Z * list cell) :=
  [ (0x1146e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x114740); C8 (Z_to_bv 64 0xcfbe8); C8 (Z_to_bv 64 0xcfd88); C8 (Z_to_bv 64 0xcff28); C8 (Z_to_bv 64 0x9c0a8); C8 (Z_to_bv 64 0x9f1e8); C8 (Z_to_bv 64 0x9f3d0)])
  ; (0x1147a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x114820); C8 (Z_to_bv 64 0xcfb94); C8 (Z_to_bv 64 0x9c348); C8 (Z_to_bv 64 0x9f824); C8 (Z_to_bv 64 0xb720c); C8 (Z_to_bv 64 0xceaa4); C8 (Z_to_bv 64 0xcf348); C8 (Z_to_bv 64 0xcff70); C8 (Z_to_bv 64 0xd00e4); C8 (Z_to_bv 64 0xd0258); C8 (Z_to_bv 64 0xd0344)])
  ; (0x1187d8, [C8 (Z_to_bv 64 0x2ca50)])
  ; (0x119940, [C8 (Z_to_bv 64 0x10d938); C8 (Z_to_bv 64 0x10d868)])
  ; (0x1b24e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
