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
  [ (0x11cba0, [C8 (Z_to_bv 64 0x116384); C8 (Z_to_bv 64 0x108d4c)])
  ; (0x1213b0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x117508, [C8 (Z_to_bv 64 0x9e74c); C8 (Z_to_bv 64 0x44700)])
  ; (0x11ac78, [C8 (Z_to_bv 64 0x11f828)])
  ; (0x11ad50, [C8 (Z_to_bv 64 0x1027b8); C8 (Z_to_bv 64 0)])
  ; (0x11b9e0, [C8 (Z_to_bv 64 0x11ac78); C8 (Z_to_bv 64 0)])
  ; (0x11ba60, [C8 (Z_to_bv 64 0x11fb20); C8 (Z_to_bv 64 0x120420)])
  ; (0x11bb20, [C8 (Z_to_bv 64 0x117518); C8 (Z_to_bv 64 0x117508)])
  ; (0x11cb60, [C8 (Z_to_bv 64 0x11cb60)])
  ; (0x11cbc0, [C8 (Z_to_bv 64 0x10e834); C8 (Z_to_bv 64 0x1090a8); C8 (Z_to_bv 64 0x10e850)])
  ; (0x121310, [C4 (Z_to_bv 64 1)])
  ; (0x121358, [C1 (Z_to_bv 8 1)])
  ; (0x1b567c, [C1 (Z_to_bv 8 1)])
  ; (0x1b59a0, [C1 (Z_to_bv 8 0)])
  ; (0x117900, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x117960); C8 (Z_to_bv 64 0xd3288); C8 (Z_to_bv 64 0xd3428); C8 (Z_to_bv 64 0xd35c8); C8 (Z_to_bv 64 0x9f748); C8 (Z_to_bv 64 0xa2888); C8 (Z_to_bv 64 0xa2a70)])
  ; (0x1179c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x117a40); C8 (Z_to_bv 64 0xd3234); C8 (Z_to_bv 64 0x9f9e8); C8 (Z_to_bv 64 0xa2ec4); C8 (Z_to_bv 64 0xba8ac); C8 (Z_to_bv 64 0xd2144); C8 (Z_to_bv 64 0xd29e8); C8 (Z_to_bv 64 0xd3610); C8 (Z_to_bv 64 0xd3784); C8 (Z_to_bv 64 0xd38f8); C8 (Z_to_bv 64 0xd39e4)])
  ; (0x11b9f8, [C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40)])
  ; (0x11ba18, [C8 (Z_to_bv 64 0x2cd30)])
  ; (0x11cb80, [C8 (Z_to_bv 64 0x110b68); C8 (Z_to_bv 64 0x110a98)])
  ; (0x1b5726, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10d71, 10)
  ; (0x14e42, 4)
  ; (0x161b5, 17)
  ; (0x161c0, 128)
  ; (0x1a9dd, 33)
  ; (0x1f01c, 21)
  ; (0x1f031, 23)
  ; (0x21800, 128)
  ; (0x22919, 7)
  ; (0x22919, 7)
  ; (0x2e368, 16)
  ; (0x646140, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x11cba0, 0x11cbb0); (0x1213b0, 0x1213b8);
    (0x117508, 0x117518); (0x11ac78, 0x11ac80); (0x11ad50, 0x11ad60); (0x11b9e0, 0x11b9f0); (0x11ba60, 0x11ba70); (0x11bb20, 0x11bb30);
    (0x11cb60, 0x11cb68); (0x11cbc0, 0x11cbd8); (0x121310, 0x121314); (0x121358, 0x121359); (0x1b567c, 0x1b567d); (0x1b59a0, 0x1b59a1);
    (0x117900, 0x117940); (0x1179c0, 0x117a20); (0x11b9f8, 0x11ba18); (0x11ba18, 0x11ba20); (0x11cb80, 0x11cb90); (0x1b5726, 0x1b5728) ].

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
  [ (0x117900, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x117960); C8 (Z_to_bv 64 0xd3288); C8 (Z_to_bv 64 0xd3428); C8 (Z_to_bv 64 0xd35c8); C8 (Z_to_bv 64 0x9f748); C8 (Z_to_bv 64 0xa2888); C8 (Z_to_bv 64 0xa2a70)])
  ; (0x1179c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x117a40); C8 (Z_to_bv 64 0xd3234); C8 (Z_to_bv 64 0x9f9e8); C8 (Z_to_bv 64 0xa2ec4); C8 (Z_to_bv 64 0xba8ac); C8 (Z_to_bv 64 0xd2144); C8 (Z_to_bv 64 0xd29e8); C8 (Z_to_bv 64 0xd3610); C8 (Z_to_bv 64 0xd3784); C8 (Z_to_bv 64 0xd38f8); C8 (Z_to_bv 64 0xd39e4)])
  ; (0x11b9f8, [C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40)])
  ; (0x11ba18, [C8 (Z_to_bv 64 0x2cd30)])
  ; (0x11cb80, [C8 (Z_to_bv 64 0x110b68); C8 (Z_to_bv 64 0x110a98)])
  ; (0x1b5726, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
