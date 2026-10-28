(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x1705c8, [C8 (Z_to_bv 64 0x167814); C8 (Z_to_bv 64 0x158210)])
  ; (0x175470, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x168998, [C8 (Z_to_bv 64 0xb2520); C8 (Z_to_bv 64 0x58498)])
  ; (0x16e668, [C8 (Z_to_bv 64 0x173330)])
  ; (0x16e740, [C8 (Z_to_bv 64 0x14fba4); C8 (Z_to_bv 64 0)])
  ; (0x16f3d8, [C8 (Z_to_bv 64 0x16e668); C8 (Z_to_bv 64 0)])
  ; (0x16f438, [C8 (Z_to_bv 64 0x173630); C8 (Z_to_bv 64 0x1744f0)])
  ; (0x16f538, [C8 (Z_to_bv 64 0x1689a8); C8 (Z_to_bv 64 0x168998)])
  ; (0x170580, [C8 (Z_to_bv 64 0x170580)])
  ; (0x1705f8, [C8 (Z_to_bv 64 0x15e90c); C8 (Z_to_bv 64 0x158628); C8 (Z_to_bv 64 0x15e928)])
  ; (0x1753d0, [C4 (Z_to_bv 64 1)])
  ; (0x175418, [C1 (Z_to_bv 8 1)])
  ; (0x20973c, [C1 (Z_to_bv 8 1)])
  ; (0x209a60, [C1 (Z_to_bv 8 0)])
  ; (0x168f40, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168fa0); C8 (Z_to_bv 64 0xe6fb0); C8 (Z_to_bv 64 0xe7150); C8 (Z_to_bv 64 0xe72f0); C8 (Z_to_bv 64 0xb3470); C8 (Z_to_bv 64 0xb65b0); C8 (Z_to_bv 64 0xb6798)])
  ; (0x169000, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x169080); C8 (Z_to_bv 64 0xe6f5c); C8 (Z_to_bv 64 0xb3710); C8 (Z_to_bv 64 0xb6bec); C8 (Z_to_bv 64 0xce5d4); C8 (Z_to_bv 64 0xe5e6c); C8 (Z_to_bv 64 0xe6710); C8 (Z_to_bv 64 0xe7338); C8 (Z_to_bv 64 0xe74ac); C8 (Z_to_bv 64 0xe7620); C8 (Z_to_bv 64 0xe770c)])
  ; (0x16f428, [C8 (Z_to_bv 64 0x2d450)])
  ; (0x1705a8, [C8 (Z_to_bv 64 0x160de0); C8 (Z_to_bv 64 0x160d10)])
  ; (0x2097e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x168e08, [C8 (Z_to_bv 64 0x111a64); C8 (Z_to_bv 64 0xb0168); C8 (Z_to_bv 64 8)])
  ; (0x16f3f0, [C8 (Z_to_bv 64 0x16c3b0); C8 (Z_to_bv 64 0x16c430)])
  ; (0x16c590, [C8 (Z_to_bv 64 0x138584)])
  ; (0x16f430, [C8 (Z_to_bv 64 0x6aa8e0)])
  ; (0x16bf18, [C8 (Z_to_bv 64 0x16c118); C8 (Z_to_bv 64 0x2d268)])
  ; (0x16c0f0, [C8 (Z_to_bv 64 0x16c168); C8 (Z_to_bv 64 0x2d327)])
  ; (0x16c138, [C8 (Z_to_bv 64 0x109cfc)])
  ; (0x16c150, [C8 (Z_to_bv 64 0x10a060); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c1a8)])
  ; (0x16c190, [C8 (Z_to_bv 64 0x10acd4)])
  ; (0x16c1a0, [C8 (Z_to_bv 64 0x10a0dc); C8 (Z_to_bv 64 0x16c168); C8 (Z_to_bv 64 0x2d349); C8 (Z_to_bv 64 0x16c0f0)])
  ; (0x16e540, [C8 (Z_to_bv 64 0x149a0c); C8 (Z_to_bv 64 0x149a44); C8 (Z_to_bv 64 0x149ae0)])
  ; (0x16e570, [C8 (Z_to_bv 64 0x149c04); C8 (Z_to_bv 64 0x149cec); C8 (Z_to_bv 64 0x149d14)])
  ; (0x16e598, [C8 (Z_to_bv 64 0x149dc0)])
  ; (0x16e718, [C8 (Z_to_bv 64 0x0)])
  ; (0x16f450, [C8 (Z_to_bv 64 0x173290)])
  ; (0x16f458, [C8 (Z_to_bv 64 0x173288)])
  ; (0x1705c0, [C8 (Z_to_bv 64 0x153978)])
  ; (0x16c598, [C8 (Z_to_bv 64 0x13858c)])
  ; (0x16d140, [C8 (Z_to_bv 64 0x11cfa8); C8 (Z_to_bv 64 0x11d254); C8 (Z_to_bv 64 0x11d500); C8 (Z_to_bv 64 0x11d788); C8 (Z_to_bv 64 0x11da10)])
  ; (0x16c728, [C8 (Z_to_bv 64 0x13b770); C8 (Z_to_bv 64 0x13b780); C8 (Z_to_bv 64 0x13b790)])
  ; (0x16f500, [C8 (Z_to_bv 64 0x6aa668)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10ded, 10)
  ; (0x14f66, 4)
  ; (0x162fa, 17)
  ; (0x16300, 128)
  ; (0x1ad48, 33)
  ; (0x1f488, 21)
  ; (0x1f49d, 23)
  ; (0x21c40, 128)
  ; (0x22da5, 7)
  ; (0x22da5, 7)
  ; (0x33a18, 16)
  ; (0x69a200, 16)
  ; (0x13ebe, 19)
  ; (0x149be, 1)
  ; (0x17df9, 3)
  ; (0x1a4a1, 3)
  ; (0x1fece, 3)
  ; (0x20b48, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x1705c8, 0x1705d8); (0x175470, 0x175478);
    (0x168998, 0x1689a8); (0x16e668, 0x16e670); (0x16e740, 0x16e750); (0x16f3d8, 0x16f3e8); (0x16f438, 0x16f448); (0x16f538, 0x16f548);
    (0x170580, 0x170588); (0x1705f8, 0x170610); (0x1753d0, 0x1753d4); (0x175418, 0x175419); (0x20973c, 0x20973d); (0x209a60, 0x209a61);
    (0x168f40, 0x168f80); (0x169000, 0x169060); (0x16f428, 0x16f430); (0x1705a8, 0x1705b8); (0x2097e6, 0x2097e8);
    (0x168e08, 0x168e20); (0x16f3f0, 0x16f400); (0x16c590, 0x16c598); (0x16f430, 0x16f438);
      (0x16bf18, 0x16bf28); (0x16c0f0, 0x16c100); (0x16c138, 0x16c140); (0x16c150, 0x16c168); (0x16c190, 0x16c198); (0x16c1a0, 0x16c1c0); (0x16e540, 0x16e558); (0x16e570, 0x16e588); (0x16e598, 0x16e5a0); (0x16e718, 0x16e720); (0x16f450, 0x16f458); (0x16f458, 0x16f460); (0x1705c0, 0x1705c8);
      (0x16c598, 0x16c5a0); (0x16d140, 0x16d168); (0x16c728, 0x16c740); (0x16f500, 0x16f508) ].

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
  [ (0x168f40, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168fa0); C8 (Z_to_bv 64 0xe6fb0); C8 (Z_to_bv 64 0xe7150); C8 (Z_to_bv 64 0xe72f0); C8 (Z_to_bv 64 0xb3470); C8 (Z_to_bv 64 0xb65b0); C8 (Z_to_bv 64 0xb6798)])
  ; (0x169000, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x169080); C8 (Z_to_bv 64 0xe6f5c); C8 (Z_to_bv 64 0xb3710); C8 (Z_to_bv 64 0xb6bec); C8 (Z_to_bv 64 0xce5d4); C8 (Z_to_bv 64 0xe5e6c); C8 (Z_to_bv 64 0xe6710); C8 (Z_to_bv 64 0xe7338); C8 (Z_to_bv 64 0xe74ac); C8 (Z_to_bv 64 0xe7620); C8 (Z_to_bv 64 0xe770c)])
  ; (0x16f428, [C8 (Z_to_bv 64 0x2d450)])
  ; (0x1705a8, [C8 (Z_to_bv 64 0x160de0); C8 (Z_to_bv 64 0x160d10)])
  ; (0x2097e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x168e08, [C8 (Z_to_bv 64 0x111a64); C8 (Z_to_bv 64 0xb0168); C8 (Z_to_bv 64 8)])
  ; (0x16f3f0, [C8 (Z_to_bv 64 0x16c3b0); C8 (Z_to_bv 64 0x16c430)])
  ; (0x16c590, [C8 (Z_to_bv 64 0x138584)])
  ; (0x16f430, [C8 (Z_to_bv 64 0x6aa8e0)])
  ; (0x16bf18, [C8 (Z_to_bv 64 0x16c118); C8 (Z_to_bv 64 0x2d268)])
  ; (0x16c0f0, [C8 (Z_to_bv 64 0x16c168); C8 (Z_to_bv 64 0x2d327)])
  ; (0x16c138, [C8 (Z_to_bv 64 0x109cfc)])
  ; (0x16c150, [C8 (Z_to_bv 64 0x10a060); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c1a8)])
  ; (0x16c190, [C8 (Z_to_bv 64 0x10acd4)])
  ; (0x16c1a0, [C8 (Z_to_bv 64 0x10a0dc); C8 (Z_to_bv 64 0x16c168); C8 (Z_to_bv 64 0x2d349); C8 (Z_to_bv 64 0x16c0f0)])
  ; (0x16e540, [C8 (Z_to_bv 64 0x149a0c); C8 (Z_to_bv 64 0x149a44); C8 (Z_to_bv 64 0x149ae0)])
  ; (0x16e570, [C8 (Z_to_bv 64 0x149c04); C8 (Z_to_bv 64 0x149cec); C8 (Z_to_bv 64 0x149d14)])
  ; (0x16e598, [C8 (Z_to_bv 64 0x149dc0)])
  ; (0x16e718, [C8 (Z_to_bv 64 0x0)])
  ; (0x16f450, [C8 (Z_to_bv 64 0x173290)])
  ; (0x16f458, [C8 (Z_to_bv 64 0x173288)])
  ; (0x1705c0, [C8 (Z_to_bv 64 0x153978)])
  ; (0x16c598, [C8 (Z_to_bv 64 0x13858c)])
  ; (0x16d140, [C8 (Z_to_bv 64 0x11cfa8); C8 (Z_to_bv 64 0x11d254); C8 (Z_to_bv 64 0x11d500); C8 (Z_to_bv 64 0x11d788); C8 (Z_to_bv 64 0x11da10)])
  ; (0x16c728, [C8 (Z_to_bv 64 0x13b770); C8 (Z_to_bv 64 0x13b780); C8 (Z_to_bv 64 0x13b790)])
  ; (0x16f500, [C8 (Z_to_bv 64 0x6aa668)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
