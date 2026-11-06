(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x163d60, [C8 (Z_to_bv 64 0x15afb8); C8 (Z_to_bv 64 0x14b9b4)])
  ; (0x1682f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x15c138, [C8 (Z_to_bv 64 0xb17e4); C8 (Z_to_bv 64 0x57fdc)])
  ; (0x161e08, [C8 (Z_to_bv 64 0x1666f8)])
  ; (0x161ee0, [C8 (Z_to_bv 64 0x143348); C8 (Z_to_bv 64 0)])
  ; (0x162b78, [C8 (Z_to_bv 64 0x161e08); C8 (Z_to_bv 64 0)])
  ; (0x162bd8, [C8 (Z_to_bv 64 0x1669f0); C8 (Z_to_bv 64 0x167370)])
  ; (0x162cd8, [C8 (Z_to_bv 64 0x15c148); C8 (Z_to_bv 64 0x15c138)])
  ; (0x163d18, [C8 (Z_to_bv 64 0x163d18)])
  ; (0x163d90, [C8 (Z_to_bv 64 0x1520b0); C8 (Z_to_bv 64 0x14bdcc); C8 (Z_to_bv 64 0x1520cc)])
  ; (0x168250, [C4 (Z_to_bv 64 1)])
  ; (0x168298, [C1 (Z_to_bv 8 1)])
  ; (0x1fc5bc, [C1 (Z_to_bv 8 1)])
  ; (0x1fc8e0, [C1 (Z_to_bv 8 0)])
  ; (0x15c6e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15c740); C8 (Z_to_bv 64 0xdb210); C8 (Z_to_bv 64 0xdb39c); C8 (Z_to_bv 64 0xdb528); C8 (Z_to_bv 64 0xb25a8); C8 (Z_to_bv 64 0xb4b98); C8 (Z_to_bv 64 0xb4d28)])
  ; (0x15c7a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15c820); C8 (Z_to_bv 64 0xdb1bc); C8 (Z_to_bv 64 0xb2804); C8 (Z_to_bv 64 0xb513c); C8 (Z_to_bv 64 0xc7b94); C8 (Z_to_bv 64 0xda280); C8 (Z_to_bv 64 0xdaa34); C8 (Z_to_bv 64 0xdb570); C8 (Z_to_bv 64 0xdb6d0); C8 (Z_to_bv 64 0xdb838); C8 (Z_to_bv 64 0xdb924)])
  ; (0x162bc8, [C8 (Z_to_bv 64 0x2d268)])
  ; (0x163d40, [C8 (Z_to_bv 64 0x154584); C8 (Z_to_bv 64 0x1544b4)])
  ; (0x1fc666, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x15c5a8, [C8 (Z_to_bv 64 0x105410); C8 (Z_to_bv 64 0xb07e8); C8 (Z_to_bv 64 8)])
  ; (0x162b90, [C8 (Z_to_bv 64 0x15fb50); C8 (Z_to_bv 64 0x15fbd0)])
  ; (0x15fd30, [C8 (Z_to_bv 64 0x12bd28)])
  ; (0x162bd0, [C8 (Z_to_bv 64 0x69d760)])
  ; (0x15f6b8, [C8 (Z_to_bv 64 0x15f8b8); C8 (Z_to_bv 64 0x2d080)])
  ; (0x15f890, [C8 (Z_to_bv 64 0x15f908); C8 (Z_to_bv 64 0x2d13f)])
  ; (0x15f8d8, [C8 (Z_to_bv 64 0xfd6a8)])
  ; (0x15f8f0, [C8 (Z_to_bv 64 0xfda0c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15f948)])
  ; (0x15f930, [C8 (Z_to_bv 64 0xfe680)])
  ; (0x15f940, [C8 (Z_to_bv 64 0xfda88); C8 (Z_to_bv 64 0x15f908); C8 (Z_to_bv 64 0x2d161); C8 (Z_to_bv 64 0x15f890)])
  ; (0x161ce0, [C8 (Z_to_bv 64 0x13d1b0); C8 (Z_to_bv 64 0x13d1e8); C8 (Z_to_bv 64 0x13d284)])
  ; (0x161d10, [C8 (Z_to_bv 64 0x13d3a8); C8 (Z_to_bv 64 0x13d490); C8 (Z_to_bv 64 0x13d4b8)])
  ; (0x161d38, [C8 (Z_to_bv 64 0x13d564)])
  ; (0x161eb8, [C8 (Z_to_bv 64 0x0)])
  ; (0x162bf0, [C8 (Z_to_bv 64 0x166658)])
  ; (0x162bf8, [C8 (Z_to_bv 64 0x166650)])
  ; (0x163d58, [C8 (Z_to_bv 64 0x14711c)])
  ; (0x15fd38, [C8 (Z_to_bv 64 0x12bd30)])
  ; (0x1608d8, [C8 (Z_to_bv 64 0x1104b4)])
  ; (0x1608e0, [C8 (Z_to_bv 64 0x11074c); C8 (Z_to_bv 64 0x1109f8); C8 (Z_to_bv 64 0x110ca4); C8 (Z_to_bv 64 0x110f2c); C8 (Z_to_bv 64 0x1111b4)])
  ; (0x15fec8, [C8 (Z_to_bv 64 0x12ef14); C8 (Z_to_bv 64 0x12ef24); C8 (Z_to_bv 64 0x12ef34)])
  ; (0x162ca0, [C8 (Z_to_bv 64 0x69d4e8)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10dc1, 10)
  ; (0x14f28, 4)
  ; (0x162ab, 17)
  ; (0x16280, 128)
  ; (0x1abfb, 33)
  ; (0x1f459, 21)
  ; (0x1f46e, 23)
  ; (0x21b80, 128)
  ; (0x22c75, 7)
  ; (0x22c75, 7)
  ; (0x33830, 16)
  ; (0x68d080, 16)
  ; (0x13e80, 19)
  ; (0x14980, 1)
  ; (0x17d80, 3)
  ; (0x1a354, 3)
  ; (0x1fe16, 3)
  ; (0x20a8f, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x163d60, 0x163d70); (0x1682f0, 0x1682f8);
    (0x15c138, 0x15c148); (0x161e08, 0x161e10); (0x161ee0, 0x161ef0); (0x162b78, 0x162b88); (0x162bd8, 0x162be8); (0x162cd8, 0x162ce8);
    (0x163d18, 0x163d20); (0x163d90, 0x163da8); (0x168250, 0x168254); (0x168298, 0x168299); (0x1fc5bc, 0x1fc5bd); (0x1fc8e0, 0x1fc8e1);
    (0x15c6e0, 0x15c720); (0x15c7a0, 0x15c800); (0x162bc8, 0x162bd0); (0x163d40, 0x163d50); (0x1fc666, 0x1fc668);
    (0x15c5a8, 0x15c5c0); (0x162b90, 0x162ba0); (0x15fd30, 0x15fd38); (0x162bd0, 0x162bd8);
      (0x15f6b8, 0x15f6c8); (0x15f890, 0x15f8a0); (0x15f8d8, 0x15f8e0); (0x15f8f0, 0x15f908); (0x15f930, 0x15f938); (0x15f940, 0x15f960); (0x161ce0, 0x161cf8); (0x161d10, 0x161d28); (0x161d38, 0x161d40); (0x161eb8, 0x161ec0); (0x162bf0, 0x162bf8); (0x162bf8, 0x162c00); (0x163d58, 0x163d60);
      (0x15fd38, 0x15fd40);   (0x1608d8, 0x1608e0); (0x1608e0, 0x160908); (0x15fec8, 0x15fee0); (0x162ca0, 0x162ca8) ].

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
  [ (0x15c6e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15c740); C8 (Z_to_bv 64 0xdb210); C8 (Z_to_bv 64 0xdb39c); C8 (Z_to_bv 64 0xdb528); C8 (Z_to_bv 64 0xb25a8); C8 (Z_to_bv 64 0xb4b98); C8 (Z_to_bv 64 0xb4d28)])
  ; (0x15c7a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15c820); C8 (Z_to_bv 64 0xdb1bc); C8 (Z_to_bv 64 0xb2804); C8 (Z_to_bv 64 0xb513c); C8 (Z_to_bv 64 0xc7b94); C8 (Z_to_bv 64 0xda280); C8 (Z_to_bv 64 0xdaa34); C8 (Z_to_bv 64 0xdb570); C8 (Z_to_bv 64 0xdb6d0); C8 (Z_to_bv 64 0xdb838); C8 (Z_to_bv 64 0xdb924)])
  ; (0x162bc8, [C8 (Z_to_bv 64 0x2d268)])
  ; (0x163d40, [C8 (Z_to_bv 64 0x154584); C8 (Z_to_bv 64 0x1544b4)])
  ; (0x1fc666, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x15c5a8, [C8 (Z_to_bv 64 0x105410); C8 (Z_to_bv 64 0xb07e8); C8 (Z_to_bv 64 8)])
  ; (0x162b90, [C8 (Z_to_bv 64 0x15fb50); C8 (Z_to_bv 64 0x15fbd0)])
  ; (0x15fd30, [C8 (Z_to_bv 64 0x12bd28)])
  ; (0x162bd0, [C8 (Z_to_bv 64 0x69d760)])
  ; (0x15f6b8, [C8 (Z_to_bv 64 0x15f8b8); C8 (Z_to_bv 64 0x2d080)])
  ; (0x15f890, [C8 (Z_to_bv 64 0x15f908); C8 (Z_to_bv 64 0x2d13f)])
  ; (0x15f8d8, [C8 (Z_to_bv 64 0xfd6a8)])
  ; (0x15f8f0, [C8 (Z_to_bv 64 0xfda0c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15f948)])
  ; (0x15f930, [C8 (Z_to_bv 64 0xfe680)])
  ; (0x15f940, [C8 (Z_to_bv 64 0xfda88); C8 (Z_to_bv 64 0x15f908); C8 (Z_to_bv 64 0x2d161); C8 (Z_to_bv 64 0x15f890)])
  ; (0x161ce0, [C8 (Z_to_bv 64 0x13d1b0); C8 (Z_to_bv 64 0x13d1e8); C8 (Z_to_bv 64 0x13d284)])
  ; (0x161d10, [C8 (Z_to_bv 64 0x13d3a8); C8 (Z_to_bv 64 0x13d490); C8 (Z_to_bv 64 0x13d4b8)])
  ; (0x161d38, [C8 (Z_to_bv 64 0x13d564)])
  ; (0x161eb8, [C8 (Z_to_bv 64 0x0)])
  ; (0x162bf0, [C8 (Z_to_bv 64 0x166658)])
  ; (0x162bf8, [C8 (Z_to_bv 64 0x166650)])
  ; (0x163d58, [C8 (Z_to_bv 64 0x14711c)])
  ; (0x15fd38, [C8 (Z_to_bv 64 0x12bd30)])
  ; (0x1608d8, [C8 (Z_to_bv 64 0x1104b4)])
  ; (0x1608e0, [C8 (Z_to_bv 64 0x11074c); C8 (Z_to_bv 64 0x1109f8); C8 (Z_to_bv 64 0x110ca4); C8 (Z_to_bv 64 0x110f2c); C8 (Z_to_bv 64 0x1111b4)])
  ; (0x15fec8, [C8 (Z_to_bv 64 0x12ef14); C8 (Z_to_bv 64 0x12ef24); C8 (Z_to_bv 64 0x12ef34)])
  ; (0x162ca0, [C8 (Z_to_bv 64 0x69d4e8)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
