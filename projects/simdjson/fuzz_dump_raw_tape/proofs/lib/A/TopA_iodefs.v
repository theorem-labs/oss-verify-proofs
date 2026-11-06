(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x164c60, [C8 (Z_to_bv 64 0x15beac); C8 (Z_to_bv 64 0x14c8a8)])
  ; (0x1696f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x15d030, [C8 (Z_to_bv 64 0xb24d0); C8 (Z_to_bv 64 0x586d4)])
  ; (0x162d08, [C8 (Z_to_bv 64 0x1675f8)])
  ; (0x162de0, [C8 (Z_to_bv 64 0x14423c); C8 (Z_to_bv 64 0)])
  ; (0x163a78, [C8 (Z_to_bv 64 0x162d08); C8 (Z_to_bv 64 0)])
  ; (0x163ad8, [C8 (Z_to_bv 64 0x1678f0); C8 (Z_to_bv 64 0x168770)])
  ; (0x163bd8, [C8 (Z_to_bv 64 0x15d040); C8 (Z_to_bv 64 0x15d030)])
  ; (0x164c18, [C8 (Z_to_bv 64 0x164c18)])
  ; (0x164c90, [C8 (Z_to_bv 64 0x152fa4); C8 (Z_to_bv 64 0x14ccc0); C8 (Z_to_bv 64 0x152fc0)])
  ; (0x169650, [C4 (Z_to_bv 64 1)])
  ; (0x169698, [C1 (Z_to_bv 8 1)])
  ; (0x1fd9bc, [C1 (Z_to_bv 8 1)])
  ; (0x1fdce0, [C1 (Z_to_bv 8 0)])
  ; (0x15d5e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15d640); C8 (Z_to_bv 64 0xdbefc); C8 (Z_to_bv 64 0xdc088); C8 (Z_to_bv 64 0xdc214); C8 (Z_to_bv 64 0xb3294); C8 (Z_to_bv 64 0xb5884); C8 (Z_to_bv 64 0xb5a14)])
  ; (0x15d6a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15d720); C8 (Z_to_bv 64 0xdbea8); C8 (Z_to_bv 64 0xb34f0); C8 (Z_to_bv 64 0xb5e28); C8 (Z_to_bv 64 0xc8880); C8 (Z_to_bv 64 0xdaf6c); C8 (Z_to_bv 64 0xdb720); C8 (Z_to_bv 64 0xdc25c); C8 (Z_to_bv 64 0xdc3bc); C8 (Z_to_bv 64 0xdc524); C8 (Z_to_bv 64 0xdc610)])
  ; (0x163ac8, [C8 (Z_to_bv 64 0x2d770)])
  ; (0x164c40, [C8 (Z_to_bv 64 0x155478); C8 (Z_to_bv 64 0x1553a8)])
  ; (0x1fda66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x15d4a8, [C8 (Z_to_bv 64 0x1060fc); C8 (Z_to_bv 64 0xb0254); C8 (Z_to_bv 64 8)])
  ; (0x163a90, [C8 (Z_to_bv 64 0x160a50); C8 (Z_to_bv 64 0x160ad0)])
  ; (0x160c30, [C8 (Z_to_bv 64 0x12cc1c)])
  ; (0x163ad0, [C8 (Z_to_bv 64 0x69eb60)])
  ; (0x1605b8, [C8 (Z_to_bv 64 0x1607b8); C8 (Z_to_bv 64 0x2d588)])
  ; (0x160790, [C8 (Z_to_bv 64 0x160808); C8 (Z_to_bv 64 0x2d647)])
  ; (0x1607d8, [C8 (Z_to_bv 64 0xfe394)])
  ; (0x1607f0, [C8 (Z_to_bv 64 0xfe6f8); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x160848)])
  ; (0x160830, [C8 (Z_to_bv 64 0xff36c)])
  ; (0x160840, [C8 (Z_to_bv 64 0xfe774); C8 (Z_to_bv 64 0x160808); C8 (Z_to_bv 64 0x2d669); C8 (Z_to_bv 64 0x160790)])
  ; (0x162be0, [C8 (Z_to_bv 64 0x13e0a4); C8 (Z_to_bv 64 0x13e0dc); C8 (Z_to_bv 64 0x13e178)])
  ; (0x162c10, [C8 (Z_to_bv 64 0x13e29c); C8 (Z_to_bv 64 0x13e384); C8 (Z_to_bv 64 0x13e3ac)])
  ; (0x162c38, [C8 (Z_to_bv 64 0x13e458)])
  ; (0x162db8, [C8 (Z_to_bv 64 0x0)])
  ; (0x163af0, [C8 (Z_to_bv 64 0x167558)])
  ; (0x163af8, [C8 (Z_to_bv 64 0x167550)])
  ; (0x164c58, [C8 (Z_to_bv 64 0x148010)])
  ; (0x160c38, [C8 (Z_to_bv 64 0x12cc24)])
  ; (0x1617e0, [C8 (Z_to_bv 64 0x111640); C8 (Z_to_bv 64 0x1118ec); C8 (Z_to_bv 64 0x111b98); C8 (Z_to_bv 64 0x111e20); C8 (Z_to_bv 64 0x1120a8)])
  ; (0x160dc8, [C8 (Z_to_bv 64 0x12fe08); C8 (Z_to_bv 64 0x12fe18); C8 (Z_to_bv 64 0x12fe28)])
  ; (0x163ba0, [C8 (Z_to_bv 64 0x69e8e8)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10dd1, 10)
  ; (0x14f7f, 4)
  ; (0x16311, 17)
  ; (0x16300, 128)
  ; (0x1ad3f, 33)
  ; (0x1f513, 21)
  ; (0x1f528, 23)
  ; (0x21c00, 128)
  ; (0x22d20, 7)
  ; (0x22d20, 7)
  ; (0x33d38, 16)
  ; (0x68e480, 16)
  ; (0x13ec7, 19)
  ; (0x149d7, 1)
  ; (0x17dee, 3)
  ; (0x1a498, 3)
  ; (0x1fed0, 3)
  ; (0x20b49, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x164c60, 0x164c70); (0x1696f0, 0x1696f8);
    (0x15d030, 0x15d040); (0x162d08, 0x162d10); (0x162de0, 0x162df0); (0x163a78, 0x163a88); (0x163ad8, 0x163ae8); (0x163bd8, 0x163be8);
    (0x164c18, 0x164c20); (0x164c90, 0x164ca8); (0x169650, 0x169654); (0x169698, 0x169699); (0x1fd9bc, 0x1fd9bd); (0x1fdce0, 0x1fdce1);
    (0x15d5e0, 0x15d620); (0x15d6a0, 0x15d700); (0x163ac8, 0x163ad0); (0x164c40, 0x164c50); (0x1fda66, 0x1fda68);
    (0x15d4a8, 0x15d4c0); (0x163a90, 0x163aa0); (0x160c30, 0x160c38); (0x163ad0, 0x163ad8);
      (0x1605b8, 0x1605c8); (0x160790, 0x1607a0); (0x1607d8, 0x1607e0); (0x1607f0, 0x160808); (0x160830, 0x160838); (0x160840, 0x160860); (0x162be0, 0x162bf8); (0x162c10, 0x162c28); (0x162c38, 0x162c40); (0x162db8, 0x162dc0); (0x163af0, 0x163af8); (0x163af8, 0x163b00); (0x164c58, 0x164c60);
      (0x160c38, 0x160c40); (0x1617e0, 0x161808); (0x160dc8, 0x160de0); (0x163ba0, 0x163ba8) ].

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
  [ (0x15d5e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15d640); C8 (Z_to_bv 64 0xdbefc); C8 (Z_to_bv 64 0xdc088); C8 (Z_to_bv 64 0xdc214); C8 (Z_to_bv 64 0xb3294); C8 (Z_to_bv 64 0xb5884); C8 (Z_to_bv 64 0xb5a14)])
  ; (0x15d6a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x15d720); C8 (Z_to_bv 64 0xdbea8); C8 (Z_to_bv 64 0xb34f0); C8 (Z_to_bv 64 0xb5e28); C8 (Z_to_bv 64 0xc8880); C8 (Z_to_bv 64 0xdaf6c); C8 (Z_to_bv 64 0xdb720); C8 (Z_to_bv 64 0xdc25c); C8 (Z_to_bv 64 0xdc3bc); C8 (Z_to_bv 64 0xdc524); C8 (Z_to_bv 64 0xdc610)])
  ; (0x163ac8, [C8 (Z_to_bv 64 0x2d770)])
  ; (0x164c40, [C8 (Z_to_bv 64 0x155478); C8 (Z_to_bv 64 0x1553a8)])
  ; (0x1fda66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x15d4a8, [C8 (Z_to_bv 64 0x1060fc); C8 (Z_to_bv 64 0xb0254); C8 (Z_to_bv 64 8)])
  ; (0x163a90, [C8 (Z_to_bv 64 0x160a50); C8 (Z_to_bv 64 0x160ad0)])
  ; (0x160c30, [C8 (Z_to_bv 64 0x12cc1c)])
  ; (0x163ad0, [C8 (Z_to_bv 64 0x69eb60)])
  ; (0x1605b8, [C8 (Z_to_bv 64 0x1607b8); C8 (Z_to_bv 64 0x2d588)])
  ; (0x160790, [C8 (Z_to_bv 64 0x160808); C8 (Z_to_bv 64 0x2d647)])
  ; (0x1607d8, [C8 (Z_to_bv 64 0xfe394)])
  ; (0x1607f0, [C8 (Z_to_bv 64 0xfe6f8); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x160848)])
  ; (0x160830, [C8 (Z_to_bv 64 0xff36c)])
  ; (0x160840, [C8 (Z_to_bv 64 0xfe774); C8 (Z_to_bv 64 0x160808); C8 (Z_to_bv 64 0x2d669); C8 (Z_to_bv 64 0x160790)])
  ; (0x162be0, [C8 (Z_to_bv 64 0x13e0a4); C8 (Z_to_bv 64 0x13e0dc); C8 (Z_to_bv 64 0x13e178)])
  ; (0x162c10, [C8 (Z_to_bv 64 0x13e29c); C8 (Z_to_bv 64 0x13e384); C8 (Z_to_bv 64 0x13e3ac)])
  ; (0x162c38, [C8 (Z_to_bv 64 0x13e458)])
  ; (0x162db8, [C8 (Z_to_bv 64 0x0)])
  ; (0x163af0, [C8 (Z_to_bv 64 0x167558)])
  ; (0x163af8, [C8 (Z_to_bv 64 0x167550)])
  ; (0x164c58, [C8 (Z_to_bv 64 0x148010)])
  ; (0x160c38, [C8 (Z_to_bv 64 0x12cc24)])
  ; (0x1617e0, [C8 (Z_to_bv 64 0x111640); C8 (Z_to_bv 64 0x1118ec); C8 (Z_to_bv 64 0x111b98); C8 (Z_to_bv 64 0x111e20); C8 (Z_to_bv 64 0x1120a8)])
  ; (0x160dc8, [C8 (Z_to_bv 64 0x12fe08); C8 (Z_to_bv 64 0x12fe18); C8 (Z_to_bv 64 0x12fe28)])
  ; (0x163ba0, [C8 (Z_to_bv 64 0x69e8e8)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
