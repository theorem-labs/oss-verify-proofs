(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x16c098, [C8 (Z_to_bv 64 0x162fec); C8 (Z_to_bv 64 0x153924)])
  ; (0x1714f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x164170, [C8 (Z_to_bv 64 0xb9304); C8 (Z_to_bv 64 0x5a4e0)])
  ; (0x16a128, [C8 (Z_to_bv 64 0x16ea38)])
  ; (0x16a200, [C8 (Z_to_bv 64 0x14b2b8); C8 (Z_to_bv 64 0)])
  ; (0x16ae98, [C8 (Z_to_bv 64 0x16a128); C8 (Z_to_bv 64 0)])
  ; (0x16af20, [C8 (Z_to_bv 64 0x16ed30); C8 (Z_to_bv 64 0x170570)])
  ; (0x16b008, [C8 (Z_to_bv 64 0x164180); C8 (Z_to_bv 64 0x164170)])
  ; (0x16c048, [C8 (Z_to_bv 64 0x16c048)])
  ; (0x16c0c8, [C8 (Z_to_bv 64 0x15a020); C8 (Z_to_bv 64 0x153d3c); C8 (Z_to_bv 64 0x15a03c)])
  ; (0x171450, [C4 (Z_to_bv 64 1)])
  ; (0x171498, [C1 (Z_to_bv 8 1)])
  ; (0x2057bc, [C1 (Z_to_bv 8 1)])
  ; (0x205ae0, [C1 (Z_to_bv 8 0)])
  ; (0x164a00, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164a60); C8 (Z_to_bv 64 0xe2d30); C8 (Z_to_bv 64 0xe2ebc); C8 (Z_to_bv 64 0xe3048); C8 (Z_to_bv 64 0xba0c8); C8 (Z_to_bv 64 0xbc6b8); C8 (Z_to_bv 64 0xbc848)])
  ; (0x164ac0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164b40); C8 (Z_to_bv 64 0xe2cdc); C8 (Z_to_bv 64 0xba324); C8 (Z_to_bv 64 0xbcc5c); C8 (Z_to_bv 64 0xcf6b4); C8 (Z_to_bv 64 0xe1da0); C8 (Z_to_bv 64 0xe2554); C8 (Z_to_bv 64 0xe3090); C8 (Z_to_bv 64 0xe31f0); C8 (Z_to_bv 64 0xe3358); C8 (Z_to_bv 64 0xe3444)])
  ; (0x16aec0, [C8 (Z_to_bv 64 0x2eae8)])
  ; (0x16c078, [C8 (Z_to_bv 64 0x15c4f4); C8 (Z_to_bv 64 0x15c424)])
  ; (0x205866, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x164628, [C8 (Z_to_bv 64 0x10d178); C8 (Z_to_bv 64 0xb6f64); C8 (Z_to_bv 64 8)])
  ; (0x16aec8, [C8 (Z_to_bv 64 0x167ef0); C8 (Z_to_bv 64 0x167e70)])
  ; (0x168050, [C8 (Z_to_bv 64 0x133c98)])
  ; (0x16af18, [C8 (Z_to_bv 64 0x6a6960)])
  ; (0x164570, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)])
  ; (0x1679d8, [C8 (Z_to_bv 64 0x167bd8); C8 (Z_to_bv 64 0x2e900)])
  ; (0x167bb0, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9bf)])
  ; (0x167bf8, [C8 (Z_to_bv 64 0x1051c8)])
  ; (0x167c10, [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)])
  ; (0x167c50, [C8 (Z_to_bv 64 0x1061a0)])
  ; (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)])
  ; (0x16a000, [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)])
  ; (0x16a030, [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)])
  ; (0x16a058, [C8 (Z_to_bv 64 0x1454d4)])
  ; (0x16a1d8, [C8 (Z_to_bv 64 0x0)])
  ; (0x16aeb8, [C8 (Z_to_bv 64 0x104dd0)])
  ; (0x16af38, [C8 (Z_to_bv 64 0x16e998)])
  ; (0x16af40, [C8 (Z_to_bv 64 0x16e990)])
  ; (0x16c090, [C8 (Z_to_bv 64 0x14f08c)])
  ; (0x168058, [C8 (Z_to_bv 64 0x133ca0)])
  ; (0x168c00, [C8 (Z_to_bv 64 0x1186bc); C8 (Z_to_bv 64 0x118968); C8 (Z_to_bv 64 0x118c14); C8 (Z_to_bv 64 0x118e9c); C8 (Z_to_bv 64 0x119124)])
  ; (0x1681e8, [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)])
  ; (0x16afd0, [C8 (Z_to_bv 64 0x6a66e8)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10dd9, 10)
  ; (0x14ffe, 4)
  ; (0x16390, 17)
  ; (0x16380, 128)
  ; (0x1ae0b, 33)
  ; (0x1f5f2, 21)
  ; (0x1f607, 23)
  ; (0x21d40, 128)
  ; (0x22e7d, 7)
  ; (0x22e7d, 7)
  ; (0x350b0, 16)
  ; (0x696280, 16)
  ; (0x13f46, 19)
  ; (0x14a56, 1)
  ; (0x17e6d, 3)
  ; (0x1a564, 3)
  ; (0x1ffdd, 3)
  ; (0x20c56, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x16c098, 0x16c0a8); (0x1714f0, 0x1714f8);
    (0x164170, 0x164180); (0x16a128, 0x16a130); (0x16a200, 0x16a210); (0x16ae98, 0x16aea8); (0x16af20, 0x16af30); (0x16b008, 0x16b018);
    (0x16c048, 0x16c050); (0x16c0c8, 0x16c0e0); (0x171450, 0x171454); (0x171498, 0x171499); (0x2057bc, 0x2057bd); (0x205ae0, 0x205ae1);
    (0x164a00, 0x164a40); (0x164ac0, 0x164b20); (0x16aec0, 0x16aec8); (0x16c078, 0x16c088); (0x205866, 0x205868);
    (0x164628, 0x164640); (0x16aec8, 0x16aed8); (0x168050, 0x168058); (0x16af18, 0x16af20);
      (0x164570, 0x164588); (0x1679d8, 0x1679e8); (0x167bb0, 0x167bc0); (0x167bf8, 0x167c00); (0x167c10, 0x167c28); (0x167c50, 0x167c58); (0x167c60, 0x167c80); (0x16a000, 0x16a018); (0x16a030, 0x16a048); (0x16a058, 0x16a060); (0x16a1d8, 0x16a1e0); (0x16aeb8, 0x16aec0); (0x16af38, 0x16af40); (0x16af40, 0x16af48); (0x16c090, 0x16c098);
      (0x168058, 0x168060); (0x168c00, 0x168c28); (0x1681e8, 0x168200); (0x16afd0, 0x16afd8) ].

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
  [ (0x164a00, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164a60); C8 (Z_to_bv 64 0xe2d30); C8 (Z_to_bv 64 0xe2ebc); C8 (Z_to_bv 64 0xe3048); C8 (Z_to_bv 64 0xba0c8); C8 (Z_to_bv 64 0xbc6b8); C8 (Z_to_bv 64 0xbc848)])
  ; (0x164ac0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164b40); C8 (Z_to_bv 64 0xe2cdc); C8 (Z_to_bv 64 0xba324); C8 (Z_to_bv 64 0xbcc5c); C8 (Z_to_bv 64 0xcf6b4); C8 (Z_to_bv 64 0xe1da0); C8 (Z_to_bv 64 0xe2554); C8 (Z_to_bv 64 0xe3090); C8 (Z_to_bv 64 0xe31f0); C8 (Z_to_bv 64 0xe3358); C8 (Z_to_bv 64 0xe3444)])
  ; (0x16aec0, [C8 (Z_to_bv 64 0x2eae8)])
  ; (0x16c078, [C8 (Z_to_bv 64 0x15c4f4); C8 (Z_to_bv 64 0x15c424)])
  ; (0x205866, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x164628, [C8 (Z_to_bv 64 0x10d178); C8 (Z_to_bv 64 0xb6f64); C8 (Z_to_bv 64 8)])
  ; (0x16aec8, [C8 (Z_to_bv 64 0x167ef0); C8 (Z_to_bv 64 0x167e70)])
  ; (0x168050, [C8 (Z_to_bv 64 0x133c98)])
  ; (0x16af18, [C8 (Z_to_bv 64 0x6a6960)])
  ; (0x164570, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x236cc); C8 (Z_to_bv 64 0x1679d8)])
  ; (0x1679d8, [C8 (Z_to_bv 64 0x167bd8); C8 (Z_to_bv 64 0x2e900)])
  ; (0x167bb0, [C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9bf)])
  ; (0x167bf8, [C8 (Z_to_bv 64 0x1051c8)])
  ; (0x167c10, [C8 (Z_to_bv 64 0x10552c); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x167c68)])
  ; (0x167c50, [C8 (Z_to_bv 64 0x1061a0)])
  ; (0x167c60, [C8 (Z_to_bv 64 0x1055a8); C8 (Z_to_bv 64 0x167c28); C8 (Z_to_bv 64 0x2e9e1); C8 (Z_to_bv 64 0x167bb0)])
  ; (0x16a000, [C8 (Z_to_bv 64 0x145120); C8 (Z_to_bv 64 0x145158); C8 (Z_to_bv 64 0x1451f4)])
  ; (0x16a030, [C8 (Z_to_bv 64 0x145318); C8 (Z_to_bv 64 0x145400); C8 (Z_to_bv 64 0x145428)])
  ; (0x16a058, [C8 (Z_to_bv 64 0x1454d4)])
  ; (0x16a1d8, [C8 (Z_to_bv 64 0x0)])
  ; (0x16aeb8, [C8 (Z_to_bv 64 0x104dd0)])
  ; (0x16af38, [C8 (Z_to_bv 64 0x16e998)])
  ; (0x16af40, [C8 (Z_to_bv 64 0x16e990)])
  ; (0x16c090, [C8 (Z_to_bv 64 0x14f08c)])
  ; (0x168058, [C8 (Z_to_bv 64 0x133ca0)])
  ; (0x168c00, [C8 (Z_to_bv 64 0x1186bc); C8 (Z_to_bv 64 0x118968); C8 (Z_to_bv 64 0x118c14); C8 (Z_to_bv 64 0x118e9c); C8 (Z_to_bv 64 0x119124)])
  ; (0x1681e8, [C8 (Z_to_bv 64 0x136e84); C8 (Z_to_bv 64 0x136e94); C8 (Z_to_bv 64 0x136ea4)])
  ; (0x16afd0, [C8 (Z_to_bv 64 0x6a66e8)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
