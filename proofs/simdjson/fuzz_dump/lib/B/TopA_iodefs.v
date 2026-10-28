(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x170028, [C8 (Z_to_bv 64 0x167288); C8 (Z_to_bv 64 0x157c84)])
  ; (0x1749f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x168408, [C8 (Z_to_bv 64 0xb219c); C8 (Z_to_bv 64 0x57e4c)])
  ; (0x16e0c8, [C8 (Z_to_bv 64 0x172d90)])
  ; (0x16e1a0, [C8 (Z_to_bv 64 0x14f618); C8 (Z_to_bv 64 0)])
  ; (0x16ee38, [C8 (Z_to_bv 64 0x16e0c8); C8 (Z_to_bv 64 0)])
  ; (0x16ee98, [C8 (Z_to_bv 64 0x173090); C8 (Z_to_bv 64 0x173a50)])
  ; (0x16ef98, [C8 (Z_to_bv 64 0x168418); C8 (Z_to_bv 64 0x168408)])
  ; (0x16ffe0, [C8 (Z_to_bv 64 0x16ffe0)])
  ; (0x170058, [C8 (Z_to_bv 64 0x15e380); C8 (Z_to_bv 64 0x15809c); C8 (Z_to_bv 64 0x15e39c)])
  ; (0x174950, [C4 (Z_to_bv 64 1)])
  ; (0x174998, [C1 (Z_to_bv 8 1)])
  ; (0x208cbc, [C1 (Z_to_bv 8 1)])
  ; (0x208fe0, [C1 (Z_to_bv 8 0)])
  ; (0x1689a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168a00); C8 (Z_to_bv 64 0xe6c2c); C8 (Z_to_bv 64 0xe6dcc); C8 (Z_to_bv 64 0xe6f6c); C8 (Z_to_bv 64 0xb30ec); C8 (Z_to_bv 64 0xb622c); C8 (Z_to_bv 64 0xb6414)])
  ; (0x168a60, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168ae0); C8 (Z_to_bv 64 0xe6bd8); C8 (Z_to_bv 64 0xb338c); C8 (Z_to_bv 64 0xb6868); C8 (Z_to_bv 64 0xce250); C8 (Z_to_bv 64 0xe5ae8); C8 (Z_to_bv 64 0xe638c); C8 (Z_to_bv 64 0xe6fb4); C8 (Z_to_bv 64 0xe7128); C8 (Z_to_bv 64 0xe729c); C8 (Z_to_bv 64 0xe7388)])
  ; (0x16ee88, [C8 (Z_to_bv 64 0x2cf28)])
  ; (0x170008, [C8 (Z_to_bv 64 0x160854); C8 (Z_to_bv 64 0x160784)])
  ; (0x208d66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x168868, [C8 (Z_to_bv 64 0x1116e0); C8 (Z_to_bv 64 0xb0d84); C8 (Z_to_bv 64 8)])
  ; (0x16ee50, [C8 (Z_to_bv 64 0x16be10); C8 (Z_to_bv 64 0x16be90)])
  ; (0x16bff0, [C8 (Z_to_bv 64 0x137ff8)])
  ; (0x16ee90, [C8 (Z_to_bv 64 0x6a9e60)])
  ; (0x16b978, [C8 (Z_to_bv 64 0x16bb78); C8 (Z_to_bv 64 0x2cd40)])
  ; (0x16bb50, [C8 (Z_to_bv 64 0x16bbc8); C8 (Z_to_bv 64 0x2cdff)])
  ; (0x16bb98, [C8 (Z_to_bv 64 0x109978)])
  ; (0x16bbb0, [C8 (Z_to_bv 64 0x109cdc); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16bc08)])
  ; (0x16bbf0, [C8 (Z_to_bv 64 0x10a950)])
  ; (0x16bc00, [C8 (Z_to_bv 64 0x109d58); C8 (Z_to_bv 64 0x16bbc8); C8 (Z_to_bv 64 0x2ce21); C8 (Z_to_bv 64 0x16bb50)])
  ; (0x16dfa0, [C8 (Z_to_bv 64 0x149480); C8 (Z_to_bv 64 0x1494b8); C8 (Z_to_bv 64 0x149554)])
  ; (0x16dfd0, [C8 (Z_to_bv 64 0x149678); C8 (Z_to_bv 64 0x149760); C8 (Z_to_bv 64 0x149788)])
  ; (0x16dff8, [C8 (Z_to_bv 64 0x149834)])
  ; (0x16e178, [C8 (Z_to_bv 64 0x0)])
  ; (0x16eeb0, [C8 (Z_to_bv 64 0x172cf0)])
  ; (0x16eeb8, [C8 (Z_to_bv 64 0x172ce8)])
  ; (0x170020, [C8 (Z_to_bv 64 0x1533ec)])
  ; (0x16bff8, [C8 (Z_to_bv 64 0x138000)])
  ; (0x16cb98, [C8 (Z_to_bv 64 0x11c784)])
  ; (0x16cba0, [C8 (Z_to_bv 64 0x11ca1c); C8 (Z_to_bv 64 0x11ccc8); C8 (Z_to_bv 64 0x11cf74); C8 (Z_to_bv 64 0x11d1fc); C8 (Z_to_bv 64 0x11d484)])
  ; (0x16c188, [C8 (Z_to_bv 64 0x13b1e4); C8 (Z_to_bv 64 0x13b1f4); C8 (Z_to_bv 64 0x13b204)])
  ; (0x16ef60, [C8 (Z_to_bv 64 0x6a9be8)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10de4, 10)
  ; (0x14f4c, 4)
  ; (0x162cf, 17)
  ; (0x162c0, 128)
  ; (0x1ac26, 33)
  ; (0x1f3d8, 21)
  ; (0x1f3ed, 23)
  ; (0x21b80, 128)
  ; (0x22ceb, 7)
  ; (0x22ceb, 7)
  ; (0x334f0, 16)
  ; (0x699780, 16)
  ; (0x13ea4, 19)
  ; (0x149a4, 1)
  ; (0x17dad, 3)
  ; (0x1a37f, 3)
  ; (0x1fe0e, 3)
  ; (0x20a88, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x170028, 0x170038); (0x1749f0, 0x1749f8);
    (0x168408, 0x168418); (0x16e0c8, 0x16e0d0); (0x16e1a0, 0x16e1b0); (0x16ee38, 0x16ee48); (0x16ee98, 0x16eea8); (0x16ef98, 0x16efa8);
    (0x16ffe0, 0x16ffe8); (0x170058, 0x170070); (0x174950, 0x174954); (0x174998, 0x174999); (0x208cbc, 0x208cbd); (0x208fe0, 0x208fe1);
    (0x1689a0, 0x1689e0); (0x168a60, 0x168ac0); (0x16ee88, 0x16ee90); (0x170008, 0x170018); (0x208d66, 0x208d68);
    (0x168868, 0x168880); (0x16ee50, 0x16ee60); (0x16bff0, 0x16bff8); (0x16ee90, 0x16ee98);
      (0x16b978, 0x16b988); (0x16bb50, 0x16bb60); (0x16bb98, 0x16bba0); (0x16bbb0, 0x16bbc8); (0x16bbf0, 0x16bbf8); (0x16bc00, 0x16bc20); (0x16dfa0, 0x16dfb8); (0x16dfd0, 0x16dfe8); (0x16dff8, 0x16e000); (0x16e178, 0x16e180); (0x16eeb0, 0x16eeb8); (0x16eeb8, 0x16eec0); (0x170020, 0x170028);
      (0x16bff8, 0x16c000);   (0x16cb98, 0x16cba0); (0x16cba0, 0x16cbc8); (0x16c188, 0x16c1a0); (0x16ef60, 0x16ef68) ].

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
  [ (0x1689a0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168a00); C8 (Z_to_bv 64 0xe6c2c); C8 (Z_to_bv 64 0xe6dcc); C8 (Z_to_bv 64 0xe6f6c); C8 (Z_to_bv 64 0xb30ec); C8 (Z_to_bv 64 0xb622c); C8 (Z_to_bv 64 0xb6414)])
  ; (0x168a60, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x168ae0); C8 (Z_to_bv 64 0xe6bd8); C8 (Z_to_bv 64 0xb338c); C8 (Z_to_bv 64 0xb6868); C8 (Z_to_bv 64 0xce250); C8 (Z_to_bv 64 0xe5ae8); C8 (Z_to_bv 64 0xe638c); C8 (Z_to_bv 64 0xe6fb4); C8 (Z_to_bv 64 0xe7128); C8 (Z_to_bv 64 0xe729c); C8 (Z_to_bv 64 0xe7388)])
  ; (0x16ee88, [C8 (Z_to_bv 64 0x2cf28)])
  ; (0x170008, [C8 (Z_to_bv 64 0x160854); C8 (Z_to_bv 64 0x160784)])
  ; (0x208d66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x168868, [C8 (Z_to_bv 64 0x1116e0); C8 (Z_to_bv 64 0xb0d84); C8 (Z_to_bv 64 8)])
  ; (0x16ee50, [C8 (Z_to_bv 64 0x16be10); C8 (Z_to_bv 64 0x16be90)])
  ; (0x16bff0, [C8 (Z_to_bv 64 0x137ff8)])
  ; (0x16ee90, [C8 (Z_to_bv 64 0x6a9e60)])
  ; (0x16b978, [C8 (Z_to_bv 64 0x16bb78); C8 (Z_to_bv 64 0x2cd40)])
  ; (0x16bb50, [C8 (Z_to_bv 64 0x16bbc8); C8 (Z_to_bv 64 0x2cdff)])
  ; (0x16bb98, [C8 (Z_to_bv 64 0x109978)])
  ; (0x16bbb0, [C8 (Z_to_bv 64 0x109cdc); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16bc08)])
  ; (0x16bbf0, [C8 (Z_to_bv 64 0x10a950)])
  ; (0x16bc00, [C8 (Z_to_bv 64 0x109d58); C8 (Z_to_bv 64 0x16bbc8); C8 (Z_to_bv 64 0x2ce21); C8 (Z_to_bv 64 0x16bb50)])
  ; (0x16dfa0, [C8 (Z_to_bv 64 0x149480); C8 (Z_to_bv 64 0x1494b8); C8 (Z_to_bv 64 0x149554)])
  ; (0x16dfd0, [C8 (Z_to_bv 64 0x149678); C8 (Z_to_bv 64 0x149760); C8 (Z_to_bv 64 0x149788)])
  ; (0x16dff8, [C8 (Z_to_bv 64 0x149834)])
  ; (0x16e178, [C8 (Z_to_bv 64 0x0)])
  ; (0x16eeb0, [C8 (Z_to_bv 64 0x172cf0)])
  ; (0x16eeb8, [C8 (Z_to_bv 64 0x172ce8)])
  ; (0x170020, [C8 (Z_to_bv 64 0x1533ec)])
  ; (0x16bff8, [C8 (Z_to_bv 64 0x138000)])
  ; (0x16cb98, [C8 (Z_to_bv 64 0x11c784)])
  ; (0x16cba0, [C8 (Z_to_bv 64 0x11ca1c); C8 (Z_to_bv 64 0x11ccc8); C8 (Z_to_bv 64 0x11cf74); C8 (Z_to_bv 64 0x11d1fc); C8 (Z_to_bv 64 0x11d484)])
  ; (0x16c188, [C8 (Z_to_bv 64 0x13b1e4); C8 (Z_to_bv 64 0x13b1f4); C8 (Z_to_bv 64 0x13b204)])
  ; (0x16ef60, [C8 (Z_to_bv 64 0x6a9be8)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
