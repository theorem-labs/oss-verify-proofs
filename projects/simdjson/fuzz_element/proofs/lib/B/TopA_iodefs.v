(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x17acb0, [C8 (Z_to_bv 64 0x171c04); C8 (Z_to_bv 64 0x1624b0)])
  ; (0x180530, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x172d88, [C8 (Z_to_bv 64 0xbc578); C8 (Z_to_bv 64 0x5ab90)])
  ; (0x178d28, [C8 (Z_to_bv 64 0x17da10)])
  ; (0x178e00, [C8 (Z_to_bv 64 0x159e44); C8 (Z_to_bv 64 0)])
  ; (0x179a98, [C8 (Z_to_bv 64 0x178d28); C8 (Z_to_bv 64 0)])
  ; (0x179b20, [C8 (Z_to_bv 64 0x17dd10); C8 (Z_to_bv 64 0x17f590)])
  ; (0x179c08, [C8 (Z_to_bv 64 0x172d98); C8 (Z_to_bv 64 0x172d88)])
  ; (0x17ac60, [C8 (Z_to_bv 64 0x17ac60)])
  ; (0x17ace0, [C8 (Z_to_bv 64 0x168bac); C8 (Z_to_bv 64 0x1628c8); C8 (Z_to_bv 64 0x168bc8)])
  ; (0x180490, [C4 (Z_to_bv 64 1)])
  ; (0x1804d8, [C1 (Z_to_bv 8 1)])
  ; (0x2147fc, [C1 (Z_to_bv 8 1)])
  ; (0x214b20, [C1 (Z_to_bv 8 0)])
  ; (0x173600, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x173660); C8 (Z_to_bv 64 0xf1008); C8 (Z_to_bv 64 0xf11a8); C8 (Z_to_bv 64 0xf1348); C8 (Z_to_bv 64 0xbd4c8); C8 (Z_to_bv 64 0xc0608); C8 (Z_to_bv 64 0xc07f0)])
  ; (0x1736c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x173740); C8 (Z_to_bv 64 0xf0fb4); C8 (Z_to_bv 64 0xbd768); C8 (Z_to_bv 64 0xc0c44); C8 (Z_to_bv 64 0xd862c); C8 (Z_to_bv 64 0xefec4); C8 (Z_to_bv 64 0xf0768); C8 (Z_to_bv 64 0xf1390); C8 (Z_to_bv 64 0xf1504); C8 (Z_to_bv 64 0xf1678); C8 (Z_to_bv 64 0xf1764)])
  ; (0x179ac0, [C8 (Z_to_bv 64 0x2e928)])
  ; (0x17ac90, [C8 (Z_to_bv 64 0x16b080); C8 (Z_to_bv 64 0x16afb0)])
  ; (0x2148a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x173228, [C8 (Z_to_bv 64 0x11bd04); C8 (Z_to_bv 64 0xb9ea8); C8 (Z_to_bv 64 8)])
  ; (0x179ac8, [C8 (Z_to_bv 64 0x176af0); C8 (Z_to_bv 64 0x176a70)])
  ; (0x176c50, [C8 (Z_to_bv 64 0x142824)])
  ; (0x179b18, [C8 (Z_to_bv 64 0x6b59a0)])
  ; (0x173170, [C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x238bc); C8 (Z_to_bv 64 0x1765d8)])
  ; (0x1765d8, [C8 (Z_to_bv 64 0x1767d8); C8 (Z_to_bv 64 0x2e740)])
  ; (0x1767b0, [C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x2e7ff)])
  ; (0x1767f8, [C8 (Z_to_bv 64 0x113d54)])
  ; (0x176810, [C8 (Z_to_bv 64 0x1140b8); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x176868)])
  ; (0x176850, [C8 (Z_to_bv 64 0x114d2c)])
  ; (0x176860, [C8 (Z_to_bv 64 0x114134); C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x2e821); C8 (Z_to_bv 64 0x1767b0)])
  ; (0x178c00, [C8 (Z_to_bv 64 0x153cac); C8 (Z_to_bv 64 0x153ce4); C8 (Z_to_bv 64 0x153d80)])
  ; (0x178c30, [C8 (Z_to_bv 64 0x153ea4); C8 (Z_to_bv 64 0x153f8c); C8 (Z_to_bv 64 0x153fb4)])
  ; (0x178c58, [C8 (Z_to_bv 64 0x154060)])
  ; (0x178dd8, [C8 (Z_to_bv 64 0x0)])
  ; (0x179ab8, [C8 (Z_to_bv 64 0x11395c)])
  ; (0x179b38, [C8 (Z_to_bv 64 0x17d970)])
  ; (0x179b40, [C8 (Z_to_bv 64 0x17d968)])
  ; (0x17aca8, [C8 (Z_to_bv 64 0x15dc18)])
  ; (0x176c58, [C8 (Z_to_bv 64 0x14282c)])
  ; (0x177800, [C8 (Z_to_bv 64 0x127248); C8 (Z_to_bv 64 0x1274f4); C8 (Z_to_bv 64 0x1277a0); C8 (Z_to_bv 64 0x127a28); C8 (Z_to_bv 64 0x127cb0)])
  ; (0x176de8, [C8 (Z_to_bv 64 0x145a10); C8 (Z_to_bv 64 0x145a20); C8 (Z_to_bv 64 0x145a30)])
  ; (0x179bd0, [C8 (Z_to_bv 64 0x6b5728)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10e0d, 10)
  ; (0x1504b, 4)
  ; (0x163ee, 17)
  ; (0x163c0, 128)
  ; (0x1aeb9, 33)
  ; (0x1f625, 21)
  ; (0x1f63a, 23)
  ; (0x21e00, 128)
  ; (0x22ff0, 7)
  ; (0x22ff0, 7)
  ; (0x34ef0, 16)
  ; (0x6a52c0, 16)
  ; (0x13f9b, 19)
  ; (0x14aa3, 1)
  ; (0x17f05, 3)
  ; (0x1a612, 3)
  ; (0x200a9, 3)
  ; (0x20d2b, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x17acb0, 0x17acc0); (0x180530, 0x180538);
    (0x172d88, 0x172d98); (0x178d28, 0x178d30); (0x178e00, 0x178e10); (0x179a98, 0x179aa8); (0x179b20, 0x179b30); (0x179c08, 0x179c18);
    (0x17ac60, 0x17ac68); (0x17ace0, 0x17acf8); (0x180490, 0x180494); (0x1804d8, 0x1804d9); (0x2147fc, 0x2147fd); (0x214b20, 0x214b21);
    (0x173600, 0x173640); (0x1736c0, 0x173720); (0x179ac0, 0x179ac8); (0x17ac90, 0x17aca0); (0x2148a6, 0x2148a8);
    (0x173228, 0x173240); (0x179ac8, 0x179ad8); (0x176c50, 0x176c58); (0x179b18, 0x179b20);
      (0x173170, 0x173188); (0x1765d8, 0x1765e8); (0x1767b0, 0x1767c0); (0x1767f8, 0x176800); (0x176810, 0x176828); (0x176850, 0x176858); (0x176860, 0x176880); (0x178c00, 0x178c18); (0x178c30, 0x178c48); (0x178c58, 0x178c60); (0x178dd8, 0x178de0); (0x179ab8, 0x179ac0); (0x179b38, 0x179b40); (0x179b40, 0x179b48); (0x17aca8, 0x17acb0);
      (0x176c58, 0x176c60); (0x177800, 0x177828); (0x176de8, 0x176e00); (0x179bd0, 0x179bd8) ].

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
  [ (0x173600, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x173660); C8 (Z_to_bv 64 0xf1008); C8 (Z_to_bv 64 0xf11a8); C8 (Z_to_bv 64 0xf1348); C8 (Z_to_bv 64 0xbd4c8); C8 (Z_to_bv 64 0xc0608); C8 (Z_to_bv 64 0xc07f0)])
  ; (0x1736c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x173740); C8 (Z_to_bv 64 0xf0fb4); C8 (Z_to_bv 64 0xbd768); C8 (Z_to_bv 64 0xc0c44); C8 (Z_to_bv 64 0xd862c); C8 (Z_to_bv 64 0xefec4); C8 (Z_to_bv 64 0xf0768); C8 (Z_to_bv 64 0xf1390); C8 (Z_to_bv 64 0xf1504); C8 (Z_to_bv 64 0xf1678); C8 (Z_to_bv 64 0xf1764)])
  ; (0x179ac0, [C8 (Z_to_bv 64 0x2e928)])
  ; (0x17ac90, [C8 (Z_to_bv 64 0x16b080); C8 (Z_to_bv 64 0x16afb0)])
  ; (0x2148a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x173228, [C8 (Z_to_bv 64 0x11bd04); C8 (Z_to_bv 64 0xb9ea8); C8 (Z_to_bv 64 8)])
  ; (0x179ac8, [C8 (Z_to_bv 64 0x176af0); C8 (Z_to_bv 64 0x176a70)])
  ; (0x176c50, [C8 (Z_to_bv 64 0x142824)])
  ; (0x179b18, [C8 (Z_to_bv 64 0x6b59a0)])
  ; (0x173170, [C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x238bc); C8 (Z_to_bv 64 0x1765d8)])
  ; (0x1765d8, [C8 (Z_to_bv 64 0x1767d8); C8 (Z_to_bv 64 0x2e740)])
  ; (0x1767b0, [C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x2e7ff)])
  ; (0x1767f8, [C8 (Z_to_bv 64 0x113d54)])
  ; (0x176810, [C8 (Z_to_bv 64 0x1140b8); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x176868)])
  ; (0x176850, [C8 (Z_to_bv 64 0x114d2c)])
  ; (0x176860, [C8 (Z_to_bv 64 0x114134); C8 (Z_to_bv 64 0x176828); C8 (Z_to_bv 64 0x2e821); C8 (Z_to_bv 64 0x1767b0)])
  ; (0x178c00, [C8 (Z_to_bv 64 0x153cac); C8 (Z_to_bv 64 0x153ce4); C8 (Z_to_bv 64 0x153d80)])
  ; (0x178c30, [C8 (Z_to_bv 64 0x153ea4); C8 (Z_to_bv 64 0x153f8c); C8 (Z_to_bv 64 0x153fb4)])
  ; (0x178c58, [C8 (Z_to_bv 64 0x154060)])
  ; (0x178dd8, [C8 (Z_to_bv 64 0x0)])
  ; (0x179ab8, [C8 (Z_to_bv 64 0x11395c)])
  ; (0x179b38, [C8 (Z_to_bv 64 0x17d970)])
  ; (0x179b40, [C8 (Z_to_bv 64 0x17d968)])
  ; (0x17aca8, [C8 (Z_to_bv 64 0x15dc18)])
  ; (0x176c58, [C8 (Z_to_bv 64 0x14282c)])
  ; (0x177800, [C8 (Z_to_bv 64 0x127248); C8 (Z_to_bv 64 0x1274f4); C8 (Z_to_bv 64 0x1277a0); C8 (Z_to_bv 64 0x127a28); C8 (Z_to_bv 64 0x127cb0)])
  ; (0x176de8, [C8 (Z_to_bv 64 0x145a10); C8 (Z_to_bv 64 0x145a20); C8 (Z_to_bv 64 0x145a30)])
  ; (0x179bd0, [C8 (Z_to_bv 64 0x6b5728)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
