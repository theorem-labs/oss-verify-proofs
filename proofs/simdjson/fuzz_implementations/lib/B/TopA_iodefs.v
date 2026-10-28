(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x181d88, [C8 (Z_to_bv 64 0x178858); C8 (Z_to_bv 64 0x168e70)])
  ; (0x187230, [C8 (Z_to_bv 64 0)])
  ; (0x181ee0, [C8 (Z_to_bv 64 0x160578)])
  ; (0x181e38, [C8 (Z_to_bv 64 0x168400)])
  ; (0x181e00, [C8 (Z_to_bv 64 0x1673e4)])
  ; (0x183fb4, [C4 (Z_to_bv 64 0x8)])
  ; (0x187194, [C1 (Z_to_bv 8 0x0)])
  ; (0x17d5c0, [C8 (Z_to_bv 64 0x8)])
  ; (0x17d6e0, [C8 (Z_to_bv 64 0x8)])
  ; (0x17da68, [C8 (Z_to_bv 64 0x1226b8)])
  ; (0x17db98, [C8 (Z_to_bv 64 0x122e1c)])
  ; (0x17de28, [C8 (Z_to_bv 64 0x14a7c8)])
  ; (0x17e0d8, [C8 (Z_to_bv 64 0x149ffc)])     ].

Definition io_ro : list (Z * list cell) :=
  [ (0x1799e0, [C8 (Z_to_bv 64 0xbff10); C8 (Z_to_bv 64 0x5dcf4)])
  ; (0x17fdb8, [C8 (Z_to_bv 64 0x184af0)])
  ; (0x17fe98, [C8 (Z_to_bv 64 0x160574); C8 (Z_to_bv 64 0)])
  ; (0x180b30, [C8 (Z_to_bv 64 0x17fdb8); C8 (Z_to_bv 64 0)])
  ; (0x180bb0, [C8 (Z_to_bv 64 0x184df0); C8 (Z_to_bv 64 0x1862b0)])
  ; (0x180ce8, [C8 (Z_to_bv 64 0x1799f0); C8 (Z_to_bv 64 0x1799e0)])
  ; (0x181d40, [C8 (Z_to_bv 64 0x181d40)])
  ; (0x181db8, [C8 (Z_to_bv 64 0x16fa44); C8 (Z_to_bv 64 0x169760); C8 (Z_to_bv 64 0x16fa60)])
  ; (0x187190, [C4 (Z_to_bv 64 1)])
  ; (0x1871d8, [C1 (Z_to_bv 8 1)])
  ; (0x21b4fc, [C1 (Z_to_bv 8 1)])
  ; (0x21b820, [C1 (Z_to_bv 8 0)])
  ; (0x17a080, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17a0e0); C8 (Z_to_bv 64 0xf57bc); C8 (Z_to_bv 64 0xf595c); C8 (Z_to_bv 64 0xf5afc); C8 (Z_to_bv 64 0xc1c7c); C8 (Z_to_bv 64 0xc4dbc); C8 (Z_to_bv 64 0xc4fa4)])
  ; (0x17a140, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17a1c0); C8 (Z_to_bv 64 0xf5768); C8 (Z_to_bv 64 0xc1f1c); C8 (Z_to_bv 64 0xc53f8); C8 (Z_to_bv 64 0xdcde0); C8 (Z_to_bv 64 0xf4678); C8 (Z_to_bv 64 0xf4f1c); C8 (Z_to_bv 64 0xf5b44); C8 (Z_to_bv 64 0xf5cb8); C8 (Z_to_bv 64 0xf5e2c); C8 (Z_to_bv 64 0xf5f18)])
  ; (0x180b50, [C8 (Z_to_bv 64 0x17d908); C8 (Z_to_bv 64 0x17d730); C8 (Z_to_bv 64 0x17d4f0); C8 (Z_to_bv 64 0x17d8b8)])
  ; (0x17d908, [C8 (Z_to_bv 64 0x17d8d0); C8 (Z_to_bv 64 0x17d940); C8 (Z_to_bv 64 0x17d968); C8 (Z_to_bv 64 0x17d8f8); C8 (Z_to_bv 64 0x70)])
  ; (0x17d8b8, [C8 (Z_to_bv 64 0x70)])
  ; (0x17d7a0, [C8 (Z_to_bv 64 0x12081c); C8 (Z_to_bv 64 0x1213f0)])
  ; (0x180ba0, [C8 (Z_to_bv 64 0x31890)])
  ; (0x181d68, [C8 (Z_to_bv 64 0x171d80); C8 (Z_to_bv 64 0x171cac)])
  ; (0x21b5a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x17dce0, [C8 (Z_to_bv 64 0x148f54)])
  ; (0x180ba8, [C8 (Z_to_bv 64 0x6bcee0)])
  ; (0x17d058, [C8 (Z_to_bv 64 0x17d258); C8 (Z_to_bv 64 0x316a8)])
  ; (0x17d230, [C8 (Z_to_bv 64 0x17d2a8); C8 (Z_to_bv 64 0x31767)])
  ; (0x17d278, [C8 (Z_to_bv 64 0x118a60)])
  ; (0x17d290, [C8 (Z_to_bv 64 0x118dc4); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17d2e8)])
  ; (0x17d2d0, [C8 (Z_to_bv 64 0x119a38)])
  ; (0x17d2e0, [C8 (Z_to_bv 64 0x118e40); C8 (Z_to_bv 64 0x17d2a8); C8 (Z_to_bv 64 0x31789); C8 (Z_to_bv 64 0x17d230)])
  ; (0x17fc90, [C8 (Z_to_bv 64 0x15a3dc); C8 (Z_to_bv 64 0x15a414); C8 (Z_to_bv 64 0x15a4b0)])
  ; (0x17fcc0, [C8 (Z_to_bv 64 0x15a5d4); C8 (Z_to_bv 64 0x15a6bc); C8 (Z_to_bv 64 0x15a6e4)])
  ; (0x17fce8, [C8 (Z_to_bv 64 0x15a790)])
  ; (0x17fe70, [C8 (Z_to_bv 64 0x0)])
  ; (0x180bc8, [C8 (Z_to_bv 64 0x184a50)])
  ; (0x180bd0, [C8 (Z_to_bv 64 0x184a48)])
  ; (0x181d80, [C8 (Z_to_bv 64 0x164348)])
  ; (0x17dce8, [C8 (Z_to_bv 64 0x148f5c)])
  ; (0x17e888, [C8 (Z_to_bv 64 0x12d6e0)])
  ; (0x17e890, [C8 (Z_to_bv 64 0x12d978); C8 (Z_to_bv 64 0x12dc24); C8 (Z_to_bv 64 0x12ded0); C8 (Z_to_bv 64 0x12e158); C8 (Z_to_bv 64 0x12e3e0)])
  ; (0x17de78, [C8 (Z_to_bv 64 0x14c140); C8 (Z_to_bv 64 0x14c150); C8 (Z_to_bv 64 0x14c160)])
  ; (0x17ff60, [C8 (Z_to_bv 64 0x183fb4)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10e24, 10)
  ; (0x15046, 4)
  ; (0x16412, 17)
  ; (0x16400, 128)
  ; (0x1ae83, 33)
  ; (0x1f63a, 21)
  ; (0x1f64f, 23)
  ; (0x21ec0, 128)
  ; (0x23192, 7)
  ; (0x23192, 7)
  ; (0x38030, 16)
  ; (0x6abfc0, 16)
  ; (0x13f96, 19)
  ; (0x14a9e, 1)
  ; (0x17eff, 3)
  ; (0x1a5dc, 3)
  ; (0x200fe, 3)
  ; (0x20df7, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x181d88, 0x181d98); (0x187230, 0x187238);   (0x181ee0, 0x181ee8); (0x181e38, 0x181e40); (0x181e00, 0x181e08); (0x183fb4, 0x183fb8); (0x187194, 0x187195); (0x17d5c0, 0x17d5c8); (0x17d6e0, 0x17d6e8); (0x17da68, 0x17da70); (0x17db98, 0x17dba0); (0x17de28, 0x17de30); (0x17e0d8, 0x17e0e0);
    (0x1799e0, 0x1799f0); (0x17fdb8, 0x17fdc0); (0x17fe98, 0x17fea8); (0x180b30, 0x180b40); (0x180bb0, 0x180bc0); (0x180ce8, 0x180cf8);
    (0x181d40, 0x181d48); (0x181db8, 0x181dd0); (0x187190, 0x187194); (0x1871d8, 0x1871d9); (0x21b4fc, 0x21b4fd); (0x21b820, 0x21b821);
    (0x17a080, 0x17a0c0); (0x17a140, 0x17a1a0);   (0x180b50, 0x180b70);   (0x17d908, 0x17d930);   (0x17d8b8, 0x17d8c0);   (0x17d7a0, 0x17d7b0); (0x180ba0, 0x180ba8); (0x181d68, 0x181d78); (0x21b5a6, 0x21b5a8);
      (0x17dce0, 0x17dce8); (0x180ba8, 0x180bb0);
      (0x17d058, 0x17d068); (0x17d230, 0x17d240); (0x17d278, 0x17d280); (0x17d290, 0x17d2a8); (0x17d2d0, 0x17d2d8); (0x17d2e0, 0x17d300); (0x17fc90, 0x17fca8); (0x17fcc0, 0x17fcd8); (0x17fce8, 0x17fcf0); (0x17fe70, 0x17fe78); (0x180bc8, 0x180bd0); (0x180bd0, 0x180bd8); (0x181d80, 0x181d88);
      (0x17dce8, 0x17dcf0);   (0x17e888, 0x17e890); (0x17e890, 0x17e8b8); (0x17de78, 0x17de90)  ;   (0x17ff60, 0x17ff68) ].

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
  [ (0x17a080, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17a0e0); C8 (Z_to_bv 64 0xf57bc); C8 (Z_to_bv 64 0xf595c); C8 (Z_to_bv 64 0xf5afc); C8 (Z_to_bv 64 0xc1c7c); C8 (Z_to_bv 64 0xc4dbc); C8 (Z_to_bv 64 0xc4fa4)])
  ; (0x17a140, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17a1c0); C8 (Z_to_bv 64 0xf5768); C8 (Z_to_bv 64 0xc1f1c); C8 (Z_to_bv 64 0xc53f8); C8 (Z_to_bv 64 0xdcde0); C8 (Z_to_bv 64 0xf4678); C8 (Z_to_bv 64 0xf4f1c); C8 (Z_to_bv 64 0xf5b44); C8 (Z_to_bv 64 0xf5cb8); C8 (Z_to_bv 64 0xf5e2c); C8 (Z_to_bv 64 0xf5f18)])
  ; (0x180b50, [C8 (Z_to_bv 64 0x17d908); C8 (Z_to_bv 64 0x17d730); C8 (Z_to_bv 64 0x17d4f0); C8 (Z_to_bv 64 0x17d8b8)])
  ; (0x17d908, [C8 (Z_to_bv 64 0x17d8d0); C8 (Z_to_bv 64 0x17d940); C8 (Z_to_bv 64 0x17d968); C8 (Z_to_bv 64 0x17d8f8); C8 (Z_to_bv 64 0x70)])
  ; (0x17d8b8, [C8 (Z_to_bv 64 0x70)])
  ; (0x17d7a0, [C8 (Z_to_bv 64 0x12081c); C8 (Z_to_bv 64 0x1213f0)])
  ; (0x180ba0, [C8 (Z_to_bv 64 0x31890)])
  ; (0x181d68, [C8 (Z_to_bv 64 0x171d80); C8 (Z_to_bv 64 0x171cac)])
  ; (0x21b5a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x17dce0, [C8 (Z_to_bv 64 0x148f54)])
  ; (0x180ba8, [C8 (Z_to_bv 64 0x6bcee0)])
  ; (0x17d058, [C8 (Z_to_bv 64 0x17d258); C8 (Z_to_bv 64 0x316a8)])
  ; (0x17d230, [C8 (Z_to_bv 64 0x17d2a8); C8 (Z_to_bv 64 0x31767)])
  ; (0x17d278, [C8 (Z_to_bv 64 0x118a60)])
  ; (0x17d290, [C8 (Z_to_bv 64 0x118dc4); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x17d2e8)])
  ; (0x17d2d0, [C8 (Z_to_bv 64 0x119a38)])
  ; (0x17d2e0, [C8 (Z_to_bv 64 0x118e40); C8 (Z_to_bv 64 0x17d2a8); C8 (Z_to_bv 64 0x31789); C8 (Z_to_bv 64 0x17d230)])
  ; (0x17fc90, [C8 (Z_to_bv 64 0x15a3dc); C8 (Z_to_bv 64 0x15a414); C8 (Z_to_bv 64 0x15a4b0)])
  ; (0x17fcc0, [C8 (Z_to_bv 64 0x15a5d4); C8 (Z_to_bv 64 0x15a6bc); C8 (Z_to_bv 64 0x15a6e4)])
  ; (0x17fce8, [C8 (Z_to_bv 64 0x15a790)])
  ; (0x17fe70, [C8 (Z_to_bv 64 0x0)])
  ; (0x180bc8, [C8 (Z_to_bv 64 0x184a50)])
  ; (0x180bd0, [C8 (Z_to_bv 64 0x184a48)])
  ; (0x181d80, [C8 (Z_to_bv 64 0x164348)])
  ; (0x17dce8, [C8 (Z_to_bv 64 0x148f5c)])
  ; (0x17e888, [C8 (Z_to_bv 64 0x12d6e0)])
  ; (0x17e890, [C8 (Z_to_bv 64 0x12d978); C8 (Z_to_bv 64 0x12dc24); C8 (Z_to_bv 64 0x12ded0); C8 (Z_to_bv 64 0x12e158); C8 (Z_to_bv 64 0x12e3e0)])
  ; (0x17de78, [C8 (Z_to_bv 64 0x14c140); C8 (Z_to_bv 64 0x14c150); C8 (Z_to_bv 64 0x14c160)])
 ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
