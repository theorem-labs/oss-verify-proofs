(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x16baf8, [C8 (Z_to_bv 64 0x162d58); C8 (Z_to_bv 64 0x153754)])
  ; (0x16ff30, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x163ed8, [C8 (Z_to_bv 64 0xb8ebc); C8 (Z_to_bv 64 0x5af8c)])
  ; (0x169ba8, [C8 (Z_to_bv 64 0x16e490)])
  ; (0x169c80, [C8 (Z_to_bv 64 0x14b0e8); C8 (Z_to_bv 64 0)])
  ; (0x16a918, [C8 (Z_to_bv 64 0x169ba8); C8 (Z_to_bv 64 0)])
  ; (0x16a978, [C8 (Z_to_bv 64 0x16e790); C8 (Z_to_bv 64 0x16ef90)])
  ; (0x16aa70, [C8 (Z_to_bv 64 0x163ee8); C8 (Z_to_bv 64 0x163ed8)])
  ; (0x16bab0, [C8 (Z_to_bv 64 0x16bab0)])
  ; (0x16bb28, [C8 (Z_to_bv 64 0x159e50); C8 (Z_to_bv 64 0x153b6c); C8 (Z_to_bv 64 0x159e6c)])
  ; (0x16fe90, [C4 (Z_to_bv 64 1)])
  ; (0x16fed8, [C1 (Z_to_bv 8 1)])
  ; (0x2041fc, [C1 (Z_to_bv 8 1)])
  ; (0x204520, [C1 (Z_to_bv 8 0)])
  ; (0x164480, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1644e0); C8 (Z_to_bv 64 0xe3208); C8 (Z_to_bv 64 0xe3394); C8 (Z_to_bv 64 0xe3520); C8 (Z_to_bv 64 0xba5a0); C8 (Z_to_bv 64 0xbcb90); C8 (Z_to_bv 64 0xbcd20)])
  ; (0x164540, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1645c0); C8 (Z_to_bv 64 0xe31b4); C8 (Z_to_bv 64 0xba7fc); C8 (Z_to_bv 64 0xbd134); C8 (Z_to_bv 64 0xcfb8c); C8 (Z_to_bv 64 0xe2278); C8 (Z_to_bv 64 0xe2a2c); C8 (Z_to_bv 64 0xe3568); C8 (Z_to_bv 64 0xe36c8); C8 (Z_to_bv 64 0xe3830); C8 (Z_to_bv 64 0xe391c)])
  ; (0x16a968, [C8 (Z_to_bv 64 0x30548)])
  ; (0x16bad8, [C8 (Z_to_bv 64 0x15c324); C8 (Z_to_bv 64 0x15c254)])
  ; (0x2042a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x164348, [C8 (Z_to_bv 64 0x10d8e0); C8 (Z_to_bv 64 0xb2b1c); C8 (Z_to_bv 64 8)])
  ; (0x16a930, [C8 (Z_to_bv 64 0x1678f0); C8 (Z_to_bv 64 0x167970)])
  ; (0x167ad0, [C8 (Z_to_bv 64 0x133ac8)])
  ; (0x16a970, [C8 (Z_to_bv 64 0x6a53a0)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10e27, 10)
  ; (0x14fb8, 4)
  ; (0x16351, 17)
  ; (0x16340, 128)
  ; (0x1acbf, 33)
  ; (0x1f549, 21)
  ; (0x1f55e, 23)
  ; (0x21c40, 128)
  ; (0x22d29, 7)
  ; (0x22d29, 7)
  ; (0x36b10, 16)
  ; (0x694cc0, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x16baf8, 0x16bb08); (0x16ff30, 0x16ff38);
    (0x163ed8, 0x163ee8); (0x169ba8, 0x169bb0); (0x169c80, 0x169c90); (0x16a918, 0x16a928); (0x16a978, 0x16a988); (0x16aa70, 0x16aa80);
    (0x16bab0, 0x16bab8); (0x16bb28, 0x16bb40); (0x16fe90, 0x16fe94); (0x16fed8, 0x16fed9); (0x2041fc, 0x2041fd); (0x204520, 0x204521);
    (0x164480, 0x1644c0); (0x164540, 0x1645a0); (0x16a968, 0x16a970); (0x16bad8, 0x16bae8); (0x2042a6, 0x2042a8);
    (0x164348, 0x164360); (0x16a930, 0x16a940); (0x167ad0, 0x167ad8); (0x16a970, 0x16a978) ].

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
  [ (0x164480, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1644e0); C8 (Z_to_bv 64 0xe3208); C8 (Z_to_bv 64 0xe3394); C8 (Z_to_bv 64 0xe3520); C8 (Z_to_bv 64 0xba5a0); C8 (Z_to_bv 64 0xbcb90); C8 (Z_to_bv 64 0xbcd20)])
  ; (0x164540, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1645c0); C8 (Z_to_bv 64 0xe31b4); C8 (Z_to_bv 64 0xba7fc); C8 (Z_to_bv 64 0xbd134); C8 (Z_to_bv 64 0xcfb8c); C8 (Z_to_bv 64 0xe2278); C8 (Z_to_bv 64 0xe2a2c); C8 (Z_to_bv 64 0xe3568); C8 (Z_to_bv 64 0xe36c8); C8 (Z_to_bv 64 0xe3830); C8 (Z_to_bv 64 0xe391c)])
  ; (0x16a968, [C8 (Z_to_bv 64 0x30548)])
  ; (0x16bad8, [C8 (Z_to_bv 64 0x15c324); C8 (Z_to_bv 64 0x15c254)])
  ; (0x2042a6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x164348, [C8 (Z_to_bv 64 0x10d8e0); C8 (Z_to_bv 64 0xb2b1c); C8 (Z_to_bv 64 8)])
  ; (0x16a930, [C8 (Z_to_bv 64 0x1678f0); C8 (Z_to_bv 64 0x167970)])
  ; (0x167ad0, [C8 (Z_to_bv 64 0x133ac8)])
  ; (0x16a970, [C8 (Z_to_bv 64 0x6a53a0)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
