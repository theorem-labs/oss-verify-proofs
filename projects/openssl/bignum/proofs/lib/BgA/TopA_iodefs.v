(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Cells Step. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5a7c20, [C8 (Z_to_bv 64 0x52de08); C8 (Z_to_bv 64 0x521fdc); C8 (Z_to_bv 64 0x52243c)])
  ; (0x66a9f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x52ee60, [C8 (Z_to_bv 64 0x1f3e04); C8 (Z_to_bv 64 0x199a84); C8 (Z_to_bv 64 0x1f3380)])
  ; (0x5a4aa8, [C8 (Z_to_bv 64 0x5aad68)])
  ; (0x5a4b88, [C8 (Z_to_bv 64 0x51b3dc); C8 (Z_to_bv 64 0)])
  ; (0x5a5838, [C8 (Z_to_bv 64 0x5a4aa8); C8 (Z_to_bv 64 0x1f2fe4)])
  ; (0x5a6b08, [C8 (Z_to_bv 64 0x5ab060); C8 (Z_to_bv 64 0x669a60)])
  ; (0x5a6b50, [C8 (Z_to_bv 64 0x52ee78); C8 (Z_to_bv 64 0x52ee60)])
  ; (0x5a7bc0, [C8 (Z_to_bv 64 0x5a7bc0)])
  ; (0x5a7c58, [C8 (Z_to_bv 64 0x52597c); C8 (Z_to_bv 64 0x522820); C8 (Z_to_bv 64 0x52599c)])
  ; (0x66a950, [C4 (Z_to_bv 64 1)])
  ; (0x6fecbc, [C1 (Z_to_bv 8 1)])
  ; (0x6fefe0, [C1 (Z_to_bv 8 0)]) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121f3, 10)
  ; (0x1daa5, 4)
  ; (0x21267, 17)
  ; (0x21240, 128)
  ; (0x2ef08, 33)
  ; (0x3cc48, 21)
  ; (0x3cc5d, 23)
  ; (0x44040, 128)
  ; (0x488dc, 7)
  ; (0x11a1b0, 16)
  ; (0xb8f780, 16)    ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bgasegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bgasegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bgasegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x5a7c20, 0x5a7c38); (0x66a9f0, 0x66a9f8);
    (0x52ee60, 0x52ee78); (0x5a4aa8, 0x5a4ab0); (0x5a4b88, 0x5a4b98); (0x5a5838, 0x5a5848); (0x5a6b08, 0x5a6b18); (0x5a6b50, 0x5a6b60);
    (0x5a7bc0, 0x5a7bc8); (0x5a7c58, 0x5a7c70); (0x66a950, 0x66a954); (0x6fecbc, 0x6fecbd); (0x6fefe0, 0x6fefe1) ].

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bgasegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bgasegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bgasegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
