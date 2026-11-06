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
  [ (0x5dff80, [C8 (Z_to_bv 64 0x5665ec); C8 (Z_to_bv 64 0x55a7c0); C8 (Z_to_bv 64 0x55ac20)])
  ; (0x69d2f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x567640, [C8 (Z_to_bv 64 0x1eee38); C8 (Z_to_bv 64 0x194a70); C8 (Z_to_bv 64 0x1ee3b4)])
  ; (0x5dce08, [C8 (Z_to_bv 64 0x5e3388)])
  ; (0x5dcee8, [C8 (Z_to_bv 64 0x553bc0); C8 (Z_to_bv 64 0)])
  ; (0x5ddb98, [C8 (Z_to_bv 64 0x5dce08); C8 (Z_to_bv 64 0x1edfd0)])
  ; (0x5dee70, [C8 (Z_to_bv 64 0x5e3680); C8 (Z_to_bv 64 0x69c380)])
  ; (0x5deeb8, [C8 (Z_to_bv 64 0x567658); C8 (Z_to_bv 64 0x567640)])
  ; (0x5dff20, [C8 (Z_to_bv 64 0x5dff20)])
  ; (0x5dffb8, [C8 (Z_to_bv 64 0x55e160); C8 (Z_to_bv 64 0x55b004); C8 (Z_to_bv 64 0x55e180)])
  ; (0x69d250, [C4 (Z_to_bv 64 1)])
  ; (0x7315bc, [C1 (Z_to_bv 8 1)])
  ; (0x7318e0, [C1 (Z_to_bv 8 0)]) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121f1, 10)
  ; (0x1d8f2, 4)
  ; (0x210f1, 17)
  ; (0x21100, 128)
  ; (0x2ef2f, 33)
  ; (0x3d19e, 21)
  ; (0x3d1b3, 23)
  ; (0x44540, 128)
  ; (0x48d28, 7)
  ; (0x113530, 16)
  ; (0xbc2080, 16)    ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bgbsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bgbsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bgbsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x5dff80, 0x5dff98); (0x69d2f0, 0x69d2f8);
    (0x567640, 0x567658); (0x5dce08, 0x5dce10); (0x5dcee8, 0x5dcef8); (0x5ddb98, 0x5ddba8); (0x5dee70, 0x5dee80); (0x5deeb8, 0x5deec8);
    (0x5dff20, 0x5dff28); (0x5dffb8, 0x5dffd0); (0x69d250, 0x69d254); (0x7315bc, 0x7315bd); (0x7318e0, 0x7318e1) ].

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bgbsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bgbsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bgbsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
