(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5ab540, [C8 (Z_to_bv 64 0x531714); C8 (Z_to_bv 64 0x525808); C8 (Z_to_bv 64 0x525c68)])              (* [comment removed for export] *)
  ; (0x66e4f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x532768, [C8 (Z_to_bv 64 0x1f394c); C8 (Z_to_bv 64 0x199b34); C8 (Z_to_bv 64 0x20f73c)])            (* [comment removed for export] *)
  ; (0x5a83c8, [C8 (Z_to_bv 64 0x5ae6a8)])                                        (* [comment removed for export] *)
  ; (0x5a84a8, [C8 (Z_to_bv 64 0x51ec08); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5a9158, [C8 (Z_to_bv 64 0x5a83c8); C8 (Z_to_bv 64 0x1f33f4)])              (* [comment removed for export] *)
  ; (0x5aa420, [C8 (Z_to_bv 64 0x5ae9a0); C8 (Z_to_bv 64 0x66d560)])              (* [comment removed for export] *)
  ; (0x5aa468, [C8 (Z_to_bv 64 0x532780); C8 (Z_to_bv 64 0x532768)])              (* [comment removed for export] *)
  ; (0x5ab4e0, [C8 (Z_to_bv 64 0x5ab4e0)])                                        (* [comment removed for export] *)
  ; (0x5ab580, [C8 (Z_to_bv 64 0x529288); C8 (Z_to_bv 64 0x52612c); C8 (Z_to_bv 64 0x5292a8)])  (* [comment removed for export] *)
  ; (0x66e450, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x7027bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x702ae0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=   (* [comment removed for export] *)
  [ (0x121eb, 10)   (* [comment removed for export] *)
  ; (0x1da9d, 4)    (* [comment removed for export] *)
  ; (0x21262, 17)   (* [comment removed for export] *)
  ; (0x21240, 128)  (* [comment removed for export] *)
  ; (0x2ef0e, 33)   (* [comment removed for export] *)
  ; (0x3cc41, 21)   (* [comment removed for export] *)
  ; (0x3cc56, 23)   (* [comment removed for export] *)
  ; (0x44040, 128)  (* [comment removed for export] *)
  ; (0x488bd, 7)    (* [comment removed for export] *)
  ; (0x11a1f0, 16)   (* [comment removed for export] *)
  ; (0xb93280, 16)  (* [comment removed for export] *) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5ab540, 0x5ab558); (0x66e4f0, 0x66e4f8);
    (0x532768, 0x532780); (0x5a83c8, 0x5a83d0); (0x5a84a8, 0x5a84b8); (0x5a9158, 0x5a9168); (0x5aa420, 0x5aa430); (0x5aa468, 0x5aa478);
    (0x5ab4e0, 0x5ab4e8); (0x5ab580, 0x5ab598); (0x66e450, 0x66e454); (0x7027bc, 0x7027bd); (0x702ae0, 0x702ae1) ].

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
