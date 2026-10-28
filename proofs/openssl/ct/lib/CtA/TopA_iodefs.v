(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Cells Step. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5ac2e0, [C8 (Z_to_bv 64 0x5323d4); C8 (Z_to_bv 64 0x526710); C8 (Z_to_bv 64 0x526b70)])              (* [comment removed for export] *)
  ; (0x66f8f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x533428, [C8 (Z_to_bv 64 0x1f43d0); C8 (Z_to_bv 64 0x19ab8c); C8 (Z_to_bv 64 0x1f4400)])            (* [comment removed for export] *)
  ; (0x5a9128, [C8 (Z_to_bv 64 0x5af428)])                                        (* [comment removed for export] *)
  ; (0x5a9208, [C8 (Z_to_bv 64 0x51fb10); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5a9eb8, [C8 (Z_to_bv 64 0x5a9128); C8 (Z_to_bv 64 0x1f40ec)])              (* [comment removed for export] *)
  ; (0x5ab1c8, [C8 (Z_to_bv 64 0x5af720); C8 (Z_to_bv 64 0x66e960)])              (* [comment removed for export] *)
  ; (0x5ab210, [C8 (Z_to_bv 64 0x533440); C8 (Z_to_bv 64 0x533428)])              (* [comment removed for export] *)
  ; (0x5ac280, [C8 (Z_to_bv 64 0x5ac280)])                                        (* [comment removed for export] *)
  ; (0x5ac318, [C8 (Z_to_bv 64 0x529f48); C8 (Z_to_bv 64 0x526dec); C8 (Z_to_bv 64 0x529f68)])  (* [comment removed for export] *)
  ; (0x66f850, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x703bbc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x703ee0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=   (* [comment removed for export] *)
  [ (0x121fb, 10)   (* [comment removed for export] *)
  ; (0x1db09, 4)    (* [comment removed for export] *)
  ; (0x212eb, 17)   (* [comment removed for export] *)
  ; (0x212c0, 128)  (* [comment removed for export] *)
  ; (0x2efb9, 33)   (* [comment removed for export] *)
  ; (0x3cd30, 21)   (* [comment removed for export] *)
  ; (0x3cd45, 23)   (* [comment removed for export] *)
  ; (0x44140, 128)  (* [comment removed for export] *)
  ; (0x48a10, 7)    (* [comment removed for export] *)
  ; (0x11a9d0, 16)   (* [comment removed for export] *)
  ; (0xb94680, 16)  (* [comment removed for export] *) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells ctasegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells ctasegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc ctasegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5ac2e0, 0x5ac2f8); (0x66f8f0, 0x66f8f8);
    (0x533428, 0x533440); (0x5a9128, 0x5a9130); (0x5a9208, 0x5a9218); (0x5a9eb8, 0x5a9ec8); (0x5ab1c8, 0x5ab1d8); (0x5ab210, 0x5ab220);
    (0x5ac280, 0x5ac288); (0x5ac318, 0x5ac330); (0x66f850, 0x66f854); (0x703bbc, 0x703bbd); (0x703ee0, 0x703ee1) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells ctasegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells ctasegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc ctasegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
