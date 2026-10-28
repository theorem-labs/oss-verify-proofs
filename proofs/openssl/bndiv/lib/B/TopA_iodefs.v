(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5e3d40, [C8 (Z_to_bv 64 0x56a398); C8 (Z_to_bv 64 0x55e48c); C8 (Z_to_bv 64 0x55e8ec)])              (* [comment removed for export] *)
  ; (0x6a12b0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x56b3f0, [C8 (Z_to_bv 64 0x1ee8d4); C8 (Z_to_bv 64 0x194a98); C8 (Z_to_bv 64 0x20c324)])            (* [comment removed for export] *)
  ; (0x5e0bc8, [C8 (Z_to_bv 64 0x5e7168)])                                        (* [comment removed for export] *)
  ; (0x5e0ca8, [C8 (Z_to_bv 64 0x55788c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5e1958, [C8 (Z_to_bv 64 0x5e0bc8); C8 (Z_to_bv 64 0x1ee358)])              (* [comment removed for export] *)
  ; (0x5e2c28, [C8 (Z_to_bv 64 0x5e7460); C8 (Z_to_bv 64 0x6a0320)])              (* [comment removed for export] *)
  ; (0x5e2c70, [C8 (Z_to_bv 64 0x56b408); C8 (Z_to_bv 64 0x56b3f0)])              (* [comment removed for export] *)
  ; (0x5e3ce0, [C8 (Z_to_bv 64 0x5e3ce0)])                                        (* [comment removed for export] *)
  ; (0x5e3d80, [C8 (Z_to_bv 64 0x561f0c); C8 (Z_to_bv 64 0x55edb0); C8 (Z_to_bv 64 0x561f2c)])  (* [comment removed for export] *)
  ; (0x6a1210, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x73557c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x7358a0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=   (* [comment removed for export] *)
  [ (0x121e9, 10)   (* [comment removed for export] *)
  ; (0x1d8ea, 4)    (* [comment removed for export] *)
  ; (0x210ec, 17)   (* [comment removed for export] *)
  ; (0x210c0, 128)  (* [comment removed for export] *)
  ; (0x2ef35, 33)   (* [comment removed for export] *)
  ; (0x3d197, 21)   (* [comment removed for export] *)
  ; (0x3d1ac, 23)   (* [comment removed for export] *)
  ; (0x44540, 128)  (* [comment removed for export] *)
  ; (0x48d09, 7)    (* [comment removed for export] *)
  ; (0x1134e8, 16)   (* [comment removed for export] *)
  ; (0xbc6040, 16)  (* [comment removed for export] *) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5e3d40, 0x5e3d58); (0x6a12b0, 0x6a12b8);
    (0x56b3f0, 0x56b408); (0x5e0bc8, 0x5e0bd0); (0x5e0ca8, 0x5e0cb8); (0x5e1958, 0x5e1968); (0x5e2c28, 0x5e2c38); (0x5e2c70, 0x5e2c80);
    (0x5e3ce0, 0x5e3ce8); (0x5e3d80, 0x5e3d98); (0x6a1210, 0x6a1214); (0x73557c, 0x73557d); (0x7358a0, 0x7358a1) ].

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
