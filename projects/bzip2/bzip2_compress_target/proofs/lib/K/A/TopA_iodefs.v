(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xceb80, [C8 (Z_to_bv 64 0xcb868); C8 (Z_to_bv 64 0xc276c)])              (* [comment removed for export] *)
  ; (0xd3df0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xcc8c0, [C8 (Z_to_bv 64 0x81638); C8 (Z_to_bv 64 0x31788)])              (* [comment removed for export] *)
  ; (0xccd30, [C8 (Z_to_bv 64 0xd2368)])                                        (* [comment removed for export] *)
  ; (0xcce08, [C8 (Z_to_bv 64 0xbc610); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcda98, [C8 (Z_to_bv 64 0xccd30); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcdaa8, [C8 (Z_to_bv 64 0xccd38)])
  ; (0xcdac0, [C8 (Z_to_bv 64 0xd2660); C8 (Z_to_bv 64 0xd2e60)])              (* [comment removed for export] *)
  ; (0xcdb00, [C8 (Z_to_bv 64 0xcc8d0); C8 (Z_to_bv 64 0xcc8c0)])              (* [comment removed for export] *)
  ; (0xceb40, [C8 (Z_to_bv 64 0xceb40)])                                        (* [comment removed for export] *)
  ; (0xceba0, [C8 (Z_to_bv 64 0xc5ab0); C8 (Z_to_bv 64 0xc29a0); C8 (Z_to_bv 64 0xc5acc)])  (* [comment removed for export] *)
  ; (0xd3d50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1680bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1683e0, [C1 (Z_to_bv 8 0)])                                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0xceb60, [C8 (Z_to_bv 64 0xc6134); C8 (Z_to_bv 64 0xc6064)])              (* [comment removed for export] *)
  ; (0x168166, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].                         (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10bc0, 10)     (* [comment removed for export] *)
  ; (0x148af, 4)      (* [comment removed for export] *)
  ; (0x15940, 128)    (* [comment removed for export] *)
  ; (0x197df, 33)     (* [comment removed for export] *)
  ; (0x1d821, 21)     (* [comment removed for export] *)
  ; (0x1d836, 23)     (* [comment removed for export] *)
  ; (0x1f980, 128)    (* [comment removed for export] *)
  ; (0x20752, 7)      (* [comment removed for export] *)
  ; (0x234e0, 16)     (* [comment removed for export] *)
  ; (0x5f8b80, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xc17a0, [C8 (Z_to_bv 64 0xbe488); C8 (Z_to_bv 64 0xb538c)])              (* [comment removed for export] *)
  ; (0xc69f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xbf4e0, [C8 (Z_to_bv 64 0x81bf4); C8 (Z_to_bv 64 0x318a0)])              (* [comment removed for export] *)
  ; (0xbf950, [C8 (Z_to_bv 64 0xc4f28)])                                        (* [comment removed for export] *)
  ; (0xbfa28, [C8 (Z_to_bv 64 0xaf230); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc06b8, [C8 (Z_to_bv 64 0xbf950); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc06c8, [C8 (Z_to_bv 64 0xbf958)])
  ; (0xc06e0, [C8 (Z_to_bv 64 0xc5220); C8 (Z_to_bv 64 0xc5a60)])              (* [comment removed for export] *)
  ; (0xc0720, [C8 (Z_to_bv 64 0xbf4f0); C8 (Z_to_bv 64 0xbf4e0)])              (* [comment removed for export] *)
  ; (0xc1760, [C8 (Z_to_bv 64 0xc1760)])                                        (* [comment removed for export] *)
  ; (0xc17c0, [C8 (Z_to_bv 64 0xb86d0); C8 (Z_to_bv 64 0xb55c0); C8 (Z_to_bv 64 0xb86ec)])  (* [comment removed for export] *)
  ; (0xc6950, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x15acbc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x15afe0, [C1 (Z_to_bv 8 0)])                                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0xc1780, [C8 (Z_to_bv 64 0xb8d54); C8 (Z_to_bv 64 0xb8c84)])              (* [comment removed for export] *)
  ; (0x15ad66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) ].                         (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10bc0, 10)     (* [comment removed for export] *)
  ; (0x148af, 4)      (* [comment removed for export] *)
  ; (0x15940, 128)    (* [comment removed for export] *)
  ; (0x197df, 33)     (* [comment removed for export] *)
  ; (0x1d821, 21)     (* [comment removed for export] *)
  ; (0x1d836, 23)     (* [comment removed for export] *)
  ; (0x1f980, 128)    (* [comment removed for export] *)
  ; (0x20752, 7)      (* [comment removed for export] *)
  ; (0x235f0, 16)     (* [comment removed for export] *)
  ; (0x5eb780, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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
