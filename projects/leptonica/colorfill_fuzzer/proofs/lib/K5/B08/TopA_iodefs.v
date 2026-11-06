(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xce560, [C8 (Z_to_bv 64 0xc8210); C8 (Z_to_bv 64 0xbf114)])              (* [comment removed for export] *)
  ; (0xd41b0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc9390, [C8 (Z_to_bv 64 0x8db2c); C8 (Z_to_bv 64 0x3c150)])              (* [comment removed for export] *)
  ; (0xcc6c8, [C8 (Z_to_bv 64 0xd0ea8)])                                        (* [comment removed for export] *)
  ; (0xcc7a0, [C8 (Z_to_bv 64 0xb8f5c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcd430, [C8 (Z_to_bv 64 0xcc6c8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcd450, [C8 (Z_to_bv 64 0xd11a0); C8 (Z_to_bv 64 0xd3220)])              (* [comment removed for export] *)
  ; (0xcd4d8, [C8 (Z_to_bv 64 0xc93a0); C8 (Z_to_bv 64 0xc9390)])              (* [comment removed for export] *)
  ; (0xce520, [C8 (Z_to_bv 64 0xce520)])                                        (* [comment removed for export] *)
  ; (0xce588, [C8 (Z_to_bv 64 0xc2458); C8 (Z_to_bv 64 0xbf348); C8 (Z_to_bv 64 0xc2474)])  (* [comment removed for export] *)
  ; (0xd4110, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x16847c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1687a0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10cc1, 10)     (* [comment removed for export] *)
  ; (0x14dcd, 4)      (* [comment removed for export] *)
  ; (0x16100, 128)    (* [comment removed for export] *)
  ; (0x1a824, 33)     (* [comment removed for export] *)
  ; (0x1eeec, 21)     (* [comment removed for export] *)
  ; (0x1ef01, 23)     (* [comment removed for export] *)
  ; (0x214c0, 128)    (* [comment removed for export] *)
  ; (0x224f3, 7)      (* [comment removed for export] *)
  ; (0x27c78, 16)     (* [comment removed for export] *)
  ; (0x5f8f40, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xce560, 0xce570); (0xd41b0, 0xd41b8);
    (0xc9390, 0xc93a0); (0xcc6c8, 0xcc6d0); (0xcc7a0, 0xcc7b0); (0xcd430, 0xcd440); (0xcd450, 0xcd460); (0xcd4d8, 0xcd4e8);
    (0xce520, 0xce528); (0xce588, 0xce5a0); (0xd4110, 0xd4114); (0x16847c, 0x16847d); (0x1687a0, 0x1687a1) ].

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
