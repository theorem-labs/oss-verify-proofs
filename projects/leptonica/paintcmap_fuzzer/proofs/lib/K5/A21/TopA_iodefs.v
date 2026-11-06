(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcefc0, [C8 (Z_to_bv 64 0xc8c5c); C8 (Z_to_bv 64 0xbfb60)])              (* [comment removed for export] *)
  ; (0xd4af0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc9de0, [C8 (Z_to_bv 64 0x8db74); C8 (Z_to_bv 64 0x3bf48)])              (* [comment removed for export] *)
  ; (0xcd118, [C8 (Z_to_bv 64 0xd1908)])                                        (* [comment removed for export] *)
  ; (0xcd1f0, [C8 (Z_to_bv 64 0xb99a8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcde80, [C8 (Z_to_bv 64 0xcd118); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcdea0, [C8 (Z_to_bv 64 0xd1c00); C8 (Z_to_bv 64 0xd3b80)])              (* [comment removed for export] *)
  ; (0xcdf28, [C8 (Z_to_bv 64 0xc9df0); C8 (Z_to_bv 64 0xc9de0)])              (* [comment removed for export] *)
  ; (0xcef80, [C8 (Z_to_bv 64 0xcef80)])                                        (* [comment removed for export] *)
  ; (0xcefe8, [C8 (Z_to_bv 64 0xc2ea4); C8 (Z_to_bv 64 0xbfd94); C8 (Z_to_bv 64 0xc2ec0)])  (* [comment removed for export] *)
  ; (0xd4a50, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x168dbc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1690e0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10cbc, 10)     (* [comment removed for export] *)
  ; (0x14d58, 4)      (* [comment removed for export] *)
  ; (0x16080, 192)    (* [comment removed for export] *)
  ; (0x1a837, 33)     (* [comment removed for export] *)
  ; (0x1ef65, 21)     (* [comment removed for export] *)
  ; (0x1ef7a, 23)     (* [comment removed for export] *)
  ; (0x215c0, 128)    (* [comment removed for export] *)
  ; (0x225db, 7)      (* [comment removed for export] *)
  ; (0x27ab8, 16)     (* [comment removed for export] *)
  ; (0x5f9880, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcefc0, 0xcefd0); (0xd4af0, 0xd4af8);
    (0xc9de0, 0xc9df0); (0xcd118, 0xcd120); (0xcd1f0, 0xcd200); (0xcde80, 0xcde90); (0xcdea0, 0xcdeb0); (0xcdf28, 0xcdf38);
    (0xcef80, 0xcef88); (0xcefe8, 0xcf000); (0xd4a50, 0xd4a54); (0x168dbc, 0x168dbd); (0x1690e0, 0x1690e1) ].

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
