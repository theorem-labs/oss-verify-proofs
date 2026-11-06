(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Cells Step. 
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5e4be0, [C8 (Z_to_bv 64 0x56b158); C8 (Z_to_bv 64 0x55f494); C8 (Z_to_bv 64 0x55f8f4)])              (* [comment removed for export] *)
  ; (0x6a2730, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x56c1b0, [C8 (Z_to_bv 64 0x1ef360); C8 (Z_to_bv 64 0x195b1c); C8 (Z_to_bv 64 0x1ef390)])            (* [comment removed for export] *)
  ; (0x5e1a28, [C8 (Z_to_bv 64 0x5e7fe8)])                                        (* [comment removed for export] *)
  ; (0x5e1b08, [C8 (Z_to_bv 64 0x558894); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5e27b8, [C8 (Z_to_bv 64 0x5e1a28); C8 (Z_to_bv 64 0x1ef07c)])              (* [comment removed for export] *)
  ; (0x5e3ad0, [C8 (Z_to_bv 64 0x5e82e0); C8 (Z_to_bv 64 0x6a17a0)])              (* [comment removed for export] *)
  ; (0x5e3b18, [C8 (Z_to_bv 64 0x56c1c8); C8 (Z_to_bv 64 0x56c1b0)])              (* [comment removed for export] *)
  ; (0x5e4b80, [C8 (Z_to_bv 64 0x5e4b80)])                                        (* [comment removed for export] *)
  ; (0x5e4c18, [C8 (Z_to_bv 64 0x562ccc); C8 (Z_to_bv 64 0x55fb70); C8 (Z_to_bv 64 0x562cec)])  (* [comment removed for export] *)
  ; (0x6a2690, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x7369fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x736d20, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=   (* [comment removed for export] *)
  [ (0x121f9, 10)   (* [comment removed for export] *)
  ; (0x1d956, 4)    (* [comment removed for export] *)
  ; (0x21175, 17)   (* [comment removed for export] *)
  ; (0x21180, 128)  (* [comment removed for export] *)
  ; (0x2efe0, 33)   (* [comment removed for export] *)
  ; (0x3d286, 21)   (* [comment removed for export] *)
  ; (0x3d29b, 23)   (* [comment removed for export] *)
  ; (0x44680, 128)  (* [comment removed for export] *)
  ; (0x48e5c, 7)    (* [comment removed for export] *)
  ; (0x113cd0, 16)   (* [comment removed for export] *)
  ; (0xbc74c0, 16)  (* [comment removed for export] *) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells ctbsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells ctbsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc ctbsegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5e4be0, 0x5e4bf8); (0x6a2730, 0x6a2738);
    (0x56c1b0, 0x56c1c8); (0x5e1a28, 0x5e1a30); (0x5e1b08, 0x5e1b18); (0x5e27b8, 0x5e27c8); (0x5e3ad0, 0x5e3ae0); (0x5e3b18, 0x5e3b28);
    (0x5e4b80, 0x5e4b88); (0x5e4c18, 0x5e4c30); (0x6a2690, 0x6a2694); (0x7369fc, 0x7369fd); (0x736d20, 0x736d21) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells ctbsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells ctbsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc ctbsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
