(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5ab600, [C8 (Z_to_bv 64 0x5317e0); C8 (Z_to_bv 64 0x525b1c); C8 (Z_to_bv 64 0x525f7c)])  (* [comment removed for export] *)
  ; (0x66e3f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x532838, [C8 (Z_to_bv 64 0x1f3428); C8 (Z_to_bv 64 0x199b38); C8 (Z_to_bv 64 0x20b954)])  (* [comment removed for export] *)
  ; (0x5a8488, [C8 (Z_to_bv 64 0x5ae748)])                                        (* [comment removed for export] *)
  ; (0x5a8568, [C8 (Z_to_bv 64 0x51ef1c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5a9218, [C8 (Z_to_bv 64 0x5a8488); C8 (Z_to_bv 64 0x1f3098)])              (* [comment removed for export] *)
  ; (0x5aa4e8, [C8 (Z_to_bv 64 0x5aea40); C8 (Z_to_bv 64 0x66d480)])              (* [comment removed for export] *)
  ; (0x5aa530, [C8 (Z_to_bv 64 0x532850); C8 (Z_to_bv 64 0x532838)])              (* [comment removed for export] *)
  ; (0x5ab5a0, [C8 (Z_to_bv 64 0x5ab5a0)])                                        (* [comment removed for export] *)
  ; (0x5ab638, [C8 (Z_to_bv 64 0x529354); C8 (Z_to_bv 64 0x5261f8); C8 (Z_to_bv 64 0x529374)])  (* [comment removed for export] *)
  ; (0x66e350, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x7026bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x7029e0, [C1 (Z_to_bv 8 0)])                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x5ab5c0, [C8 (Z_to_bv 64 0x52a9e4)])        (* [comment removed for export] *)
  ; (0x702765, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x5a9ba0, [C8 (Z_to_bv 64 0x1f3458)])        (* [comment removed for export] *)
  ; (0x5a9bb8, [C8 (Z_to_bv 64 0x1f396c)])        (* [comment removed for export] *)
  ; (0x5a9c70, [C8 (Z_to_bv 64 0x407fc4)])        (* [comment removed for export] *)
  ; (0x5a9bd8, [C8 (Z_to_bv 64 0x26e830)])        (* [comment removed for export] *)
  ; (0x5a9be0, [C8 (Z_to_bv 64 0x26ea98)])        (* [comment removed for export] *) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121eb, 10)     (* [comment removed for export] *)
  ; (0x1daeb, 4)      (* [comment removed for export] *)
  ; (0x212c0, 128)    (* [comment removed for export] *)
  ; (0x2ef82, 33)     (* [comment removed for export] *)
  ; (0x3ccae, 21)     (* [comment removed for export] *)
  ; (0x3ccc3, 23)     (* [comment removed for export] *)
  ; (0x44080, 128)    (* [comment removed for export] *)
  ; (0x48927, 7)      (* [comment removed for export] *)
  ; (0x11a290, 16)     (* [comment removed for export] *)
  ; (0xb93180, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5ab600, 0x5ab618); (0x66e3f0, 0x66e3f8);
    (0x532838, 0x532850); (0x5a8488, 0x5a8490); (0x5a8568, 0x5a8578); (0x5a9218, 0x5a9228); (0x5aa4e8, 0x5aa4f8); (0x5aa530, 0x5aa540);
    (0x5ab5a0, 0x5ab5a8); (0x5ab638, 0x5ab650); (0x66e350, 0x66e354); (0x7026bc, 0x7026bd); (0x7029e0, 0x7029e1);
    (0x5ab5c0, 0x5ab5c8); (0x702765, 0x702766); (0x5a9ba0, 0x5a9ba8); (0x5a9bb8, 0x5a9bc0); (0x5a9c70, 0x5a9c78); (0x5a9bd8, 0x5a9be0); (0x5a9be0, 0x5a9be8) ].

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
