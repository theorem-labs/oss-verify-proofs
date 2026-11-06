(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcbde0, [C8 (Z_to_bv 64 0xc5a98); C8 (Z_to_bv 64 0xbc99c)])              (* [comment removed for export] *)
  ; (0xd1270, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc6c18, [C8 (Z_to_bv 64 0x8cfac); C8 (Z_to_bv 64 0x3b5d0)])              (* [comment removed for export] *)
  ; (0xc9f50, [C8 (Z_to_bv 64 0xce728)])                                        (* [comment removed for export] *)
  ; (0xca028, [C8 (Z_to_bv 64 0xb67e4); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcacb8, [C8 (Z_to_bv 64 0xc9f50); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xcacd8, [C8 (Z_to_bv 64 0xcea20); C8 (Z_to_bv 64 0xd02e0)])              (* [comment removed for export] *)
  ; (0xcad60, [C8 (Z_to_bv 64 0xc6c28); C8 (Z_to_bv 64 0xc6c18)])              (* [comment removed for export] *)
  ; (0xcbda0, [C8 (Z_to_bv 64 0xcbda0)])                                        (* [comment removed for export] *)
  ; (0xcbe08, [C8 (Z_to_bv 64 0xbfce0); C8 (Z_to_bv 64 0xbcbd0); C8 (Z_to_bv 64 0xbfcfc)])  (* [comment removed for export] *)
  ; (0xd11d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x16553c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x165860, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10ca5, 10)     (* [comment removed for export] *)
  ; (0x14d06, 4)      (* [comment removed for export] *)
  ; (0x16000, 128)    (* [comment removed for export] *)
  ; (0x1a71c, 33)     (* [comment removed for export] *)
  ; (0x1edc9, 21)     (* [comment removed for export] *)
  ; (0x1edde, 23)     (* [comment removed for export] *)
  ; (0x213c0, 128)    (* [comment removed for export] *)
  ; (0x223dc, 7)      (* [comment removed for export] *)
  ; (0x27438, 16)     (* [comment removed for export] *)
  ; (0x5f6000, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcbde0, 0xcbdf0); (0xd1270, 0xd1278);
    (0xc6c18, 0xc6c28); (0xc9f50, 0xc9f58); (0xca028, 0xca038); (0xcacb8, 0xcacc8); (0xcacd8, 0xcace8); (0xcad60, 0xcad70);
    (0xcbda0, 0xcbda8); (0xcbe08, 0xcbe20); (0xd11d0, 0xd11d4); (0x16553c, 0x16553d); (0x165860, 0x165861) ].

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
