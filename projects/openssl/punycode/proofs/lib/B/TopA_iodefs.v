(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
  [ (0x5e3fc0, [C8 (Z_to_bv 64 0x56a62c); C8 (Z_to_bv 64 0x55e968); C8 (Z_to_bv 64 0x55edc8)])  (* [comment removed for export] *)
  ; (0x6a1330, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x56b680, [C8 (Z_to_bv 64 0x1eea6c); C8 (Z_to_bv 64 0x194a48); C8 (Z_to_bv 64 0x2080b8)])  (* [comment removed for export] *)
  ; (0x5e0e48, [C8 (Z_to_bv 64 0x5e73c8)])                                        (* [comment removed for export] *)
  ; (0x5e0f28, [C8 (Z_to_bv 64 0x557d68); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5e1bd8, [C8 (Z_to_bv 64 0x5e0e48); C8 (Z_to_bv 64 0x1edfa8)])              (* [comment removed for export] *)
  ; (0x5e2eb0, [C8 (Z_to_bv 64 0x5e76c0); C8 (Z_to_bv 64 0x6a03c0)])              (* [comment removed for export] *)
  ; (0x5e2ef8, [C8 (Z_to_bv 64 0x56b698); C8 (Z_to_bv 64 0x56b680)])              (* [comment removed for export] *)
  ; (0x5e3f60, [C8 (Z_to_bv 64 0x5e3f60)])                                        (* [comment removed for export] *)
  ; (0x5e3ff8, [C8 (Z_to_bv 64 0x5621a0); C8 (Z_to_bv 64 0x55f044); C8 (Z_to_bv 64 0x5621c0)])  (* [comment removed for export] *)
  ; (0x6a1290, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x7355fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x735920, [C1 (Z_to_bv 8 0)])                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x5e3f80, [C8 (Z_to_bv 64 0x563830)])        (* [comment removed for export] *)
  ; (0x7356a5, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x5e2558, [C8 (Z_to_bv 64 0x1ee344)])        (* [comment removed for export] *)
  ; (0x5e2570, [C8 (Z_to_bv 64 0x1ee868)])        (* [comment removed for export] *)
  ; (0x5e2630, [C8 (Z_to_bv 64 0x4312f4)])        (* [comment removed for export] *)
  ; (0x5e2590, [C8 (Z_to_bv 64 0x273608)])        (* [comment removed for export] *)
  ; (0x5e2598, [C8 (Z_to_bv 64 0x273870)])        (* [comment removed for export] *) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121e9, 10)     (* [comment removed for export] *)
  ; (0x1d938, 4)      (* [comment removed for export] *)
  ; (0x21140, 128)    (* [comment removed for export] *)
  ; (0x2efa9, 33)     (* [comment removed for export] *)
  ; (0x3d22e, 21)     (* [comment removed for export] *)
  ; (0x3d243, 23)     (* [comment removed for export] *)
  ; (0x44600, 128)    (* [comment removed for export] *)
  ; (0x48d9d, 7)      (* [comment removed for export] *)
  ; (0x113528, 16)     (* [comment removed for export] *)
  ; (0xbc60c0, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5e3fc0, 0x5e3fd8); (0x6a1330, 0x6a1338);
    (0x56b680, 0x56b698); (0x5e0e48, 0x5e0e50); (0x5e0f28, 0x5e0f38); (0x5e1bd8, 0x5e1be8); (0x5e2eb0, 0x5e2ec0); (0x5e2ef8, 0x5e2f08);
    (0x5e3f60, 0x5e3f68); (0x5e3ff8, 0x5e4010); (0x6a1290, 0x6a1294); (0x7355fc, 0x7355fd); (0x735920, 0x735921);
    (0x5e3f80, 0x5e3f88); (0x7356a5, 0x7356a6); (0x5e2558, 0x5e2560); (0x5e2570, 0x5e2578); (0x5e2630, 0x5e2638); (0x5e2590, 0x5e2598); (0x5e2598, 0x5e25a0) ].

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
