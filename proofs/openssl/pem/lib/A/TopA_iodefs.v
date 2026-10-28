(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x5a7620, [C8 (Z_to_bv 64 0x52d808); C8 (Z_to_bv 64 0x521b44); C8 (Z_to_bv 64 0x521fa4)])  (* [comment removed for export] *)
  ; (0x66a3f0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x52e860, [C8 (Z_to_bv 64 0x1f34cc); C8 (Z_to_bv 64 0x199adc); C8 (Z_to_bv 64 0x1f34fc)])  (* [comment removed for export] *)
  ; (0x5a44a8, [C8 (Z_to_bv 64 0x5aa768)])                                        (* [comment removed for export] *)
  ; (0x5a4588, [C8 (Z_to_bv 64 0x51af44); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x5a5238, [C8 (Z_to_bv 64 0x5a44a8); C8 (Z_to_bv 64 0x1f303c)])              (* [comment removed for export] *)
  ; (0x5a6500, [C8 (Z_to_bv 64 0x5aaa60); C8 (Z_to_bv 64 0x669460)])              (* [comment removed for export] *)
  ; (0x5a6548, [C8 (Z_to_bv 64 0x52e878); C8 (Z_to_bv 64 0x52e860)])              (* [comment removed for export] *)
  ; (0x5a75c0, [C8 (Z_to_bv 64 0x5a75c0)])                                        (* [comment removed for export] *)
  ; (0x5a7658, [C8 (Z_to_bv 64 0x52537c); C8 (Z_to_bv 64 0x522220); C8 (Z_to_bv 64 0x52539c)])  (* [comment removed for export] *)
  ; (0x66a350, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x6fe6bc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x6fe9e0, [C1 (Z_to_bv 8 0)])                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x5a75e0, [C8 (Z_to_bv 64 0x526a0c)])        (* [comment removed for export] *)
  ; (0x6fe765, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x5a5bc0, [C8 (Z_to_bv 64 0x1fbf20)])        (* [comment removed for export] *)
  ; (0x5a5bd8, [C8 (Z_to_bv 64 0x1fc430)])        (* [comment removed for export] *)
  ; (0x5a5e10, [C8 (Z_to_bv 64 0x30c090)])        (* [comment removed for export] *)
  ; (0x5a5bf8, [C8 (Z_to_bv 64 0x261140)])        (* [comment removed for export] *)
  ; (0x5a5c00, [C8 (Z_to_bv 64 0x2613a8)])        (* [comment removed for export] *)
  ; (0x6fe766, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *)
  ; (0x6fe767, [C1 (Z_to_bv 8 1)])        (* [comment removed for export] *) ].

Definition io_acc : list (Z * Z) :=
  [ (0x121eb, 10)     (* [comment removed for export] *)
  ; (0x1dae0, 4)      (* [comment removed for export] *)
  ; (0x21280, 128)    (* [comment removed for export] *)
  ; (0x2ef43, 33)     (* [comment removed for export] *)
  ; (0x3cc6f, 21)     (* [comment removed for export] *)
  ; (0x3cc84, 23)     (* [comment removed for export] *)
  ; (0x44040, 128)    (* [comment removed for export] *)
  ; (0x488e8, 7)      (* [comment removed for export] *)
  ; (0x11a1d0, 16)     (* [comment removed for export] *)
  ; (0xb8f180, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x5a7620, 0x5a7638); (0x66a3f0, 0x66a3f8);
    (0x52e860, 0x52e878); (0x5a44a8, 0x5a44b0); (0x5a4588, 0x5a4598); (0x5a5238, 0x5a5248); (0x5a6500, 0x5a6510); (0x5a6548, 0x5a6558);
    (0x5a75c0, 0x5a75c8); (0x5a7658, 0x5a7670); (0x66a350, 0x66a354); (0x6fe6bc, 0x6fe6bd); (0x6fe9e0, 0x6fe9e1);
    (0x5a75e0, 0x5a75e8); (0x6fe765, 0x6fe766); (0x5a5bc0, 0x5a5bc8); (0x5a5bd8, 0x5a5be0); (0x5a5e10, 0x5a5e18); (0x5a5bf8, 0x5a5c00); (0x5a5c00, 0x5a5c08);
    (0x6fe766, 0x6fe767); (0x6fe767, 0x6fe768) ].

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
