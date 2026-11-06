(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xe5340, [C8 (Z_to_bv 64 0xdefec); C8 (Z_to_bv 64 0xd39d4)])              (* [comment removed for export] *)
  ; (0xeca70, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x180de5, [C1 (Z_to_bv 8 1)])    (* [comment removed for export] *)
  ; (0xe5318, [C8 (Z_to_bv 64 0xd9de4)])    (* [comment removed for export] *)
  ; (0xe0170, [C8 (Z_to_bv 64 0x90bf0); C8 (Z_to_bv 64 0x3f078)])              (* [comment removed for export] *)
  ; (0xe34a8, [C8 (Z_to_bv 64 0xe7c88)])                                        (* [comment removed for export] *)
  ; (0xe3580, [C8 (Z_to_bv 64 0xcd578); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe4210, [C8 (Z_to_bv 64 0xe34a8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xe4230, [C8 (Z_to_bv 64 0xe7f80); C8 (Z_to_bv 64 0xebb00)])              (* [comment removed for export] *)
  ; (0xe42b8, [C8 (Z_to_bv 64 0xe0180); C8 (Z_to_bv 64 0xe0170)])              (* [comment removed for export] *)
  ; (0xe5300, [C8 (Z_to_bv 64 0xe5300)])                                        (* [comment removed for export] *)
  ; (0xe5368, [C8 (Z_to_bv 64 0xd9188); C8 (Z_to_bv 64 0xd3c08); C8 (Z_to_bv 64 0xd91a4)])  (* [comment removed for export] *)
  ; (0xec9d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x180d3c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x181060, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d64, 10)     (* [comment removed for export] *)
  ; (0x14f29, 4)      (* [comment removed for export] *)
  ; (0x16300, 192)    (* [comment removed for export] *)
  ; (0x1ac95, 33)     (* [comment removed for export] *)
  ; (0x1f62f, 21)     (* [comment removed for export] *)
  ; (0x1f644, 23)     (* [comment removed for export] *)
  ; (0x21dc0, 128)    (* [comment removed for export] *)
  ; (0x22e3e, 7)      (* [comment removed for export] *)
  ; (0x239b8, 16)     (* [comment removed for export] *)
  ; (0x611800, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xe5340, 0xe5350); (0xeca70, 0xeca78);
    (0x180de5, 0x180de6); (0xe5318, 0xe5320); (0xe0170, 0xe0180); (0xe34a8, 0xe34b0); (0xe3580, 0xe3590); (0xe4210, 0xe4220); (0xe4230, 0xe4240); (0xe42b8, 0xe42c8);
    (0xe5300, 0xe5308); (0xe5368, 0xe5380); (0xec9d0, 0xec9d4); (0x180d3c, 0x180d3d); (0x181060, 0x181061) ].

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
