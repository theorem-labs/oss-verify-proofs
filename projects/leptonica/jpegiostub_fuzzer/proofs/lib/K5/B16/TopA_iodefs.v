(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcaea0, [C8 (Z_to_bv 64 0xc4b48); C8 (Z_to_bv 64 0xbba4c)])              (* [comment removed for export] *)
  ; (0xcffb0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xc5cc8, [C8 (Z_to_bv 64 0x8c9a8); C8 (Z_to_bv 64 0x3b030)])              (* [comment removed for export] *)
  ; (0xc9000, [C8 (Z_to_bv 64 0xcd7e8)])                                        (* [comment removed for export] *)
  ; (0xc90d8, [C8 (Z_to_bv 64 0xb5894); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc9d68, [C8 (Z_to_bv 64 0xc9000); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xc9d88, [C8 (Z_to_bv 64 0xcdae0); C8 (Z_to_bv 64 0xcf020)])              (* [comment removed for export] *)
  ; (0xc9e10, [C8 (Z_to_bv 64 0xc5cd8); C8 (Z_to_bv 64 0xc5cc8)])              (* [comment removed for export] *)
  ; (0xcae60, [C8 (Z_to_bv 64 0xcae60)])                                        (* [comment removed for export] *)
  ; (0xcaec8, [C8 (Z_to_bv 64 0xbed90); C8 (Z_to_bv 64 0xbbc80); C8 (Z_to_bv 64 0xbedac)])  (* [comment removed for export] *)
  ; (0xcff10, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x16427c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1645a0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10cbe, 10)     (* [comment removed for export] *)
  ; (0x14d2d, 4)      (* [comment removed for export] *)
  ; (0x16000, 192)    (* [comment removed for export] *)
  ; (0x1a6f1, 33)     (* [comment removed for export] *)
  ; (0x1ed4d, 21)     (* [comment removed for export] *)
  ; (0x1ed62, 23)     (* [comment removed for export] *)
  ; (0x21300, 128)    (* [comment removed for export] *)
  ; (0x2231d, 7)      (* [comment removed for export] *)
  ; (0x26f38, 16)     (* [comment removed for export] *)
  ; (0x5f4d40, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcaea0, 0xcaeb0); (0xcffb0, 0xcffb8);
    (0xc5cc8, 0xc5cd8); (0xc9000, 0xc9008); (0xc90d8, 0xc90e8); (0xc9d68, 0xc9d78); (0xc9d88, 0xc9d98); (0xc9e10, 0xc9e20);
    (0xcae60, 0xcae68); (0xcaec8, 0xcaee0); (0xcff10, 0xcff14); (0x16427c, 0x16427d); (0x1645a0, 0x1645a1) ].

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
