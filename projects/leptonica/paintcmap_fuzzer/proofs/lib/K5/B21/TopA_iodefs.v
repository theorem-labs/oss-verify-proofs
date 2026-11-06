(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xcfa80, [C8 (Z_to_bv 64 0xc9720); C8 (Z_to_bv 64 0xc0624)])              (* [comment removed for export] *)
  ; (0xd55b0, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xca8a0, [C8 (Z_to_bv 64 0x8dc10); C8 (Z_to_bv 64 0x3bfe4)])              (* [comment removed for export] *)
  ; (0xcdbd8, [C8 (Z_to_bv 64 0xd23c8)])                                        (* [comment removed for export] *)
  ; (0xcdcb0, [C8 (Z_to_bv 64 0xba46c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xce940, [C8 (Z_to_bv 64 0xcdbd8); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xce960, [C8 (Z_to_bv 64 0xd26c0); C8 (Z_to_bv 64 0xd4640)])              (* [comment removed for export] *)
  ; (0xce9e8, [C8 (Z_to_bv 64 0xca8b0); C8 (Z_to_bv 64 0xca8a0)])              (* [comment removed for export] *)
  ; (0xcfa40, [C8 (Z_to_bv 64 0xcfa40)])                                        (* [comment removed for export] *)
  ; (0xcfaa8, [C8 (Z_to_bv 64 0xc3968); C8 (Z_to_bv 64 0xc0858); C8 (Z_to_bv 64 0xc3984)])  (* [comment removed for export] *)
  ; (0xd5510, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x16987c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x169ba0, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

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
  ; (0x5fa340, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xcfa80, 0xcfa90); (0xd55b0, 0xd55b8);
    (0xca8a0, 0xca8b0); (0xcdbd8, 0xcdbe0); (0xcdcb0, 0xcdcc0); (0xce940, 0xce950); (0xce960, 0xce970); (0xce9e8, 0xce9f8);
    (0xcfa40, 0xcfa48); (0xcfaa8, 0xcfac0); (0xd5510, 0xd5514); (0x16987c, 0x16987d); (0x169ba0, 0x169ba1) ].

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
