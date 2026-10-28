(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma fl_ok_byte1 : forall fl, fl_ok fl -> Z.land (bv_unsigned (Z_to_bv 8 (fl ≫ 8))) 2 = 0.
Proof.
  intros fl [R H].
  assert (E : bv_unsigned (Z_to_bv 8 (fl ≫ 8)) = Z.land (fl ≫ 8) 255).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite <- Z.land_ones by lia. reflexivity. }
  rewrite E. rewrite <- Z.land_assoc. change (Z.land 255 2) with 2. change 2 with (512 ≫ 8) at 1. rewrite <- Z.shiftr_land, H. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bio_w1_bytes (fl : Z) (rrw numw padw ptrw : word) : list cell :=
  [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C1 (Z_to_bv 8 fl); C1 (Z_to_bv 8 (fl ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8 ≫ 8));
   C4 rrw; C4 numw; C4 padw; C8 ptrw].

Lemma bio_w1_bytes_view : forall segs m A fl rrw numw padw ptrw, 0 <= fl < 2 ^ 31 ->
  rw_cells segs m A (bio_w1_cells (Z_to_bv 64 4294967297) fl rrw numw padw ptrw) <-> rw_cells segs m A (bio_w1_bytes fl rrw numw padw ptrw).
Proof.
  intros segs m A fl rrw numw padw ptrw R.
  assert (EB : cells_bytes (bio_w1_cells (Z_to_bv 64 4294967297) fl rrw numw padw ptrw) = cells_bytes (bio_w1_bytes fl rrw numw padw ptrw)).
  { unfold bio_w1_cells, bio_w1_bytes. cbn [cells_bytes cbytes app]. unfold le4. rewrite <- !store_bytes_8'. rewrite ?unsigned_lit by lia. cbn [Z_to_le_bytes app].
    repeat (apply (f_equal2 cons); [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|]); reflexivity. }
  split; intros H.
  - apply (th_cells_congr segs m A _ _ EB); [reflexivity| unfold bio_w1_bytes; cbn; tauto| exact H].
  - apply (th_cells_congr segs m A _ _ (eq_sym EB)); [reflexivity| unfold bio_w1_cells; cbn; tauto| exact H].
Qed.
