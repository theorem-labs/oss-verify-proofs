(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CELLS. Context {rc : runConstT}.
Fixpoint e42_c8s_of (k : nat) (bs : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 bs)) :: e42_c8s_of k' (skipn 8 bs) end.

Lemma e42_c8s_of_props : forall k bs, length bs = (8 * k)%nat ->
  cells_wf (e42_c8s_of k bs) /\ cells_bytes (e42_c8s_of k bs) = bs /\ cells_size (e42_c8s_of k bs) = (8 * k)%nat.
Proof.
  induction k as [|k IH]; intros bs HL.
  - destruct bs; [|discriminate]. cbn. repeat split; try constructor.
  - cbn [e42_c8s_of]. assert (L2 : length (skipn 8 bs) = (8 * k)%nat) by (rewrite skipn_length; lia).
    destruct (IH _ L2) as (W & B & S'). split; [|split].
    + split; [exact I | exact W].
    + cbn [cells_bytes cbytes]. rewrite B, le8_of_bytes by (rewrite firstn_length; lia). apply firstn_skipn.
    + cbn [cells_size csize]. rewrite S'. lia.
Qed.

Lemma e42_cb_as_c8s : forall m A (k : nat) bs, rw_cells bsegs m A [CB (8 * k) bs] -> rw_cells bsegs m A (e42_c8s_of k bs).
Proof.
  intros m A k bs H. assert (HL : length bs = (8 * k)%nat).
  { destruct H as [[W _] _]. exact (proj1 W). }
  destruct (e42_c8s_of_props k bs HL) as (W & B & S').
  apply (rw_cells_recast bsegs m A _ _ H W).
  - rewrite B. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite S'. cbn [cells_size csize]. lia.
Qed.

Lemma e42_cb144_as_c8s : forall m A bs, rw_cells bsegs m A [CB 144 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : word,
    rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                        C8 w14; C8 w15; C8 w16; C8 w17].
Proof.
  intros m A bs H. pose proof (e42_cb_as_c8s m A 18 bs H) as H2. cbn [e42_c8s_of] in H2.
  do 18 eexists. exact H2.
Qed.

Lemma e42_cb128_as_c8s : forall m A bs, rw_cells bsegs m A [CB 128 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word,
    rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15].
Proof.
  intros m A bs H. pose proof (e42_cb_as_c8s m A 16 bs H) as H2. cbn [e42_c8s_of] in H2.
  do 16 eexists. exact H2.
Qed.

Lemma e42_cb32_as_c8s : forall m A bs, rw_cells bsegs m A [CB 32 bs] ->
  exists w0 w1 w2 w3 : word, rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
  intros m A bs H. pose proof (e42_cb_as_c8s m A 4 bs H) as H2. cbn [e42_c8s_of] in H2.
  do 4 eexists. exact H2.
Qed.
End CELLS.
