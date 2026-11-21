(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg ABase ARep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section WithSegs.
Variable segs : list Segment.

Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma wr_at_agree : forall m m' A n,
  wr_at segs m A n -> (forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))) -> wr_at segs m' A n.
Proof.
  intros m m' A n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree m m' _ (E i Hi)). apply H. exact Hi.
Qed.

Lemma wr_at_transportD : forall W m m' A n,
  wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros W m m' A n WR MU D. pose proof WR as (H0 & H1 & _).
  eapply wr_at_agree; [exact WR|]. intros i Hi. apply MU.
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma rw_cells_transportD : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
  - eapply wr_at_transportD; eauto.
Qed.





End WithSegs.

Lemma junk_frameD : forall W m m' A n, junk_at m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma fill_frameD : forall W m m' A n v, fill_at m A n v -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cells_frameD : forall W m m' A cs, rw_cells bsegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof. intros. eapply rw_cells_transportD; eauto. Qed.




End CANSEC1.
