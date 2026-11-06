(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ARep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.
#[using="Type"] Lemma wr_at_agree : forall m m' A n,
wr_at segs m A n -> (forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))) -> wr_at segs m' A n.
Proof.
intros m m' A n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (wview_agree m m' _ (E i Hi)). apply H. exact Hi.
Qed.
#[using="Type"] Lemma wr_at_transportD : forall W m m' A n,
wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
intros W m m' A n WR MU D. pose proof WR as (H0 & H1 & _).
eapply wr_at_agree; [exact WR|]. intros i Hi. apply MU.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>33628179521.1451696475855.1400000:00>S2H02H12HiS2Hi".
rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_transportD : forall W m m' A cs,
rw_cells segs m A cs -> munch W m m' ->
disjoint_from W A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof.
intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
- eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
- eapply wr_at_transportD; eauto.
Qed.
End WithSegs.
#[using="Type"] Lemma junk_frameD : forall W m m' A n, junk_at m A n -> munch W m m' ->
(0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
intros W m m' A n [bs H] MU D. exists bs.
pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
destruct (Z.lt_ge_cases 0 n).
- eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
Local Ltac2 Set LiaHints.tbl := fun () => "0080>1312051727.17 14229248646.1920742173918.192424953696.18 24931798969.1740669651581.1759647939808.1768686216788.1900000600?00H00Q00Z00c00l018S1L2W1S1L2W12H0S1L2W12HiS1L2W12H0S1L2B02W1S1L2W12H0S1L2W12H0S1L2W12H02Hi".
rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
- assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
+ split; [lia|]. split; [lia|]. intros i Hi. lia.
+ split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fill_frameD : forall W m m' A n v, fill_at m A n v -> munch W m m' ->
(0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
intros W m m' A n v H MU D. unfold fill_at in *.
destruct (Z.lt_ge_cases 0 n).
- eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>20742173918.2023121635500.182424953696.11 24931663515.1825166272120.1840669959007.1868686216788.2000000700;00?00F00O00S00ZS2W12HiS2W1S2H0S2B02W1S2H01L2W1S2W1S2W12Hi".
rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
- pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
+ split; [lia|]. split; [lia|]. intros i Hi. lia.
+ split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cells_frameD : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' ->
disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_transportD; eauto. Qed.
End CANSEC1.
