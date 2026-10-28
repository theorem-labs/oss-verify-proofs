(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ARep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section WithSegs.
Variable segs : list Segment.

Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
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

Lemma u8arr_transportD : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transportD; eauto.
Qed.

Lemma u32arr_transportD : forall W m m' A ws,
  u32arr segs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

Lemma u64arr_transportD : forall W m m' A ws,
  u64arr segs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

(* [comment removed for export] *)
Lemma stk_transportD : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU D. split; [exact H0|]. split; [exact H1|].
  intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  destruct (H a Ha) as [WV [b RD]]. split.
  - rewrite (wview_agree m m' _ E). exact WV.
  - exists b. unfold mrd in *. rewrite E. exact RD.
Qed.

(* [comment removed for export] *)
Lemma munch_agree_range : forall W m m' A n i,
  munch W m m' -> disjoint_from W A n -> 0 <= A -> A + n <= 2^64 -> 0 <= i < n ->
  m' (wa (A + i)) = m (wa (A + i)).
Proof.
  intros W m m' A n i MU D H0 H1 Hi. apply MU. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [exact D | lia].
Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Lemma u64arr_frameD : forall W m m' A ws, u64arr bsegs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof. intros. eapply u64arr_transportD; eauto. Qed.
Lemma u32arr_frameD : forall W m m' A ws, u32arr bsegs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr bsegs m' A ws.
Proof. intros. eapply u32arr_transportD; eauto. Qed.

Lemma azero_frameD : forall W m m' A n, azero m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros W m m' A n [Z0 WR] MU D. pose proof WR as (W0 & W1 & _).
  assert (E : forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))).
  { intros i Hi. eapply munch_agree_range; [exact MU | apply D; lia | lia | lia | lia]. }
  split.
  - intros i Hi. rewrite (E i Hi). apply Z0. exact Hi.
  - eapply wr_at_agree; [exact WR | exact E].
Qed.

(* [comment removed for export] *)
Lemma ro_cells_frameD : forall W m m' A cs, ro_cells bsegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells bsegs m' A cs.
Proof. intros. eapply ro_cells_transport; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wmono_but (W : list ivl) (m m' : amem) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> wview bsegs m x <> None -> wview bsegs m' x <> None.

Lemma munch_wmono_but : forall W m m', munch W m m' -> wmono_but W m m'.
Proof. intros W m m' MU x Hx. rewrite (wview_agree bsegs m m' x (MU x Hx)). exact (fun H => H). Qed.
Lemma wmono_wmono_but : forall W m m', wmono bsegs m m' -> wmono_but W m m'.
Proof. intros W m m' WM x _. apply WM. Qed.
Lemma wmono_but_refl : forall W m, wmono_but W m m.
Proof. intros W m x _ H; exact H. Qed.
Lemma wmono_but_trans : forall W m1 m2 m3, wmono_but W m1 m2 -> wmono_but W m2 m3 -> wmono_but W m1 m3.
Proof. intros W m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; assumption. Qed.
Lemma wmono_but_weaken : forall W W' m m', sub_fp W W' -> wmono_but W m m' -> wmono_but W' m m'.
Proof. intros W W' m m' S H x Hx. apply H. apply S. exact Hx. Qed.
Lemma wmono_but_write : forall W m0 m a bs, wmono_but W m0 m -> wmono_but W m0 (write_to_mem m a bs).
Proof. intros W m0 m a bs H x Hx Hw. apply wview_write_mono. apply H; assumption. Qed.
End CANSEC1.
