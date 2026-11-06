(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase ARep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
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

#[using="Type"] Lemma u8arr_transportD : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u32arr_transportD : forall W m m' A ws,
  u32arr segs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u64arr_transportD : forall W m m' A ws,
  u64arr segs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_transportD : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU D. split; [exact H0|]. split; [exact H1|].
  intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. Local Ltac2 Set LiaHints.tbl := fun () => "0020>14255785789.1456765667309.1400000400>S2HaS2H02H12Ha".
rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  destruct (H a Ha) as [WV [b RD]]. split.
  - rewrite (wview_agree m m' _ E). exact WV.
  - exists b. unfold mrd in *. rewrite E. exact RD.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma munch_agree_range : forall W m m' A n i,
  munch W m m' -> disjoint_from W A n -> 0 <= A -> A + n <= 2^64 -> 0 <= i < n ->
  m' (wa (A + i)) = m (wa (A + i)).
Proof.
  intros W m m' A n i MU D H0 H1 Hi. apply MU. Local Ltac2 Set LiaHints.tbl := fun () => "0020>33628179521.1351696475855.1300000:00>S2H02H12HiS2Hi".
rewrite wa_unsigned by lia.
  eapply disjoint_outside; [exact D | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

#[using="Type"] Lemma u64arr_frameD : forall W m m' A ws, u64arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_transportD; eauto. Qed.
#[using="Type"] Lemma u32arr_frameD : forall W m m' A ws, u32arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_transportD; eauto. Qed.

#[using="Type"] Lemma azero_frameD : forall W m m' A n, azero m A n -> munch W m m' ->
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
#[using="Type"] Lemma ro_cells_frameD : forall W m m' A cs, ro_cells asegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
Proof. intros. eapply ro_cells_transport; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wmono_but (W : list ivl) (m m' : amem) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

#[using="Type"] Lemma munch_wmono_but : forall W m m', munch W m m' -> wmono_but W m m'.
Proof. intros W m m' MU x Hx. rewrite (wview_agree asegs m m' x (MU x Hx)). exact (fun H => H). Qed.
#[using="Type"] Lemma wmono_wmono_but : forall W m m', wmono asegs m m' -> wmono_but W m m'.
Proof. intros W m m' WM x _. apply WM. Qed.
#[using="Type"] Lemma wmono_but_refl : forall W m, wmono_but W m m.
Proof. intros W m x _ H; exact H. Qed.
#[using="Type"] Lemma wmono_but_trans : forall W m1 m2 m3, wmono_but W m1 m2 -> wmono_but W m2 m3 -> wmono_but W m1 m3.
Proof. intros W m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; assumption. Qed.
#[using="Type"] Lemma wmono_but_weaken : forall W W' m m', sub_fp W W' -> wmono_but W m m' -> wmono_but W' m m'.
Proof. intros W W' m m' S H x Hx. apply H. apply S. exact Hx. Qed.
#[using="Type"] Lemma wmono_but_write : forall W m0 m a bs, wmono_but W m0 m -> wmono_but W m0 (write_to_mem m a bs).
Proof. intros W m0 m a bs H x Hx Hw. apply wview_write_mono. apply H; assumption. Qed.
End CANSEC1.
