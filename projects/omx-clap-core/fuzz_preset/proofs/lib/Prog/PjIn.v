From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition pj_in_ok (m : word -> option byte) (q text len p d : Z) (txt : list byte) : Prop :=
  bytes_at segs m q (le8 (Z_to_bv 64 p)) /\
  bytes_at segs m (q + 8) (le8 (Z_to_bv 64 (text + len))) /\
  bytes_at segs m (q + 16) (le4 (Z_to_bv 64 d)) /\
  wr_at segs m q 24 /\
  q mod 8 = 0 /\
  0 < text /\ text + len < 2 ^ 62 /\
  text <= p <= text + len /\
  Z.of_nat (length txt) = len /\ bytes_at segs m text txt /\
  disjoint_from [(text, text + len)] q 24 /\
  0 <= d <= 32.

Lemma disjoint_from_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia|]. exact (IH a n a' n' H4 H1 H2).
Qed.

Lemma pj_in_ok_bounds : forall m q text len p d txt, pj_in_ok m q text len p d txt ->
  0 <= q /\ q + 24 <= 2 ^ 64 /\ 0 < text /\ text <= p <= text + len /\ text + len < 2 ^ 62 /\
  (q + 24 <= text \/ text + len <= q) /\ Z.of_nat (length txt) = len /\ q mod 8 = 0 /\ 0 <= d <= 32.
Proof.
  intros m q text len p d txt (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  destruct H4 as (W1 & W2 & _). cbn in H11. lia.
Qed.

Lemma pj_in_ok_rd_p : forall m q text len p d txt, pj_in_ok m q text len p d txt ->
  ov_read_bytes segs m (wa q) 8 = Some (le8 (Z_to_bv 64 p)).
Proof.
  intros m q text len p d txt (H1 & _).
  rewrite <- (Z.add_0_r q) at 1. rewrite (bytes_at_read segs m q _ 0 8 H1) by (rewrite ?length_le8; cbn; lia).
  rewrite firstn_all2 by (rewrite ?length_skipn, ?length_le8; lia). reflexivity.
Qed.

Lemma pj_in_ok_rd_end : forall m q text len p d txt, pj_in_ok m q text len p d txt ->
  ov_read_bytes segs m (wa (q + 8)) 8 = Some (le8 (Z_to_bv 64 (text + len))).
Proof.
  intros m q text len p d txt (_ & H2 & _).
  rewrite <- (Z.add_0_r (q + 8)) at 1. rewrite (bytes_at_read segs m (q + 8) _ 0 8 H2) by (rewrite ?length_le8; cbn; lia).
  rewrite firstn_all2 by (rewrite ?length_skipn, ?length_le8; lia). reflexivity.
Qed.

Lemma pj_in_ok_store_p : forall m q text len p d txt, pj_in_ok m q text len p d txt ->
  store_ok segs m (wa q) 8 = true.
Proof.
  intros m q text len p d txt (_ & _ & _ & H4 & _).
  rewrite <- (Z.add_0_r q) at 1. apply (wr_at_store_ok segs m q 24 0 8 H4); cbn; lia.
Qed.

Lemma pj_in_ok_set_p : forall m q text len p d txt p',
  pj_in_ok m q text len p d txt -> text <= p' <= text + len ->
  pj_in_ok (write_to_mem m (wa q) (le8 (Z_to_bv 64 p'))) q text len p' d txt.
Proof.
  intros m q text len p d txt p' H Hp'.
  pose proof (pj_in_ok_bounds m q text len p d txt H) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _).
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj Hp' (conj H9 (conj _ (conj H11 H12))))))))))).
  - apply bytes_at_write_same; rewrite ?length_le8; lia.
  - apply bytes_at_write_other; [exact H2 | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
  - apply bytes_at_write_other; [exact H3 | lia | rewrite length_le8; lia | rewrite length_le4, length_le8; lia].
  - apply wr_at_write. exact H4.
  - apply bytes_at_write_other; [exact H10 | lia | rewrite length_le8; lia | rewrite length_le8; lia].
Qed.

Lemma pj_in_ok_transport : forall W m m' q text len p d txt,
  pj_in_ok m q text len p d txt -> munch W m m' -> wmono segs m m' ->
  disjoint_from W q 24 -> disjoint_from W text len -> pj_in_ok m' q text len p d txt.
Proof.
  intros W m m' q text len p d txt H MU WM D1 D2.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D1 | lia | lia]].
  - eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le8; eapply disjoint_from_sub; [exact D1 | lia | lia]].
  - eapply bytes_at_transport; [exact H3 | exact MU | rewrite length_le4; eapply disjoint_from_sub; [exact D1 | lia | lia]].
  - exact (wr_at_transport segs m m' q 24 H4 WM).
  - eapply bytes_at_transport; [exact H10 | exact MU | rewrite H9; exact D2].
Qed.

Lemma pj_in_ok_write_other : forall m q text len p d txt a bs,
  pj_in_ok m q text len p d txt -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  disjoint_from [(q, q + 24); (text, text + len)] a (Z.of_nat (length bs)) ->
  pj_in_ok (write_to_mem m (wa a) bs) q text len p d txt.
Proof.
  intros m q text len p d txt a bs H Ha Hl D. cbn [disjoint_from] in D.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
  - apply bytes_at_write_other; [exact H1 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H2 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H3 | lia | lia | rewrite length_le4; lia].
  - apply wr_at_write. exact H4.
  - apply bytes_at_write_other; [exact H10 | lia | lia | rewrite H9; lia].
Qed.

End WithSegs.
