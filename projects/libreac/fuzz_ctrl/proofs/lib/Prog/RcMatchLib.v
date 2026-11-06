From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcParse RcMatch.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma cm_image_nth : forall n A bs, image_bytes segs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|]. cbn in H.
  destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  inversion H; subst bs. destruct i as [|i].
  - rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma cm_bytes_img : forall m A n bs, image_bytes segs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall a, A <= a < A + Z.of_nat n -> mrd segs m (wa a) = seg_rom segs (wa a)) -> bytes_at segs m A bs.
Proof.
  intros m A n bs E H0 H1 H. pose proof (image_bytes_length segs n A bs E) as L.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite H by lia. apply (cm_image_nth n A bs E). lia.
Qed.

Lemma cm_img_apart : forall A n bs lo hi, image_bytes segs A n = Some bs -> (0 < n)%nat -> lo < hi ->
  (forall a, lo <= a < hi -> seg_rom segs (wa a) = None) -> A + Z.of_nat n <= lo \/ hi <= A.
Proof.
  intros A n bs lo hi E Hn Hlh H.
  destruct (Z.le_gt_cases (A + Z.of_nat n) lo) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases hi A) as [G|G]; [right; exact G|]. exfalso.
  pose proof (image_bytes_length segs n A bs E) as LB.
  set (x := Z.max A lo).
  assert (I : (Z.to_nat (x - A) < n)%nat) by lia.
  pose proof (cm_image_nth n A bs E (Z.to_nat (x - A)) I) as R.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in R by lia.
  rewrite (H x) in R by lia.
  symmetry in R. apply nth_error_None in R. lia.
Qed.

Lemma cm_rw_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hn & Hw).
  rewrite (cells_bytes_length cs1 W1) in B2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma cm_rw_join : forall m A B cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn1 & H1)] [[W2 B2] (Hb & Hn2 & H2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply H2. lia.
Qed.

Lemma cm_rw_of_bytes : forall m A bs n, bytes_at segs m A bs -> length bs = n -> wr_at segs m A (Z.of_nat n) ->
  rw_cells segs m A [CB n bs].
Proof.
  intros m A bs n HB HL HW. split; [split|].
  - cbn. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma cm_wr_of_rw : forall m A n bs, rw_cells segs m A [CB n bs] -> wr_at segs m A (Z.of_nat n).
Proof. intros m A n bs [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. exact HW. Qed.

Lemma cm_bytes_of_rw : forall m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[W HB] _]. cbn in W. destruct W as [L _]. cbn [cells_bytes cbytes] in HB.
  rewrite app_nil_r in HB. split; assumption.
Qed.

Lemma cm_frame_split : forall m A B C D c1 c2 c3 cs, csize c1 = 4%nat -> csize c2 = 32%nat -> csize c3 = 36%nat ->
  rw_cells segs m A (c1 :: c2 :: c3 :: cs) -> B = A + 4 -> C = A + 36 -> D = A + 72 ->
  rw_cells segs m A [c1] /\ rw_cells segs m B [c2] /\ rw_cells segs m C [c3] /\ rw_cells segs m D cs.
Proof.
  intros m A B C D c1 c2 c3 cs H1 H2 H3 R -> -> ->.
  destruct (cm_rw_split m A [c1] (c2 :: c3 :: cs) R) as [R1 R'].
  destruct (cm_rw_split m _ [c2] (c3 :: cs) R') as [R2 R''].
  destruct (cm_rw_split m _ [c3] cs R'') as [R3 R4].
  cbn [cells_size] in *. rewrite H1, H2, H3 in *. cbn [Nat.add] in *.
  split; [exact R1|]. split; [exact R2|]. split.
  - replace (A + 36) with (A + Z.of_nat 4 + Z.of_nat 32) by lia. exact R3.
  - replace (A + 72) with (A + Z.of_nat 4 + Z.of_nat 32 + Z.of_nat 36) by lia. exact R4.
Qed.

Lemma cm_frame_release : forall m lo A B C D j0 bb pb cs, stk segs m lo A -> lo <= A ->
  rw_cells segs m A [CB 4 j0] -> rw_cells segs m B [CB 32 bb] -> rw_cells segs m C [CB 36 pb] ->
  rw_cells segs m D cs -> B = A + 4 -> C = A + 36 -> D = A + 72 -> stk segs m lo (D + Z.of_nat (cells_size cs)).
Proof.
  intros m lo A B C D j0 bb pb cs ST HL R1 R2 R3 R4 -> -> ->.
  pose proof (stk_release segs m lo A [CB 4 j0] ST R1 HL) as S1. change (Z.of_nat (cells_size [CB 4 j0])) with 4 in S1.
  pose proof (stk_release segs m lo (A + 4) [CB 32 bb] S1 R2 ltac:(lia)) as S2.
  change (Z.of_nat (cells_size [CB 32 bb])) with 32 in S2. replace (A + 4 + 32) with (A + 36) in S2 by lia.
  pose proof (stk_release segs m lo (A + 36) [CB 36 pb] S2 R3 ltac:(lia)) as S3.
  change (Z.of_nat (cells_size [CB 36 pb])) with 36 in S3. replace (A + 36 + 36) with (A + 72) in S3 by lia.
  exact (stk_release segs m lo (A + 72) cs S3 R4 ltac:(lia)).
Qed.

End WithSegs.

Lemma cm_find_hit : forall b ds i, (i < length ds)%nat -> nth i ds [] = b ->
  (forall j, (j < i)%nat -> nth j ds [] <> b) -> cm_find b ds = Some i.
Proof.
  intros b ds. induction ds as [|d ds IH]; intros i Hi E H; cbn in Hi; [lia|].
  cbn [cm_find]. destruct i as [|i].
  - cbn in E. subst d. rewrite bool_decide_eq_true_2 by reflexivity. reflexivity.
  - rewrite bool_decide_eq_false_2 by exact (H 0%nat ltac:(lia)).
    rewrite (IH i) by (try lia; try exact E; intros j Hj; exact (H (S j) ltac:(lia))). reflexivity.
Qed.

Lemma cm_find_none : forall b ds, (forall j, (j < length ds)%nat -> nth j ds [] <> b) -> cm_find b ds = None.
Proof.
  intros b ds. induction ds as [|d ds IH]; intros H; [reflexivity|].
  cbn [cm_find]. rewrite bool_decide_eq_false_2 by exact (H 0%nat ltac:(cbn; lia)).
  rewrite IH; [reflexivity|]. intros j Hj. exact (H (S j) ltac:(cbn; lia)).
Qed.

Lemma DECLS_length : length DECLS = 11%nat.
Proof. reflexivity. Qed.

Lemma cm_eqb_zxb : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma cm_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma cm_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma cm_gate_false : forall len fb, cm_gate len fb = false -> forall T, want T len fb = 0.
Proof. intros len fb H T. unfold want. rewrite H. reflexivity. Qed.

Lemma cm_want_hit : forall T len fb i, cm_gate len fb = true -> (i < 11)%nat -> nth i DECLS [] = cm_blk fb ->
  (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) -> want T len fb = T + 296 * Z.of_nat i.
Proof.
  intros T len fb i G Hi E H. unfold want. rewrite G. rewrite (cm_find_hit (cm_blk fb) DECLS i); [reflexivity | | exact E | exact H].
  rewrite DECLS_length. exact Hi.
Qed.

Lemma cm_want_none : forall T len fb, (forall j, (j < 11)%nat -> nth j DECLS [] <> cm_blk fb) -> want T len fb = 0.
Proof.
  intros T len fb H. unfold want. destruct (cm_gate len fb); [|reflexivity].
  rewrite cm_find_none; [reflexivity|]. rewrite DECLS_length. exact H.
Qed.

Lemma cm_ltu_neg_l : forall c x, -2^64 <= c < 0 -> 0 <= x < 2^64 ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 x) = (c + 2^64 <? x).
Proof.
  intros c x Hc Hx. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  replace (c mod 2^64) with (c + 2^64); [reflexivity|].
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cm_ltu_neg_r : forall x c, 0 <= x < 2^64 -> -2^64 <= c < 0 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 c) = (x <? c + 2^64).
Proof.
  intros x c Hx Hc. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  replace (c mod 2^64) with (c + 2^64); [reflexivity|].
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.
