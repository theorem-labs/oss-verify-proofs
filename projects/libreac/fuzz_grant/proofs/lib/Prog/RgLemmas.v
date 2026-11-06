From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_ro_disj : forall m d n s bs,
  mem_inv rsegs m -> wr_at rsegs m d n -> ro_bytes rsegs s bs -> 0 < n -> 0 <= s -> (0 < length bs)%nat ->
  d + n <= s \/ s + Z.of_nat (length bs) <= d.
Proof.
  intros m d n s bs HI (Hd & Hdn & HW) HR Hn Hs Hl.
  destruct (Z_le_gt_dec (d + n) s) as [?|H1]; [left; lia|].
  destruct (Z_le_gt_dec (s + Z.of_nat (length bs)) d) as [?|H2]; [right; lia|].
  exfalso.
  destruct (nth_error bs (Z.to_nat (Z.max d s - s))) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  pose proof (ro_bytes_nth rsegs bs s _ b HR E) as [_ Hro].
  replace (s + Z.of_nat (Z.to_nat (Z.max d s - s))) with (Z.max d s) in Hro by lia.
  specialize (HW (Z.max d s - d) ltac:(lia)). replace (d + (Z.max d s - d)) with (Z.max d s) in HW by lia.
  destruct (m (wa (Z.max d s))) eqn:Em.
  - pose proof (HI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa (Z.max d s)) HW Em). congruence.
Qed.

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; (split; [lia|]; split; [lia|]); intros i Hi.
    + apply H; lia.
    + replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H; lia.
  - intros ((Ha & Hl & Hx) & (Hb & Hm & Hy)). split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n1); [apply Hx; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hy; lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite (wr_at_app m A) by lia. split.
  - intros [[[W1 W2] B] [X Y]]. apply (bytes_at_app rsegs) in B. destruct B as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1. tauto.
  - intros [[[W1 B1] X] [[W2 B2] Y]]. split; [split; [tauto|] | tauto].
    apply (bytes_at_app rsegs). split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
Qed.

Lemma bytes_at_sub : forall m A bs k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n (Ha & Hl & H) Hk. split; [lia|]. split.
  - rewrite firstn_length, skipn_length. lia.
  - intros i Hi. rewrite firstn_length, skipn_length in Hi.
    replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
    rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i n); [|lia].
    rewrite nth_error_skipn. reflexivity.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma le1_byte : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros. unfold le1. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. rewrite unsigned_lit_wrap. apply (mod_mod8_of_modw z 64). lia.
Qed.

Lemma skipn_app_len : forall {A} (x y : list A) n, length x = n -> skipn n (x ++ y) = y.
Proof. intros A x y n <-. induction x as [|a x IH]; cbn; [reflexivity|exact IH]. Qed.

Lemma rw_cells_join2 : forall m A b1 b2 bs,
  rw_cells rsegs m A [C1 b1; C1 b2] -> rw_cells rsegs m (A + 2) [CB 32 bs] ->
  rw_cells rsegs m A [CB 34 (b1 :: b2 :: bs)].
Proof.
  intros m A b1 b2 bs H1 H2.
  assert (H : rw_cells rsegs m A ([C1 b1; C1 b2] ++ [CB 32 bs])) by (apply rw_cells_app; split; [exact H1 | exact H2]).
  apply (rw_cells_merge rsegs m A [] ([C1 b1; C1 b2] ++ [CB 32 bs]) []) in H.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma rw_cells_cb_split : forall m A n1 n2 bs, 0 <= n1 -> 0 <= n2 ->
  rw_cells rsegs m A [CB (Z.to_nat (n1 + n2)) bs] ->
  rw_cells rsegs m A [CB (Z.to_nat n1) (firstn (Z.to_nat n1) bs)] /\
  rw_cells rsegs m (A + n1) [CB (Z.to_nat n2) (skipn (Z.to_nat n1) bs)].
Proof.
  intros m A n1 n2 bs H1 H2 H.
  pose proof (proj1 (proj1 H)) as Hwf. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hlen _].
  apply (rw_cells_split_CB rsegs m A [] _ bs [] [Z.to_nat n1; Z.to_nat n2]) in H; [| cbn; lia].
  cbn [app mk_CB_cells] in H.
  apply (proj1 (rw_cells_app m A [CB (Z.to_nat n1) (firstn (Z.to_nat n1) bs)] _)) in H.
  destruct H as [Ha Hb]. split; [exact Ha|].
  cbn [cells_size csize] in Hb. rewrite Nat.add_0_r, Z2Nat.id in Hb by lia.
  rewrite firstn_all2 in Hb by (rewrite skipn_length; lia). exact Hb.
Qed.

Lemma rw_cells_cb_join : forall m A n1 n2 b1 b2, 0 <= n1 -> 0 <= n2 ->
  rw_cells rsegs m A [CB (Z.to_nat n1) b1] -> rw_cells rsegs m (A + n1) [CB (Z.to_nat n2) b2] ->
  rw_cells rsegs m A [CB (Z.to_nat (n1 + n2)) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2 Ha Hb.
  assert (H : rw_cells rsegs m A ([CB (Z.to_nat n1) b1] ++ [CB (Z.to_nat n2) b2])).
  { apply rw_cells_app. split; [exact Ha|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact Hb. }
  apply (rw_cells_merge rsegs m A [] ([CB (Z.to_nat n1) b1] ++ [CB (Z.to_nat n2) b2]) []) in H.
  cbn [app cells_size csize cells_bytes cbytes] in H. rewrite !app_nil_r, Nat.add_0_r in H.
  rewrite Z2Nat.inj_add by lia. exact H.
Qed.

Lemma bytes_at_munch : forall W m m' a bs,
  bytes_at rsegs m a bs -> munch W m m' -> disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) HM HD. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd.
  rewrite (HM (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply (disjoint_outside W a (Z.of_nat (length bs))); [exact HD | lia].
Qed.

Lemma row_keep : forall W m m',
  bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES -> munch W m m' -> disjoint_from W CTRL_ROW 24 ->
  bytes_at rsegs m' CTRL_ROW CTRL_ROW_BYTES.
Proof. intros W m m' H HM HD. exact (bytes_at_munch W m m' _ _ H HM HD). Qed.

(* The store tactics transport or drop every [bytes_at] fact on the current memory; a caller that keeps
   the row fact on its start memory and rebuilds it through its footprint [munch] wraps it in [row_at]. *)
Definition row_at (m : word -> option byte) : Prop := bytes_at rsegs m CTRL_ROW CTRL_ROW_BYTES.
