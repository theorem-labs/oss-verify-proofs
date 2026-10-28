(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require FseNCountRT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma hForall_Znth : forall (P : Z -> Prop) (l : list Z) i, Forall P l -> 0 <= i < Zlength l -> P (Znth i l).
Proof.
  intros P l i H Hi. unfold Znth, Zlength in *. rewrite Forall_forall in H. apply H. apply nth_In. lia.
Qed.

(* [comment removed for export] *)
Fixpoint psum (k : nat) (f : Z -> Z) : Z :=
  match k with O => 0 | S k' => psum k' f + f (Z.of_nat k') end.

Lemma psum_ext k f g : (forall v, 0 <= v < Z.of_nat k -> f v = g v) -> psum k f = psum k g.
Proof.
  induction k as [|k IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite IH by (intros v Hv; apply H; lia). rewrite H by lia. reflexivity.
Qed.
Lemma psum_nonneg k f : (forall v, 0 <= v < Z.of_nat k -> 0 <= f v) -> 0 <= psum k f.
Proof.
  induction k as [|k IH]; intros H; cbn [psum]; [lia|].
  specialize (IH ltac:(intros v Hv; apply H; lia)). specialize (H (Z.of_nat k) ltac:(lia)). lia.
Qed.
Lemma psum_mono k k' f : (k <= k')%nat -> (forall v, 0 <= v < Z.of_nat k' -> 0 <= f v) -> psum k f <= psum k' f.
Proof.
  intros LE H. induction LE as [|k' LE IH]; [lia|]. cbn [psum].
  specialize (IH ltac:(intros v Hv; apply H; lia)). specialize (H (Z.of_nat k') ltac:(lia)). lia.
Qed.
Lemma psum_add_ind k f a c : 0 <= a ->
  psum k (fun v => f v + (if v =? a then c else 0)) = psum k f + (if a <? Z.of_nat k then c else 0).
Proof.
  intros Ha. induction k as [|k IH]; cbn [psum].
  - destruct (Z.ltb_spec a (Z.of_nat 0)); lia.
  - rewrite IH. destruct (Z.eqb_spec (Z.of_nat k) a), (Z.ltb_spec a (Z.of_nat k)), (Z.ltb_spec a (Z.of_nat (S k))); lia.
Qed.
Lemma psum_scale k f c : psum k (fun v => c * f v) = c * psum k f.
Proof. induction k as [|k IH]; cbn [psum]; [lia|]. rewrite IH. lia. Qed.
Lemma psum_zero k f : (forall v, 0 <= v < Z.of_nat k -> f v = 0) -> psum k f = 0.
Proof.
  induction k as [|k IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite IH by (intros v Hv; apply H; lia). rewrite H by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hcount_cons a t w : hcount (a :: t) w = hcount t w + (if w =? a then 1 else 0).
Proof.
  unfold hcount. cbn [count_occ]. destruct (Z.eq_dec a w) as [->|NE].
  - rewrite Z.eqb_refl. lia.
  - destruct (Z.eqb_spec w a); [congruence | lia].
Qed.

Lemma count_total ws : Forall (fun w => 0 <= w <= 12) ws -> psum 13 (hcount ws) = Zlength ws.
Proof.
  induction 1 as [|a t Ha _ IH]; [reflexivity|].
  rewrite (psum_ext 13 (hcount (a :: t)) (fun v => hcount t v + (if v =? a then 1 else 0))) by (intros; apply hcount_cons).
  rewrite psum_add_ind by lia. rewrite IH. unfold Zlength. cbn [length].
  destruct (Z.ltb_spec a (Z.of_nat 13)); lia.
Qed.

Lemma kraft_by_counts ws : Forall (fun w => 0 <= w <= 12) ws -> psum 13 (fun v => hcount ws v * hw_cells v) = hw_total ws.
Proof.
  induction 1 as [|a t Ha _ IH]; [reflexivity|]. cbn [hw_total].
  rewrite (psum_ext 13 _ (fun v => hcount t v * hw_cells v + (if v =? a then hw_cells a else 0))).
  2:{ intros v Hv. rewrite hcount_cons. destruct (Z.eqb_spec v a) as [->|NE]; lia. }
  rewrite psum_add_ind by lia. rewrite IH. destruct (Z.ltb_spec a (Z.of_nat 13)); lia.
Qed.

(* [comment removed for export] *)
Definition xcur (rank : list Z) (w : Z) : Z := psum (Z.to_nat w) (fun v => Znth v rank * hw_cells v).
Definition xsym (rank : list Z) (w : Z) : Z := psum (Z.to_nat w) (fun v => Znth v rank).

Section Stats.
  Variables (ws rank : list Z) (tl : Z).
  Hypothesis OK : huf_stats_ok ws rank tl.

  Lemma st_w12 : Forall (fun w => 0 <= w <= 12) ws.
  Proof. destruct OK as (TL & _ & FA & _). eapply Forall_impl; [|exact FA]. cbv beta. intros; lia. Qed.

  Lemma st_rank_nonneg v : 0 <= v <= 12 -> 0 <= Znth v rank.
  Proof. intros Hv. destruct OK as (_ & _ & _ & _ & CNT & _). rewrite (CNT v Hv). apply hcount_nonneg. Qed.

  (* [comment removed for export] *)
  Lemma st_rank_high v : tl < v <= 12 -> Znth v rank = 0.
  Proof.
    intros Hv. destruct OK as (TL & _ & FA & _ & CNT & _). rewrite (CNT v ltac:(lia)). unfold hcount.
    assert (E : count_occ Z.eq_dec ws v = 0%nat); [|rewrite E; reflexivity].
    apply count_occ_not_In. intros HI. rewrite Forall_forall in FA. specialize (FA v HI). lia.
  Qed.

  Lemma xsym_step w : 0 <= w -> xsym rank (w + 1) = xsym rank w + Znth w rank.
  Proof. intros Hw. unfold xsym. replace (Z.to_nat (w + 1)) with (S (Z.to_nat w)) by lia. cbn [psum]. rewrite Z2Nat.id by lia. reflexivity. Qed.
  Lemma xcur_step w : 0 <= w -> xcur rank (w + 1) = xcur rank w + Znth w rank * hw_cells w.
  Proof. intros Hw. unfold xcur. replace (Z.to_nat (w + 1)) with (S (Z.to_nat w)) by lia. cbn [psum]. rewrite Z2Nat.id by lia. reflexivity. Qed.

  Lemma xsym_total : xsym rank 13 = Zlength ws.
  Proof.
    unfold xsym. change (Z.to_nat 13) with 13%nat. rewrite <- (count_total ws st_w12).
    apply psum_ext. intros v Hv. destruct OK as (_ & _ & _ & _ & CNT & _). apply CNT. lia.
  Qed.
  Lemma xsym_mono w w' : 0 <= w <= w' -> w' <= 13 -> xsym rank w <= xsym rank w'.
  Proof. intros H1 H2. unfold xsym. apply psum_mono; [lia|]. intros v Hv. apply st_rank_nonneg. lia. Qed.
  Lemma xsym_nonneg w : 0 <= w <= 13 -> 0 <= xsym rank w.
  Proof. intros H. unfold xsym. apply psum_nonneg. intros v Hv. apply st_rank_nonneg. lia. Qed.

  Lemma xcur_total : xcur rank 13 = 2^tl.
  Proof.
    unfold xcur. change (Z.to_nat 13) with 13%nat. destruct OK as (_ & _ & _ & _ & CNT & KR). rewrite <- KR, <- (kraft_by_counts ws st_w12).
    apply psum_ext. intros v Hv. rewrite CNT by lia. reflexivity.
  Qed.
  Lemma xcur_mono w w' : 0 <= w <= w' -> w' <= 13 -> xcur rank w <= xcur rank w'.
  Proof.
    intros H1 H2. unfold xcur. apply psum_mono; [lia|]. intros v Hv.
    apply Z.mul_nonneg_nonneg; [apply st_rank_nonneg; lia | apply hw_cells_nonneg].
  Qed.
  Lemma xcur_nonneg w : 0 <= w <= 13 -> 0 <= xcur rank w.
  Proof.
    intros H. unfold xcur. apply psum_nonneg. intros v Hv.
    apply Z.mul_nonneg_nonneg; [apply st_rank_nonneg; lia | apply hw_cells_nonneg].
  Qed.
  (* [comment removed for export] *)
  Lemma xcur_end : xcur rank (tl + 1) = 2^tl.
  Proof.
    rewrite <- xcur_total. destruct OK as (TL & _).
    assert (G : forall k, (Z.to_nat (tl + 1) <= k <= 13)%nat -> psum k (fun v => Znth v rank * hw_cells v) = xcur rank (tl + 1)).
    { induction k as [|k IH]; intros Hk.
      - unfold xcur. replace (Z.to_nat (tl + 1)) with 0%nat by lia. reflexivity.
      - destruct (Nat.eq_dec (Z.to_nat (tl + 1)) (S k)) as [E|NE]; [unfold xcur; rewrite E; reflexivity|].
        cbn [psum]. rewrite IH by lia. rewrite st_rank_high by lia. lia. }
    symmetry. apply G. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sort_slot n w : 0 <= n < Zlength ws -> Znth n ws = w ->
    0 <= w <= tl /\ 0 <= xsym rank w + hcount (firstn (Z.to_nat n) ws) w < Zlength ws.
  Proof.
    intros Hn HW. destruct OK as (TL & _ & FA & _ & CNT & _).
    assert (WR : 0 <= w <= tl) by (rewrite <- HW; apply (hForall_Znth _ ws n FA Hn)).
    split; [exact WR|].
    pose proof (xsym_nonneg w ltac:(lia)). pose proof (hcount_nonneg (firstn (Z.to_nat n) ws) w).
    split; [lia|].
    assert (SPL : ws = firstn (Z.to_nat n) ws ++ w :: skipn (S (Z.to_nat n)) ws).
    { rewrite <- HW. unfold Znth. unfold Zlength in Hn. rewrite <- (firstn_skipn (Z.to_nat n) ws) at 1. f_equal.
      destruct (skipn (Z.to_nat n) ws) as [|a t] eqn:E.
      - exfalso. pose proof (length_skipn (Z.to_nat n) ws) as L. rewrite E in L. cbn [length] in L. lia.
      - replace (nth (Z.to_nat n) ws 0) with a.
        + f_equal. replace (S (Z.to_nat n)) with (1 + Z.to_nat n)%nat by lia. rewrite <- skipn_skipn. rewrite E. reflexivity.
        + rewrite <- (firstn_skipn (Z.to_nat n) ws) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
          rewrite length_firstn. replace (Z.to_nat n - Nat.min (Z.to_nat n) (length ws))%nat with 0%nat by lia. rewrite E. reflexivity. }
    assert (C1 : hcount (firstn (Z.to_nat n) ws) w + 1 <= hcount ws w).
    { rewrite SPL at 2. rewrite hcount_app, hcount_cons. rewrite Z.eqb_refl. pose proof (hcount_nonneg (skipn (S (Z.to_nat n)) ws) w). lia. }
    pose proof (xsym_step w ltac:(lia)) as ST. rewrite (CNT w ltac:(lia)) in ST.
    pose proof (xsym_mono (w + 1) 13 ltac:(lia) ltac:(lia)). rewrite xsym_total in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sort_step n w (rst : list Z) : 0 <= n < Zlength ws -> Znth n ws = w -> tl < Zlength rst ->
    (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v + hcount (firstn (Z.to_nat n) ws) v) ->
    forall v, 0 <= v <= tl -> Znth v (Zupd w (Znth w rst + 1) rst) = xsym rank v + hcount (firstn (Z.to_nat (n + 1)) ws) v.
  Proof.
    intros Hn HW HL INV v Hv. destruct (sort_slot n w Hn HW) as (WR & _).
    assert (E : firstn (Z.to_nat (n + 1)) ws = firstn (Z.to_nat n) ws ++ [w]).
    { replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. rewrite <- HW. unfold Znth.
      apply FseNCountRT.firstn_S_nth. unfold Zlength in Hn. lia. }
    rewrite E, hcount_app, hcount_one. destruct (Z.eq_dec w v) as [->|NE].
    - rewrite Znth_Zupd_same by lia. rewrite INV by lia. lia.
    - rewrite Znth_Zupd_other by lia. rewrite INV by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fill_slot w s : 1 <= w <= tl -> 0 <= s < Znth w rank ->
    0 <= xsym rank w + s < Zlength ws /\ 0 <= xcur rank w + s * hw_cells w /\ xcur rank w + s * hw_cells w + hw_cells w <= 2^tl.
  Proof.
    intros Hw Hs. destruct OK as (TL & _).
    pose proof (xsym_nonneg w ltac:(lia)). pose proof (xcur_nonneg w ltac:(lia)). pose proof (hw_cells_nonneg w).
    pose proof (xsym_step w ltac:(lia)) as S1. pose proof (xsym_mono (w + 1) 13 ltac:(lia) ltac:(lia)) as S2. rewrite xsym_total in S2.
    pose proof (xcur_step w ltac:(lia)) as C1. pose proof (xcur_mono (w + 1) (tl + 1) ltac:(lia) ltac:(lia)) as C2. rewrite xcur_end in C2.
    split; [lia|]. split; [nia|]. nia.
  Qed.
End Stats.

(* [comment removed for export] *)
Definition resc (s w : Z) : Z := if w =? 0 then 0 else w + s.

Definition rank_resc (s : Z) (rank rank' : list Z) : Prop :=
  Zlength rank' = 13 /\
  forall v, 0 <= v <= 12 -> Znth v rank' = if v =? 0 then Znth 0 rank else if v <=? s then 0 else Znth (v - s) rank.

Lemma hw_cells_resc s w : 0 <= s -> 0 <= w -> hw_cells (resc s w) = 2^s * hw_cells w.
Proof.
  intros Hs Hw. unfold resc, hw_cells. destruct (Z.eqb_spec w 0) as [->|NZ]; [cbn; lia|].
  destruct (Z.eqb_spec (w + s) 0); [lia|]. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma hw_total_resc s ws : 0 <= s -> Forall (fun w => 0 <= w) ws -> hw_total (map (resc s) ws) = 2^s * hw_total ws.
Proof.
  intros Hs. induction 1 as [|a t Ha _ IH]; [cbn; lia|]. cbn [map hw_total]. rewrite IH, hw_cells_resc by lia. lia.
Qed.

Lemma hcount_resc s ws v : 0 < s -> Forall (fun w => 0 <= w) ws -> 0 <= v ->
  hcount (map (resc s) ws) v = if v =? 0 then hcount ws 0 else if v <=? s then 0 else hcount ws (v - s).
Proof.
  intros Hs. induction 1 as [|a t Ha _ IH]; intros Hv.
  - cbn [map]. rewrite !hcount_nil. destruct (v =? 0), (v <=? s); reflexivity.
  - cbn [map]. rewrite hcount_cons, IH by lia. unfold resc.
    destruct (Z.eqb_spec v 0) as [->|NZ].
    + rewrite hcount_cons. destruct (Z.eqb_spec a 0) as [->|NA]; [reflexivity|].
      destruct (Z.eqb_spec 0 (a + s)); [lia|]. destruct (Z.eqb_spec 0 a); [lia | reflexivity].
    + destruct (Z.leb_spec v s).
      * destruct (Z.eqb_spec a 0); [destruct (Z.eqb_spec v 0); lia|]. destruct (Z.eqb_spec v (a + s)); lia.
      * rewrite hcount_cons. destruct (Z.eqb_spec a 0) as [->|NA].
        -- destruct (Z.eqb_spec v 0); [lia|]. destruct (Z.eqb_spec (v - s) 0); [lia | reflexivity].
        -- destruct (Z.eqb_spec v (a + s)), (Z.eqb_spec (v - s) a); lia.
Qed.

Lemma huf_stats_rescale ws rank rank' tl s : huf_stats_ok ws rank tl -> 0 < s -> tl + s <= 12 -> rank_resc s rank rank' ->
  huf_stats_ok (map (resc s) ws) rank' (tl + s).
Proof.
  intros OK Hs HT (RL & RV). pose proof OK as (TL & LEN & FA & _ & CNT & KR).
  assert (FA0 : Forall (fun w => 0 <= w) ws) by (eapply Forall_impl; [|exact FA]; cbv beta; intros; lia).
  split; [lia|]. split; [unfold Zlength in *; rewrite length_map; exact LEN|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact FA]. cbv beta. intros w Hw. unfold resc. destruct (w =? 0); lia. }
  split; [exact RL|]. split.
  - intros v Hv. rewrite (RV v Hv). rewrite (hcount_resc s ws v Hs FA0) by lia.
    destruct (Z.eqb_spec v 0); [apply CNT; lia|]. destruct (Z.leb_spec v s); [reflexivity|]. apply CNT. lia.
  - rewrite (hw_total_resc s ws ltac:(lia) FA0). rewrite KR. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resc_step_nat : forall s n (l : list Z), (n < length l)%nat ->
  upd_nat n (resc s (nth n l 0)) (map (resc s) (firstn n l) ++ skipn n l) = map (resc s) (firstn (S n) l) ++ skipn (S n) l.
Proof.
  intros s. induction n as [|n IH]; intros [|a l] H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [firstn map skipn app upd_nat nth]. f_equal. apply IH. lia.
Qed.
Lemma resc_nth_nat : forall s n (l : list Z), nth n (map (resc s) (firstn n l) ++ skipn n l) 0 = nth n l 0.
Proof.
  intros s. induction n as [|n IH]; intros [|a l]; try reflexivity. cbn [firstn map skipn app nth]. apply IH.
Qed.
Lemma resc_len_nat : forall s n (l : list Z), length (map (resc s) (firstn n l) ++ skipn n l) = length l.
Proof. intros s n l. rewrite length_app, length_map, length_firstn, length_skipn. lia. Qed.

(* [comment removed for export] *)
Definition shifted (s sc : Z) (rank cur : list Z) : Prop :=
  Zlength cur = 13 /\
  forall v, 0 <= v <= 12 -> Znth v cur = if (s <? v) && (v <=? 11) then Znth (v - sc) rank else Znth v rank.

Lemma shifted_init sc rank : Zlength rank = 13 -> shifted 11 sc rank rank.
Proof.
  intros L. split; [exact L|]. intros v Hv. destruct (Z.ltb_spec 11 v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; lia.
Qed.

Lemma shifted_step s sc rank cur : shifted s sc rank cur -> 0 < sc < s -> s <= 11 ->
  Znth (s - sc) cur = Znth (s - sc) rank /\ shifted (s - 1) sc rank (Zupd s (Znth (s - sc) rank) cur).
Proof.
  intros (L & H) Hs Hs11.
  assert (E : Znth (s - sc) cur = Znth (s - sc) rank).
  { rewrite H by lia. destruct (Z.ltb_spec s (s - sc)); [lia | reflexivity]. }
  split; [exact E|]. split; [unfold Zlength in *; rewrite Zupd_length; exact L|].
  intros v Hv. destruct (Z.eq_dec v s) as [->|NE].
  - rewrite Znth_Zupd_same by lia. destruct (Z.ltb_spec (s - 1) s), (Z.leb_spec s 11); cbn [andb]; first [lia | reflexivity].
  - rewrite Znth_Zupd_other by lia. rewrite H by lia.
    destruct (Z.ltb_spec s v), (Z.ltb_spec (s - 1) v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; lia.
Qed.

Lemma znth_resc_list a sc (l : list Z) v : 0 <= sc -> 0 <= v ->
  Znth v ([a] ++ repeat 0 (Z.to_nat sc) ++ skipn (Z.to_nat (sc + 1)) l) = if v =? 0 then a else if v <=? sc then 0 else Znth v l.
Proof.
  intros Hsc Hv. unfold Znth. destruct (Z.eqb_spec v 0) as [->|NZ]; [reflexivity|].
  rewrite app_nth2 by (cbn [length]; lia). cbn [length].
  destruct (Z.leb_spec v sc) as [LE|GT].
  - rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
    rewrite nth_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma shifted_resc sc rank cur tl : shifted sc sc rank cur -> 0 < sc -> tl + sc = 11 -> 1 <= tl ->
  (forall v, tl < v <= 12 -> Znth v rank = 0) ->
  rank_resc sc rank ([Znth 0 cur] ++ repeat 0 (Z.to_nat sc) ++ skipn (Z.to_nat (sc + 1)) cur).
Proof.
  intros (L & H) Hsc HT TL HI. split.
  - unfold Zlength in *. rewrite !length_app, repeat_length, length_skipn. cbn [length]. lia.
  - intros v Hv. rewrite znth_resc_list by lia.
    destruct (Z.eqb_spec v 0) as [->|NZ]; [rewrite H by lia; destruct (Z.ltb_spec sc 0); [lia | reflexivity]|].
    destruct (Z.leb_spec v sc); [reflexivity|]. rewrite H by lia.
    destruct (Z.ltb_spec sc v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; try lia.
    assert (v = 12) by lia. subst v. rewrite (HI 12) by lia. rewrite (HI (12 - sc)) by lia. reflexivity.
Qed.
