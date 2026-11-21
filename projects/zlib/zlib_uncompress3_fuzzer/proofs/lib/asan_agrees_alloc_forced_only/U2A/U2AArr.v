(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Fixpoint u16s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le2 w ++ u16s ws' end.

Lemma u16s_length : forall ws, length (u16s ws) = (2 * length ws)%nat.
Proof. induction ws; cbn -[le2]; [reflexivity|]. rewrite app_length, length_le2, IHws. lia. Qed.
Lemma u16s_app : forall a b, u16s (a ++ b) = u16s a ++ u16s b.
Proof. induction a; intros; cbn -[le2]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

Lemma u16s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u16s ws = u16s pre ++ le2 w ++ u16s post /\ length (u16s pre) = (2 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u16s_app. cbn -[le2]. rewrite u16s_length. repeat split; lia.
Qed.

Lemma u16s_ext : forall l l', length l = length l' ->
  (forall k w w', nth_error l k = Some w -> nth_error l' k = Some w' -> le2 w = le2 w') -> u16s l = u16s l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] HL HE; cbn -[le2] in *; try discriminate; [reflexivity|].
  rewrite (HE 0%nat x y eq_refl eq_refl). f_equal. apply IH; [lia|].
  intros k w w' H1 H2. exact (HE (S k) w w' H1 H2).
Qed.
Lemma u32s_ext : forall l l', length l = length l' ->
  (forall k w w', nth_error l k = Some w -> nth_error l' k = Some w' -> le4 w = le4 w') -> u32s l = u32s l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] HL HE; cbn -[le4] in *; try discriminate; [reflexivity|].
  rewrite (HE 0%nat x y eq_refl eq_refl). f_equal. apply IH; [lia|].
  intros k w w' H1 H2. exact (HE (S k) w w' H1 H2).
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition u16arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
  bytes_at segs m A (u16s ws) /\ wr_at segs m A (2 * Z.of_nat (length ws)).

Lemma u16arr_read : forall m A ws (i : Z) w a,
  u16arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i)%Z with (Z.of_nat (2 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !app_length, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u16arr_store_ok : forall m A ws (i : Z) a,
  u16arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 2 * i) ->
  store_ok segs m a 2 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u16arr_write : forall m A ws (i : Z) (v : word),
  u16arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u16arr (write_to_mem m (wa (A + 2 * i)) (le2 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u16s ws) (2 * i) (le2 v) Hb); [lia|].
      rewrite length_le2, u16s_length. lia. }
    rewrite Hupd, E, !u16s_app. cbn [u16s].
    replace (Z.to_nat (2 * i)) with (length (u16s pre)) by (rewrite u16s_length; lia).
    apply upd_bytes_mid. rewrite !length_le2. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

Lemma u16arr_frame : forall m A ws a xs,
  u16arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 2 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u16arr (write_to_mem m (wa a) xs) A ws.
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u16s_length. lia.
Qed.

Lemma u16arr_transport : forall W m m' A ws,
  u16arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (2 * Z.of_nat (length ws)) -> u16arr m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u16s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma u16arr_ext : forall m A ws ws', u16arr m A ws -> u16s ws = u16s ws' -> length ws = length ws' -> u16arr m A ws'.
Proof. intros m A ws ws' [Hb Hw] E L. split; [rewrite <- E; exact Hb| rewrite <- L; exact Hw]. Qed.
Lemma u32arr_ext : forall m A ws ws', u32arr segs m A ws -> u32s ws = u32s ws' -> length ws = length ws' -> u32arr segs m A ws'.
Proof. intros m A ws ws' [Hb Hw] E L. split; [rewrite <- E; exact Hb| rewrite <- L; exact Hw]. Qed.

End WithSegs.

Open Scope Z_scope.

Definition fws (f : Z -> Z) (n : nat) : list word := map (fun i => Z_to_bv 64 (f (Z.of_nat i))) (seq 0 n).
Definition fupd (f : Z -> Z) (i v : Z) : Z -> Z := fun j => if Z.eqb j i then v else f j.

Lemma fws_length : forall f n, length (fws f n) = n.
Proof. intros f n. unfold fws. rewrite map_length, seq_length. reflexivity. Qed.

Lemma fws_nth : forall f n k, (k < n)%nat -> nth_error (fws f n) k = Some (Z_to_bv 64 (f (Z.of_nat k))).
Proof.
  intros f n k H. unfold fws. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec k n); [|lia]. reflexivity.
Qed.

Lemma fupd_same : forall f i v, fupd f i v i = v.
Proof. intros f i v. unfold fupd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma fupd_other : forall f i v j, j <> i -> fupd f i v j = f j.
Proof. intros f i v j H. unfold fupd. destruct (Z.eqb_spec j i); [contradiction| reflexivity]. Qed.

Lemma fws_upd_nth : forall f n i (v : word) x k w w',
  (i < n)%nat ->
  nth_error (upd (fws f n) i v) k = Some w -> nth_error (fws (fupd f (Z.of_nat i) x) n) k = Some w' ->
  (k = i -> w = v /\ w' = Z_to_bv 64 x) /\ (k <> i -> w = w').
Proof.
  intros f n i v x k w w' Hi H1 H2.
  assert (Hk : (k < n)%nat).
  { apply nth_error_lt in H2. rewrite fws_length in H2. exact H2. }
  rewrite fws_nth in H2 by exact Hk. inversion H2; subst w'; clear H2.
  split; intros E.
  - subst k. rewrite nth_error_upd_same in H1 by (rewrite fws_length; exact Hi). inversion H1; subst w.
    rewrite fupd_same. split; reflexivity.
  - rewrite nth_error_upd_other in H1 by (intros E'; apply E; symmetry; exact E').
    rewrite fws_nth in H1 by exact Hk. inversion H1; subst w.
    rewrite fupd_other by lia. reflexivity.
Qed.

Section FViews.
Variable segs : list Segment.

Definition f8arr (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) : Prop :=
  u8arr segs m A (map (fun i => Z_to_bv 8 (f (Z.of_nat i))) (seq 0 n)).
Definition f16arr (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) : Prop := u16arr segs m A (fws f n).
Definition f32arr (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) : Prop := u32arr segs m A (fws f n).

Lemma f16arr_read : forall m A n f (i : Z) a,
  f16arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (f i))).
Proof.
  intros m A n f i a H Hi Ea.
  eapply (u16arr_read segs m A (fws f n) i); [exact H| | lia| exact Ea].
  rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma f32arr_read : forall m A n f (i : Z) a,
  f32arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (f i))).
Proof.
  intros m A n f i a H Hi Ea.
  eapply (u32arr_read segs m A (fws f n) i); [exact H| | lia| exact Ea].
  rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma f16arr_store_ok : forall m A n f (i : Z) a,
  f16arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + 2 * i) -> store_ok segs m a 2 = true.
Proof. intros m A n f i a H Hi Ea. eapply u16arr_store_ok; [exact H| rewrite fws_length; exact Hi| exact Ea]. Qed.
Lemma f32arr_store_ok : forall m A n f (i : Z) a,
  f32arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + 4 * i) -> store_ok segs m a 4 = true.
Proof. intros m A n f i a H Hi Ea. eapply u32arr_store_ok; [exact H| rewrite fws_length; exact Hi| exact Ea]. Qed.

Lemma f16arr_write : forall m A n f (i : Z) (v : word) x,
  f16arr m A n f -> 0 <= i < Z.of_nat n -> le2 v = le2 (Z_to_bv 64 x) ->
  f16arr (write_to_mem m (wa (A + 2 * i)) (le2 v)) A n (fupd f i x).
Proof.
  intros m A n f i v x H Hi Ev. unfold f16arr in *.
  pose proof (u16arr_write segs m A (fws f n) i v H ltac:(rewrite fws_length; exact Hi)) as W.
  eapply u16arr_ext; [exact W| | rewrite upd_length, !fws_length; reflexivity].
  apply u16s_ext; [rewrite upd_length, !fws_length; reflexivity|].
  intros k w w' H1 H2.
  replace i with (Z.of_nat (Z.to_nat i)) in H2 by lia.
  destruct (fws_upd_nth f n (Z.to_nat i) v x k w w' ltac:(lia) H1 H2) as [S D].
  destruct (Nat.eq_dec k (Z.to_nat i)) as [E|NE].
  - destruct (S E) as [-> ->]. exact Ev.
  - rewrite (D NE). reflexivity.
Qed.
Lemma f32arr_write : forall m A n f (i : Z) (v : word) x,
  f32arr m A n f -> 0 <= i < Z.of_nat n -> le4 v = le4 (Z_to_bv 64 x) ->
  f32arr (write_to_mem m (wa (A + 4 * i)) (le4 v)) A n (fupd f i x).
Proof.
  intros m A n f i v x H Hi Ev. unfold f32arr in *.
  pose proof (u32arr_write segs m A (fws f n) i v H ltac:(rewrite fws_length; exact Hi)) as W.
  eapply u32arr_ext; [exact W| | rewrite upd_length, !fws_length; reflexivity].
  apply u32s_ext; [rewrite upd_length, !fws_length; reflexivity|].
  intros k w w' H1 H2.
  replace i with (Z.of_nat (Z.to_nat i)) in H2 by lia.
  destruct (fws_upd_nth f n (Z.to_nat i) v x k w w' ltac:(lia) H1 H2) as [S D].
  destruct (Nat.eq_dec k (Z.to_nat i)) as [E|NE].
  - destruct (S E) as [-> ->]. exact Ev.
  - rewrite (D NE). reflexivity.
Qed.

Lemma f16arr_transport : forall W m m' A n f,
  f16arr m A n f -> munch W m m' -> wmono segs m m' -> disjoint_from W A (2 * Z.of_nat n) -> f16arr m' A n f.
Proof. intros W m m' A n f H MU WM D. eapply u16arr_transport; eauto. rewrite fws_length. exact D. Qed.
Lemma f32arr_transport : forall W m m' A n f,
  f32arr m A n f -> munch W m m' -> wmono segs m m' -> disjoint_from W A (4 * Z.of_nat n) -> f32arr m' A n f.
Proof. intros W m m' A n f H MU WM D. eapply u32arr_transport; eauto. rewrite fws_length. exact D. Qed.

Lemma f16arr_frame : forall m A n f a xs,
  f16arr m A n f -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + 2 * Z.of_nat n <= a \/ a + Z.of_nat (length xs) <= A) ->
  f16arr (write_to_mem m (wa a) xs) A n f.
Proof. intros m A n f a xs H Ha Hl Hd. unfold f16arr in *. eapply u16arr_frame; eauto. rewrite fws_length. exact Hd. Qed.
Lemma f32arr_frame : forall m A n f a xs,
  f32arr m A n f -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + 4 * Z.of_nat n <= a \/ a + Z.of_nat (length xs) <= A) ->
  f32arr (write_to_mem m (wa a) xs) A n f.
Proof. intros m A n f a xs H Ha Hl Hd. unfold f32arr in *. eapply u32arr_frame; eauto. rewrite fws_length. exact Hd. Qed.
Lemma f8arr_frame : forall m A n f a xs,
  f8arr m A n f -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + Z.of_nat n <= a \/ a + Z.of_nat (length xs) <= A) ->
  f8arr (write_to_mem m (wa a) xs) A n f.
Proof. intros m A n f a xs H Ha Hl Hd. unfold f8arr in *. eapply u8arr_frame; eauto. rewrite length_map, length_seq. exact Hd. Qed.
Lemma f8arr_transport : forall W m m' A n f,
  f8arr m A n f -> munch W m m' -> wmono segs m m' -> disjoint_from W A (Z.of_nat n) -> f8arr m' A n f.
Proof. intros W m m' A n f H MU WM D. unfold f8arr in *. eapply u8arr_transport; eauto. rewrite length_map, length_seq. exact D. Qed.

Lemma f8arr_read : forall m A n f (i : Z) a,
  f8arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (f i)].
Proof.
  intros m A n f i a H Hi Ea. unfold f8arr in H.
  eapply (u8arr_read segs m A _ i); [exact H| | lia| exact Ea].
  rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat i) n) as [_|X]; [| lia].
  cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma f8arr_store_ok : forall m A n f (i : Z) a,
  f8arr m A n f -> 0 <= i < Z.of_nat n -> a = wa (A + i) -> store_ok segs m a 1 = true.
Proof. intros m A n f i a H Hi Ea. unfold f8arr in H. eapply u8arr_store_ok; [exact H| rewrite length_map, length_seq; exact Hi| exact Ea]. Qed.

Lemma f16arr_ext : forall m A n f g, f16arr m A n f -> (forall i, 0 <= i < Z.of_nat n -> f i = g i) -> f16arr m A n g.
Proof.
  intros m A n f g H E. unfold f16arr in *. replace (fws g n) with (fws f n); [exact H|].
  unfold fws. apply map_ext_in. intros k Hk. apply in_seq in Hk. rewrite E by lia. reflexivity.
Qed.
Lemma f32arr_ext : forall m A n f g, f32arr m A n f -> (forall i, 0 <= i < Z.of_nat n -> f i = g i) -> f32arr m A n g.
Proof.
  intros m A n f g H E. unfold f32arr in *. replace (fws g n) with (fws f n); [exact H|].
  unfold fws. apply map_ext_in. intros k Hk. apply in_seq in Hk. rewrite E by lia. reflexivity.
Qed.

End FViews.
