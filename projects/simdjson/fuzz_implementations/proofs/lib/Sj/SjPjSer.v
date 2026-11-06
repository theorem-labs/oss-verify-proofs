(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjTape SjTapeInv SjTapeList SjTapeTile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma land_mask56 : forall w, 0 <= w -> Z.land w 72057594037927935 = tval w.
Proof. intros w H. unfold tval. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma shr56_ttype : forall w, Z.shiftr w 56 = ttype w.
Proof. intros w. unfold ttype. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma lor4_le32 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (lor_hi_lo 8 b1 b0) by lia.
  assert (E1 : Z.lor (b3 * 2^24) (b2 * 2^16) = (b3 * 2^8 + b2) * 2^16).
  { replace (b3 * 2^24) with ((b3 * 2^8) * 2^16) by lia.
    rewrite <- (Z.shiftl_mul_pow2 (b3 * 2^8) 16), <- (Z.shiftl_mul_pow2 b2 16), <- Z.shiftl_lor by lia.
    rewrite (lor_hi_lo 8 b3 b2) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  rewrite E1. rewrite (lor_hi_lo 16 (b3 * 2^8 + b2) (b1 * 2^8 + b0)) by lia. lia.
Qed.

Lemma ttype_range : forall w t, ttype w = t -> 0 <= t < 256 -> 0 <= w < 2^64.
Proof.
  intros w t H Ht. unfold ttype in H. pose proof (Z.div_mod w (2^56) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound w (2^56) ltac:(lia)) as M. rewrite H in D. lia.
Qed.

Lemma land_m8 : forall l, 0 <= l < 2^64 -> Z.land l 18446744073709551608 = 8 * (l / 8).
Proof.
  intros l H. change 18446744073709551608 with (Z.shiftl (Z.ones 61) 3).
  replace (8 * (l / 8)) with (Z.shiftl (Z.shiftr l 3) 3) by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec n 3) as [L|L].
  - rewrite (Z.testbit_neg_r (Z.ones 61)), (Z.testbit_neg_r (Z.shiftr l 3)) by lia. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (n - 3 + 3) with n by lia.
    destruct (Z.ltb_spec (n - 3) 61) as [L2|L2].
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
      split; [lia|]. apply Z.lt_le_trans with (2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma land_m8_range : forall l, 0 <= l < 2^64 -> 0 <= Z.land l 18446744073709551608 <= l.
Proof. intros l H. rewrite land_m8 by exact H. pose proof (Z.div_mod l 8 ltac:(lia)). pose proof (Z.mod_pos_bound l 8 ltac:(lia)). lia. Qed.

Definition pj_ne_table : list Z :=
  [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
   0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Definition pj_esc_table : list Z :=
  [6; 92; 117; 48; 48; 48; 48; 0; 6; 92; 117; 48; 48; 48; 49; 0; 6; 92; 117; 48; 48; 48; 50; 0; 6; 92; 117; 48; 48; 48; 51; 0;
   6; 92; 117; 48; 48; 48; 52; 0; 6; 92; 117; 48; 48; 48; 53; 0; 6; 92; 117; 48; 48; 48; 54; 0; 6; 92; 117; 48; 48; 48; 55; 0;
   2; 92; 98; 0; 0; 0; 0; 0; 2; 92; 116; 0; 0; 0; 0; 0; 2; 92; 110; 0; 0; 0; 0; 0; 6; 92; 117; 48; 48; 48; 98; 0;
   2; 92; 102; 0; 0; 0; 0; 0; 2; 92; 114; 0; 0; 0; 0; 0; 6; 92; 117; 48; 48; 48; 101; 0; 6; 92; 117; 48; 48; 48; 102; 0;
   6; 92; 117; 48; 48; 49; 48; 0; 6; 92; 117; 48; 48; 49; 49; 0; 6; 92; 117; 48; 48; 49; 50; 0; 6; 92; 117; 48; 48; 49; 51; 0;
   6; 92; 117; 48; 48; 49; 52; 0; 6; 92; 117; 48; 48; 49; 53; 0; 6; 92; 117; 48; 48; 49; 54; 0; 6; 92; 117; 48; 48; 49; 55; 0;
   6; 92; 117; 48; 48; 49; 56; 0; 6; 92; 117; 48; 48; 49; 57; 0; 6; 92; 117; 48; 48; 49; 97; 0; 6; 92; 117; 48; 48; 49; 98; 0;
   6; 92; 117; 48; 48; 49; 99; 0; 6; 92; 117; 48; 48; 49; 100; 0; 6; 92; 117; 48; 48; 49; 101; 0; 6; 92; 117; 48; 48; 49; 102; 0].

Lemma pj_ne_table_length : length pj_ne_table = 256%nat. Proof. reflexivity. Qed.
Lemma pj_esc_table_length : length pj_esc_table = 256%nat. Proof. reflexivity. Qed.

Definition esc_len (c : Z) : Z := nth (Z.to_nat (8 * c)) pj_esc_table 0.
Lemma esc_len_range : forall c, 0 <= c < 32 -> 2 <= esc_len c <= 6.
Proof.
  intros c Hc. unfold esc_len.
  assert (E : exists k : nat, (k < 32)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); lia).
  destruct E as (k & Hk & ->). replace (Z.to_nat (8 * Z.of_nat k)) with (8 * k)%nat by lia.
  do 32 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

Section Ser.
  Variable T : Z -> Z.
  Variable S : Z -> Z.
  Variable sn : Z.
  Hypothesis Hsn : 0 <= sn < 2^56.

  Local Notation elemS := (elemS T S sn ck_any).
  Local Notation fieldS := (fieldS T S sn).
  Local Notation str_rec := (str_rec T S sn).
  Local Notation ty := (ty T).

  Definition itemS (k : bool) (d : nat) : Z -> Z -> Z -> Z -> Prop :=
    if k then fieldS (elemS d) else elemS d.
  Definition end_ty (k : bool) : Z := if k then t_obj_end else t_arr_end.

  Lemma itemS_lt : forall k d a b x y, itemS k d a b x y -> a < b.
  Proof. intros [|] d a b x y H; [eapply fieldS_lt; exact H| eapply elemS_lt; exact H]. Qed.

  Lemma itemS_cur : forall k d a b x y, itemS k d a b x y -> x <= y /\ (x <= sn -> y <= sn).
  Proof.
    intros [|] d a b x y H; unfold itemS in H.
    - destruct H as (c1 & Hs & Hp). pose proof (str_rec_cur _ _ _ _ _ _ Hs). pose proof (elemS_cur _ _ _ _ _ _ _ _ _ Hp). lia.
    - eapply elemS_cur; exact H.
  Qed.

  Lemma str_rec_ty : forall i c c', str_rec i c c' -> ty i = t_str /\ tval (T i) = c /\ exists l, str_at S sn c l /\ c' = c + l + 5.
  Proof.
    intros i c c' (l & HT & Hs & Hc). pose proof Hs as (H0 & Hl & Hb & _).
    unfold SjTape.ty. rewrite HT, ttype_tword, tval_tword by lia. split; [reflexivity|]. split; [reflexivity|]. exists l. auto.
  Qed.

  Inductive ser_view (d : nat) (i j c c' : Z) : Prop :=
  | sv_atom : (ty i = t_true \/ ty i = t_false \/ ty i = t_null) -> j = i + 1 -> c' = c -> ser_view d i j c c'
  | sv_num : (ty i = t_i64 \/ ty i = t_u64 \/ ty i = t_dbl) -> j = i + 2 -> c' = c -> ser_view d i j c c'
  | sv_str : forall l, ty i = t_str -> tval (T i) = c -> j = i + 1 -> str_at S sn c l -> c' = c + l + 5 -> ser_view d i j c c'
  | sv_arr : forall d' e n, d = Datatypes.S d' -> ty i = t_arr -> j = e + 1 -> tnext (T i) = e + 1 -> ty e = t_arr_end ->
      tilesS (elemS d') (i + 1) e n c c' -> ser_view d i j c c'
  | sv_obj : forall d' e n, d = Datatypes.S d' -> ty i = t_obj -> j = e + 1 -> tnext (T i) = e + 1 -> ty e = t_obj_end ->
      tilesS (fieldS (elemS d')) (i + 1) e n c c' -> ser_view d i j c c'.

  Lemma ck_any_range : forall c cv, ck_any c cv -> 0 <= cv <= CNT_MAX.
  Proof. intros c cv H. exact H. Qed.

  Lemma ser_view_of : forall d i j c c', elemS d i j c c' -> 0 <= i -> j < 2^32 -> ser_view d i j c c'.
  Proof.
    intros d i j c c' H Hi Hj.
    assert (SC : scalarS T S sn i j c c' -> ser_view d i j c c').
    { intros [(Ej & Hw & Ec)|[(Ej & Hw & Ec)|(Ej & l & Hw & Hs & Ec)]].
      - apply sv_atom; [| exact Ej| exact Ec]. unfold SjTape.ty. destruct Hw as [Hw|[Hw|Hw]]; rewrite Hw, ttype_tword by lia; tauto.
      - apply sv_num; [| exact Ej| exact Ec]. unfold SjTape.ty. destruct Hw as [Hw|[Hw|Hw]]; rewrite Hw, ttype_tword by lia; tauto.
      - pose proof Hs as (H0 & Hl & Hb & _).
        apply (sv_str d i j c c' l); [| | exact Ej| exact Hs| exact Ec]; [unfold SjTape.ty|]; rewrite Hw; [apply ttype_tword| apply tval_tword]; lia. }
    destruct d as [|d']; cbn [SjTapeTile.elemS] in H.
    - destruct H as [H|[]]. apply SC. exact H.
    - destruct H as [H|(e & n & cv & Ej & Hck & [(Hw & He & Ht)|(Hw & He & Ht)])]; [apply SC; exact H| |].
      + assert (Hie : i < e) by (pose proof (tilesS_le _ (elemS_lt T S sn ck_any d') _ _ _ _ _ Ht); lia).
        assert (R1 : 0 <= e + 1 < 2^32) by lia.
        apply (sv_arr (Datatypes.S d') i j c c' d' e n); [reflexivity| | exact Ej| | | exact Ht].
        * unfold SjTape.ty. rewrite Hw. apply ttype_cword; [exact R1| exact Hck].
        * rewrite Hw. apply tnext_cword. exact R1.
        * unfold SjTape.ty. rewrite He. apply ttype_tword. lia.
      + assert (Hie : i < e) by (pose proof (tilesS_le _ (fieldS_lt T S sn ck_any d') _ _ _ _ _ Ht); lia).
        assert (R1 : 0 <= e + 1 < 2^32) by lia.
        apply (sv_obj (Datatypes.S d') i j c c' d' e n); [reflexivity| | exact Ej| | | exact Ht].
        * unfold SjTape.ty. rewrite Hw. apply ttype_cword; [exact R1| exact Hck].
        * rewrite Hw. apply tnext_cword. exact R1.
        * unfold SjTape.ty. rewrite He. apply ttype_tword. lia.
  Qed.

  Inductive rest_ok : nat -> list bool -> Z -> Z -> Z -> Z -> Prop :=
  | rest_nil : forall d j c', rest_ok d [] j c' j c'
  | rest_cons : forall d k ks i c e n c1 j c',
      tilesS (itemS k d) i e n c c1 -> ty e = end_ty k -> rest_ok (Datatypes.S d) ks (e + 1) c1 j c' ->
      rest_ok d (k :: ks) i c j c'.

  Lemma rest_ok_nil_inv : forall d i c j c', rest_ok d [] i c j c' -> i = j /\ c = c'.
  Proof. intros d i c j c' H. inversion H; subst. split; reflexivity. Qed.

  Lemma rest_ok_le : forall d ks i c j c', rest_ok d ks i c j c' -> i <= j /\ c <= c' /\ (c <= sn -> c' <= sn).
  Proof.
    intros d ks i c j c' H. induction H as [d j c'|d k ks i c e n c1 j c' Ht He Hr IH]; [lia|].
    pose proof (tilesS_le _ (itemS_lt k d) _ _ _ _ _ Ht) as [L1 _].
    pose proof (tilesS_cur (itemS k d) sn (itemS_cur k d) _ _ _ _ _ Ht) as [L2 L3]. lia.
  Qed.

  Lemma end_ty_cases : forall k, end_ty k = t_arr_end \/ end_ty k = t_obj_end.
  Proof. intros [|]; [right| left]; reflexivity. Qed.

  Lemma elemS_not_end : forall d i j c c', elemS d i j c c' -> 0 <= i -> j < 2^32 -> ty i <> t_arr_end /\ ty i <> t_obj_end.
  Proof.
    intros d i j c c' H Hi Hj. unfold t_arr_end, t_obj_end.
    destruct (ser_view_of _ _ _ _ _ H Hi Hj) as [Ht _ _|Ht _ _|l Ht _ _ _ _|d' e n _ Ht _ _ _ _|d' e n _ Ht _ _ _ _];
      unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in Ht; lia.
  Qed.

  Lemma itemS_not_end : forall k d i j c c', itemS k d i j c c' -> 0 <= i -> j < 2^32 -> ty i <> t_arr_end /\ ty i <> t_obj_end.
  Proof.
    intros [|] d i j c c' H Hi Hj; unfold itemS in H.
    - destruct H as (c1 & Hs & _). destruct (str_rec_ty _ _ _ Hs) as (Ht & _). rewrite Ht. unfold t_str, t_arr_end, t_obj_end. lia.
    - eapply elemS_not_end; eassumption.
  Qed.

  Lemma tilesS_diag : forall (P : Z -> Z -> Z -> Z -> Prop), (forall a b x y, P a b x y -> a < b) ->
    forall e n c c', tilesS P e e n c c' -> c' = c.
  Proof.
    intros P Plt e n c c' H. inversion H as [|i j e0 n0 c0 c1 c2 Hp Ht]; subst; [reflexivity|].
    pose proof (Plt _ _ _ _ Hp). pose proof (tilesS_le P Plt _ _ _ _ _ Ht). lia.
  Qed.

  Lemma rest_ok_end : forall d k ks i c j c', rest_ok d (k :: ks) i c j c' -> 0 <= i -> j < 2^32 ->
    (ty i = t_arr_end \/ ty i = t_obj_end) -> rest_ok (Datatypes.S d) ks (i + 1) c j c'.
  Proof.
    intros d k ks i c j c' H Hi Hj Hty. inversion H as [|d0 k0 ks0 i0 c0 e n c1 j0 c0' Ht He Hr]; subst.
    pose proof (rest_ok_le _ _ _ _ _ _ Hr) as (L1 & _).
    destruct (Z.eq_dec i e) as [->|Hne].
    - rewrite (tilesS_diag _ (itemS_lt k d) _ _ _ _ Ht) in Hr. exact Hr.
    - exfalso. destruct (tilesS_next _ (itemS_lt k d) _ _ _ _ _ Ht Hne) as (i2 & c2 & Hit & Hle & _).
      destruct (itemS_not_end _ _ _ _ _ _ Hit Hi ltac:(lia)) as [N1 N2]. tauto.
  Qed.

  Lemma rest_ok_item : forall d k ks i c j c', rest_ok d (k :: ks) i c j c' -> ty i <> t_arr_end -> ty i <> t_obj_end ->
    exists i2 c2, itemS k d i i2 c c2 /\ rest_ok d (k :: ks) i2 c2 j c'.
  Proof.
    intros d k ks i c j c' H N1 N2. inversion H as [|d0 k0 ks0 i0 c0 e n c1 j0 c0' Ht He Hr]; subst.
    destruct (Z.eq_dec i e) as [->|Hne]; [exfalso; destruct (end_ty_cases k) as [E|E]; rewrite E in He; tauto|].
    destruct (tilesS_next _ (itemS_lt k d) _ _ _ _ _ Ht Hne) as (i2 & c2 & Hit & Hle & Ht2).
    exists i2, c2. split; [exact Hit|]. eapply rest_cons; eassumption.
  Qed.

  Lemma rest_ok_lt : forall d k ks i c j c', rest_ok d (k :: ks) i c j c' -> i < j.
  Proof.
    intros d k ks i c j c' H. inversion H as [|d0 k0 ks0 i0 c0 e n c1 j0 c0' Ht He Hr]; subst.
    pose proof (tilesS_le _ (itemS_lt k d) _ _ _ _ _ Ht) as [L1 _]. pose proof (rest_ok_le _ _ _ _ _ _ Hr) as (L2 & _). lia.
  Qed.

  Lemma end_ty_range : forall k, 0 <= end_ty k < 256.
  Proof. intros [|]; unfold end_ty, t_obj_end, t_arr_end; lia. Qed.

  Lemma rest_ok_word : forall d k ks i c j c', rest_ok d (k :: ks) i c j c' -> 0 <= i -> j < 2^32 -> 0 <= T i < 2^64.
  Proof.
    intros d k ks i c j c' H Hi Hj. inversion H as [|d0 k0 ks0 i0 c0 e n c1 j0 c0' Ht He Hr]; subst.
    pose proof (rest_ok_le _ _ _ _ _ _ Hr) as (L2 & _).
    destruct (Z.eq_dec i e) as [->|Hne]; [eapply ttype_range; [exact He| apply end_ty_range]|].
    destruct (tilesS_next _ (itemS_lt k d) _ _ _ _ _ Ht Hne) as (i2 & c2 & Hit & Hle & _).
    destruct k; unfold itemS in Hit.
    - destruct Hit as (c1' & Hs & _). destruct (str_rec_ty _ _ _ Hs) as (Hty & _). eapply ttype_range; [exact Hty| unfold t_str; lia].
    - destruct (ser_view_of _ _ _ _ _ Hit Hi ltac:(lia)) as [Hw _ _|Hw _ _|l Hw _ _ _ _|d' e' n' _ Hw _ _ _ _|d' e' n' _ Hw _ _ _ _];
        try (destruct Hw as [Hw|[Hw|Hw]]); (eapply ttype_range; [exact Hw|]);
        unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj; lia.
  Qed.

  Lemma rest_ok_open : forall d ks k i e n c c1 j c',
    tilesS (itemS k d) (i + 1) e n c c1 -> ty e = end_ty k -> rest_ok (Datatypes.S d) ks (e + 1) c1 j c' ->
    rest_ok d (k :: ks) (i + 1) c j c'.
  Proof. intros. eapply rest_cons; eassumption. Qed.
End Ser.
