(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnDivLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma top_limb_le : forall X V k, limbs X -> limbs V -> length X = S k -> length V = S k -> lval X < lval V ->
  nth k X 0 <= nth k V 0.
Proof.
  intros X V k HX HV LX LV H.
  pose proof (nth_limb_val X k HX ltac:(lia)) as EX. pose proof (nth_limb_val V k HV ltac:(lia)) as EV.
  rewrite (skipn_all2 X) in EX by lia. rewrite (skipn_all2 V) in EV by lia. cbn [lval] in EX, EV.
  pose proof (lval_bound (firstn k V) (limbs_firstn k V HV)) as BV. rewrite firstn_length_le in BV by lia.
  pose proof (lval_nonneg (firstn k X) (limbs_firstn k X HX)) as BX.
  pose proof (Bp_pos k) as Bk.
  assert (Bp k * nth k X 0 < Bp k * (nth k V 0 + 1)) by lia.
  apply Z.mul_lt_mono_pos_l in H0; lia.
Qed.

Lemma div_inv_n0 : forall sdiv div_n loop num_n N0 Ls Lt Lr i snum tmp res,
  limbs sdiv -> (1 <= div_n)%nat -> (div_n <= length sdiv)%nat -> num_n = (loop + div_n)%nat -> (i < loop)%nat -> (num_n <= Ls)%nat ->
  div_inv sdiv div_n loop num_n N0 Ls Lt Lr i (snum, tmp, res) ->
  nth div_n (slice snum (loop - 1 - i) (div_n + 1)) 0 <= nth (div_n - 1) sdiv 0.
Proof.
  intros sdiv div_n loop num_n N0 Ls Lt Lr i snum tmp res Hsd Hdn Hsdl Hnum Hi HLs (Hsn & Hsnl & _ & _ & _ & _ & Htop & _).
  rewrite nth_slice by lia.
  pose proof (top_limb_le (slice snum (loop - i) div_n) (firstn div_n sdiv) (div_n - 1)) as T.
  rewrite nth_slice in T by lia. rewrite nth_firstn in T.
  destruct (Nat.ltb_spec (div_n - 1) div_n) as [_|]; [|lia].
  replace (loop - i + (div_n - 1))%nat with (loop - 1 - i + div_n)%nat in T by lia.
  apply T.
  - apply slice_limbs. exact Hsn.
  - apply limbs_firstn. exact Hsd.
  - rewrite slice_length by lia. lia.
  - rewrite firstn_length_le by lia. lia.
  - exact Htop.
Qed.

Lemma div_step_split : forall sdiv div_n loop num_n d0 d1 i snum tmp res,
  (1 <= div_n)%nat -> (div_n <= length sdiv)%nat -> num_n = (loop + div_n)%nat -> (i < loop)%nat ->
  (num_n <= length snum)%nat -> (div_n + 1 <= length tmp)%nat -> (loop <= length res)%nat ->
  limbs sdiv -> limbs snum -> d0 = nth (div_n - 1) sdiv 0 -> d1 = (if (div_n =? 1)%nat then 0 else nth (div_n - 2) sdiv 0) ->
  2 ^ 63 <= d0 -> lval (slice snum (loop - i) div_n) < lval (firstn div_n sdiv) ->
  let w := (loop - 1 - i)%nat in
  let V := firstn div_n sdiv in
  let WIN := slice snum w (div_n + 1) in
  let SC := step_core V d0 d1 WIN in
  div_step sdiv div_n loop num_n d0 d1 i (snum, tmp, res) =
  (firstn w snum ++ fst (fst (fst SC)) ++ skipn (w + (div_n + 1)) snum,
   (snd (fst SC) ++ skipn (length V) (snd (fst (fst SC)))) ++ skipn (div_n + 1) tmp,
   firstn w res ++ [snd SC] ++ skipn (w + 1) res)
  /\ length (fst (fst (fst SC))) = (div_n + 1)%nat
  /\ length (snd (fst SC) ++ skipn (length V) (snd (fst (fst SC)))) = (div_n + 1)%nat.
Proof.
  intros sdiv div_n loop num_n d0 d1 i snum tmp res Hdn Hsdl Hnum Hi HLs HLt HLr Hsd Hsn Hd0 Hd1 Hnorm Htop w V WIN SC.
  rewrite div_step_eq by assumption. fold w. fold V. fold WIN. fold SC.
  assert (HVl : length V = div_n) by (subst V; apply firstn_length_le; lia).
  assert (HVlimbs : limbs V) by (subst V; apply limbs_firstn; exact Hsd).
  assert (HVd0 : d0 = nth (length V - 1) V 0).
  { rewrite HVl, Hd0. subst V. rewrite nth_firstn. destruct (Nat.ltb_spec (div_n - 1) div_n); [reflexivity|lia]. }
  assert (HVd1 : d1 = if (length V =? 1)%nat then 0 else nth (length V - 2) V 0).
  { rewrite HVl, Hd1. destruct (Nat.eqb_spec div_n 1); [reflexivity|]. subst V. rewrite nth_firstn.
    destruct (Nat.ltb_spec (div_n - 2) div_n); [reflexivity|lia]. }
  assert (Hwl : length WIN = S div_n) by (subst WIN; rewrite slice_length; lia).
  assert (Hwin : limbs WIN) by (subst WIN; apply slice_limbs; exact Hsn).
  assert (Hu : lval WIN < lval V * BW).
  { pose proof BW_pos as BWp.
    assert (Ewin : lval WIN = nth w snum 0 + BW * lval (slice snum (loop - i) div_n)).
    { subst WIN. replace (div_n + 1)%nat with (1 + div_n)%nat by lia. rewrite <- slice_app_slice, lval_app.
      rewrite slice_length by lia. rewrite Bp_1. replace (w + 1)%nat with (loop - i)%nat by lia.
      assert (E : slice snum w 1 = [nth w snum 0]).
      { apply list_eq_nth; [rewrite slice_length; cbn [length]; lia|]. intros j Hj. rewrite slice_length in Hj by lia.
        assert (j = 0)%nat by lia. subst j. rewrite nth_slice by lia. cbn [nth]. f_equal. lia. }
      rewrite E. cbn [lval]. lia. }
    pose proof (limbs_nth snum w Hsn) as [_ Hx]. rewrite Ewin. fold V in Htop.
    assert (BW * lval (slice snum (loop - i) div_n) <= BW * (lval V - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  pose proof (step_core_spec V d0 d1 HVlimbs ltac:(lia) HVd0 HVd1 Hnorm WIN Hwin ltac:(lia) Hu) as Hc.
  fold SC in Hc. destruct SC as [[[win' t1] t2] q]. cbn [fst snd].
  destruct Hc as (Hw' & Hw'l & _ & _ & _ & _ & Ht1 & Ht1l & Ht2 & Ht2l). rewrite HVl in *.
  assert (L2 : length (t2 ++ skipn div_n t1) = (div_n + 1)%nat) by (rewrite length_app, length_skipn; lia).
  split; [|split; [lia | exact L2]].
  f_equal. f_equal.
  - unfold splice. rewrite Hw'l. replace (w + S div_n)%nat with (w + (div_n + 1))%nat by lia. reflexivity.
  - rewrite splice_splice_same by lia. unfold splice. cbn [firstn Nat.add app]. rewrite Ht2l, L2. reflexivity.
Qed.
