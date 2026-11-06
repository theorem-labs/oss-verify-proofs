(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel BnDivCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition step_core (V : list Z) (d0 d1 : Z) (win : list Z) : list Z * list Z * list Z * Z :=
  let div_n := length V in
  let n0 := nth div_n win 0 in
  let n1 := nth (div_n - 1) win 0 in
  let n2 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) win 0 in
  let q := div_qhat n0 n1 n2 d0 d1 in
  let '(ml, l0) := mul_words V q in
  let '(sl, bw) := sub_words win (ml ++ [l0]) in
  let q' := subw q bw in
  let msk := map (fun x => Z.land x (negw bw)) V in
  let '(al, cy) := add_words (firstn div_n sl) msk in
  (al ++ [addw (nth div_n sl 0) cy], ml ++ [l0], msk, q').

Lemma land_mask_0 : forall x, Z.land x (negw 0) = 0.
Proof. intros x. unfold negw. rewrite Z.sub_0_r, Z.mod_0_l by (unfold BW; lia). apply Z.land_0_r. Qed.

Lemma land_mask_1 : forall x, limb x -> Z.land x (negw 1) = x.
Proof.
  intros x Hx. unfold negw. replace ((0 - 1) mod BW) with (Z.ones 64) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.

Lemma map_mask_0 : forall V, map (fun x => Z.land x (negw 0)) V = repeat 0 (length V).
Proof. induction V as [|x V IH]; cbn [map repeat length]; [reflexivity|]. rewrite land_mask_0, IH. reflexivity. Qed.

Lemma map_mask_1 : forall V, limbs V -> map (fun x => Z.land x (negw 1)) V = V.
Proof.
  induction V as [|x V IH]; intros H; cbn [map]; [reflexivity|].
  apply limbs_cons_inv in H. destruct H as [Hx HV]. rewrite land_mask_1 by exact Hx. rewrite IH by exact HV. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma top3_bounds : forall l n, limbs l -> length l = S (S (S n)) ->
  let U3 := (nth (S (S n)) l 0 * BW + nth (S n) l 0) * BW + nth n l 0 in
  U3 * Bp n <= lval l < (U3 + 1) * Bp n.
Proof.
  intros l n Hl Hlen U3.
  pose proof (lval_split_le n l ltac:(lia)) as E.
  pose proof (lval_bound (firstn n l) (limbs_firstn n l Hl)) as Hb. rewrite firstn_length_le in Hb by lia.
  assert (Es : skipn n l = [nth n l 0; nth (S n) l 0; nth (S (S n)) l 0]).
  { apply list_eq_nth; [rewrite length_skipn; cbn [length]; lia|]. intros i Hi. rewrite length_skipn in Hi.
    rewrite nth_skipn. assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; cbn [nth]; f_equal; lia. }
  rewrite Es in E. cbn [lval] in E. subst U3. pose proof (Bp_pos n). nia.
Qed.

Lemma top2_bounds : forall l n, limbs l -> length l = S (S n) ->
  let V2 := nth (S n) l 0 * BW + nth n l 0 in
  V2 * Bp n <= lval l < (V2 + 1) * Bp n.
Proof.
  intros l n Hl Hlen V2.
  pose proof (lval_split_le n l ltac:(lia)) as E.
  pose proof (lval_bound (firstn n l) (limbs_firstn n l Hl)) as Hb. rewrite firstn_length_le in Hb by lia.
  assert (Es : skipn n l = [nth n l 0; nth (S n) l 0]).
  { apply list_eq_nth; [rewrite length_skipn; cbn [length]; lia|]. intros i Hi. rewrite length_skipn in Hi.
    rewrite nth_skipn. assert (i = 0 \/ i = 1)%nat as [->| ->] by lia; cbn [nth]; f_equal; lia. }
  rewrite Es in E. cbn [lval] in E. subst V2. pose proof (Bp_pos n). nia.
Qed.

Section Core.
Variable V : list Z.
Variables d0 d1 : Z.
Hypothesis HV : limbs V.
Let div_n := length V.
Hypothesis Hdn : (1 <= div_n)%nat.
Hypothesis Hd0 : d0 = nth (div_n - 1) V 0.
Hypothesis Hd1 : d1 = if (div_n =? 1)%nat then 0 else nth (div_n - 2) V 0.
Hypothesis Hnorm : 2 ^ 63 <= d0.
Let v := lval V.

Lemma core_v_bounds : Bp (div_n - 1) * 2 ^ 63 <= v < Bp div_n.
Proof.
  subst v. pose proof (lval_bound V HV) as Hb. fold div_n in Hb. split; [|lia].
  pose proof (nth_limb_val V (div_n - 1) HV ltac:(lia)) as E.
  pose proof (lval_nonneg _ (limbs_firstn (div_n - 1) V HV)).
  pose proof (lval_nonneg _ (limbs_skipn (S (div_n - 1)) V HV)).
  pose proof (Bp_pos (div_n - 1)). pose proof (Bp_pos (S (div_n - 1))). rewrite <- Hd0 in E. nia.
Qed.

Theorem step_core_spec : forall win, limbs win -> length win = S div_n -> lval win < v * BW ->
  let '(win', t1, t2, q) := step_core V d0 d1 win in
  limbs win' /\ length win' = S div_n /\ lval win' = lval win mod v /\ nth div_n win' 0 = 0 /\
  q = lval win / v /\ limb q /\
  limbs t1 /\ length t1 = S div_n /\ limbs t2 /\ length t2 = div_n.
Proof.
  intros win Hwin Hlen Hu. pose proof BW_pos as BWp. pose proof core_v_bounds as Hvb.
  assert (Hvpos : 0 < v) by (pose proof (Bp_pos (div_n - 1)); nia).
  set (u := lval win) in *.
  assert (Hu0 : 0 <= u) by (apply lval_nonneg; exact Hwin).
  unfold step_core. fold div_n.
  set (n0 := nth div_n win 0). set (n1 := nth (div_n - 1) win 0).
  set (n2 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) win 0).
  assert (Hd0l : limb d0) by (rewrite Hd0; apply limbs_nth; exact HV).
  assert (Hd1l : limb d1) by (rewrite Hd1; destruct (div_n =? 1)%nat; [exact limb_0|apply limbs_nth; exact HV]).
  assert (Hn0 : limb n0) by (apply limbs_nth; exact Hwin).
  assert (Hn1 : limb n1) by (apply limbs_nth; exact Hwin).
  assert (Hn2 : limb n2) by (subst n2; destruct (div_n =? 1)%nat; [exact limb_0|apply limbs_nth; exact Hwin]).
  (* [comment removed for export] *)
  assert (Hq : 0 <= div_qhat n0 n1 n2 d0 d1 < BW /\ u / v <= div_qhat n0 n1 n2 d0 d1 <= u / v + 1).
  { destruct (Nat.eqb_spec div_n 1) as [E1|E1].
    - (* [comment removed for export] *)
      assert (EV : V = [d0]).
      { apply list_eq_nth; [cbn [length]; fold div_n; lia|]. intros i Hi. fold div_n in Hi.
        assert (i = 0)%nat by lia. subst i. rewrite Hd0, E1. reflexivity. }
      assert (Ewin : win = [n1; n0]).
      { apply list_eq_nth; [cbn [length]; lia|]. intros i Hi.
        assert (i = 0 \/ i = 1)%nat as [->| ->] by lia; subst n0 n1; rewrite E1; reflexivity. }
      assert (Ev : v = d0) by (subst v; rewrite EV; cbn [lval]; lia).
      assert (Eu : u = n1 + BW * n0) by (subst u; rewrite Ewin; cbn [lval]; lia).
      pose proof (div_qhat_spec d0 d1 n0 n1 n2 ltac:(unfold limb in *; lia) Hd1l Hn0 Hn1 Hn2 (u * BW) (v * BW) 1 ltac:(lia)) as Hs.
      rewrite Z.div_mul_cancel_r in Hs by lia.
      assert (En2 : n2 = 0) by reflexivity.
      apply Hs; rewrite ?Eu, ?Ev, ?Hd1, ?En2 in *; try lia.
      assert ((n1 + BW * n0) * BW < d0 * BW * BW); [|lia].
      apply Z.mul_lt_mono_pos_r; lia.
    - (* [comment removed for export] *)
      destruct (Nat.eqb_spec div_n 1) as [|_]; [lia|].
      pose proof (top3_bounds win (div_n - 2) Hwin ltac:(lia)) as H3. cbv zeta in H3.
      replace (S (S (div_n - 2))) with div_n in H3 by lia. replace (S (div_n - 2)) with (div_n - 1)%nat in H3 by lia.
      pose proof (top2_bounds V (div_n - 2) HV ltac:(fold div_n; lia)) as H2. cbv zeta in H2.
      replace (S (div_n - 2)) with (div_n - 1)%nat in H2 by lia.
      rewrite <- Hd0 in H2. assert (Ed1 : d1 = nth (div_n - 2) V 0).
      { rewrite Hd1. destruct (Nat.eqb_spec div_n 1); [lia|reflexivity]. }
      rewrite <- Ed1 in H2.
      apply (div_qhat_spec d0 d1 n0 n1 n2 ltac:(unfold limb in *; lia) Hd1l Hn0 Hn1 Hn2 u v (Bp (div_n - 2)));
        [pose proof (Bp_pos (div_n - 2)); lia|exact H3|exact H2|exact Hu]. }
  destruct Hq as [Hql Hq]. set (q := div_qhat n0 n1 n2 d0 d1) in *.
  (* [comment removed for export] *)
  pose proof (mul_words_spec V q HV Hql) as Hm. destruct (mul_words V q) as [ml l0].
  destruct Hm as (Hml & Hmll & Hl0 & Hmv). fold div_n in Hmll, Hmv. fold v in Hmv.
  assert (HP : limbs (ml ++ [l0])) by (apply limbs_app; [exact Hml|constructor; [exact Hl0|constructor]]).
  assert (HPl : length (ml ++ [l0]) = S div_n) by (rewrite length_app; cbn [length]; lia).
  assert (HPv : lval (ml ++ [l0]) = v * q) by (rewrite lval_app; cbn [lval]; rewrite Hmll; lia).
  (* [comment removed for export] *)
  pose proof (sub_words_spec win (ml ++ [l0]) Hwin HP ltac:(lia)) as Hs.
  destruct (sub_words win (ml ++ [l0])) as [sl bw]. destruct Hs as (Hsl & Hsll & Hbw & Hsv).
  rewrite Hlen in Hsll, Hsv. rewrite HPv in Hsv. fold u in Hsv.
  pose proof (lval_bound sl Hsl) as Hslb. rewrite Hsll in Hslb.
  pose proof (Z.div_mod u v ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound u v Hvpos) as Hmb.
  assert (HvB : v < Bp (S div_n)) by (rewrite Bp_S; pose proof (Bp_pos div_n); nia).
  (* [comment removed for export] *)
  assert (Hbwq : q = u / v + bw).
  { assert (bw = 0 \/ bw = 1) as [->| ->] by lia.
    - assert (q = u / v \/ q = u / v + 1) as [E|E] by lia; [lia|exfalso]. rewrite E in Hsv. nia.
    - assert (q = u / v \/ q = u / v + 1) as [E|E] by lia; [exfalso|lia]. rewrite E in Hsv. nia. }
  assert (Eq' : subw q bw = u / v).
  { unfold subw. rewrite Hbwq. replace (u / v + bw - bw) with (u / v) by ring. apply Z.mod_small.
    split; [apply Z.div_pos; lia|lia]. }
  (* [comment removed for export] *)
  set (msk := map (fun x => Z.land x (negw bw)) V).
  assert (Hmsk : limbs msk /\ length msk = div_n /\ lval msk = bw * v).
  { subst msk. assert (bw = 0 \/ bw = 1) as [->| ->] by lia.
    - rewrite map_mask_0. fold div_n. rewrite lval_repeat0, repeat_length.
      split; [apply limbs_repeat; exact limb_0|]. split; lia.
    - rewrite map_mask_1 by exact HV. split; [exact HV|]. split; [reflexivity|]. fold v. lia. }
  destruct Hmsk as (Hmk & Hmkl & Hmkv).
  pose proof (add_words_spec (firstn div_n sl) msk (limbs_firstn _ _ Hsl) Hmk
                ltac:(rewrite firstn_length_le by lia; lia)) as Ha.
  destruct (add_words (firstn div_n sl) msk) as [al cy]. destruct Ha as (Hal & Hall & Hcy & Hav).
  rewrite firstn_length_le in Hall, Hav by lia. rewrite Hmkv in Hav.
  pose proof (lval_bound al Hal) as Halb. rewrite Hall in Halb.
  pose proof (nth_limb_val sl div_n Hsl ltac:(lia)) as Esl.
  rewrite (skipn_all2 sl) in Esl by lia. cbn [lval] in Esl. rewrite Z.mul_0_r, Z.add_0_r in Esl.
  set (st := nth div_n sl 0) in *. assert (Hst : limb st) by (apply limbs_nth; exact Hsl).
  (* [comment removed for export] *)
  assert (Hfin : addw st cy = 0 /\ lval al = u mod v).
  { unfold addw. pose proof (Bp_pos div_n) as Hbp. rewrite Bp_S in *.
    assert (bw = 0 \/ bw = 1) as [Eb|Eb] by lia; rewrite Eb in *.
    - (* [comment removed for export] *)
      assert (lval sl = u mod v) by lia.
      assert (Est0 : st = 0) by (unfold limb in *; nia).
      assert (Hcy0 : cy = 0) by nia. rewrite Est0, Hcy0 in *. split; [reflexivity|lia].
    - assert (Ev1 : lval sl + v = u mod v + BW * Bp div_n) by lia.
      assert (Ecs : st + cy = BW) by (unfold limb in *; nia).
      rewrite Ecs, Z.mod_same by lia. split; [reflexivity|]. nia. }
  destruct Hfin as [Etop Eal]. rewrite Etop.
  assert (Hw' : limbs (al ++ [0])) by (apply limbs_app; [exact Hal|constructor; [exact limb_0|constructor]]).
  repeat split.
  - exact Hw'.
  - rewrite length_app; cbn [length]; lia.
  - rewrite lval_app. cbn [lval]. lia.
  - rewrite app_nth2 by lia. rewrite Hall, Nat.sub_diag. reflexivity.
  - exact Eq'.
  - rewrite Eq'. apply Z.div_pos; lia.
  - rewrite Eq'. lia.
  - exact HP.
  - exact HPl.
  - exact Hmk.
  - exact Hmkl.
Qed.

End Core.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_step_eq : forall sdiv div_n loop num_n d0 d1 i snum tmp res,
  (1 <= div_n)%nat -> (div_n <= length sdiv)%nat -> num_n = (loop + div_n)%nat -> (i < loop)%nat ->
  (num_n <= length snum)%nat -> (div_n + 1 <= length tmp)%nat -> (loop <= length res)%nat ->
  let w := (loop - 1 - i)%nat in
  div_step sdiv div_n loop num_n d0 d1 i (snum, tmp, res) =
  let '(win', t1, t2, q) := step_core (firstn div_n sdiv) d0 d1 (slice snum w (div_n + 1)) in
  (splice snum w win', splice (splice tmp 0 t1) 0 t2, upd res w q).
Proof.
  intros sdiv div_n loop num_n d0 d1 i snum tmp res Hdn Hsd Hnum Hi Hsn Htmp Hres w.
  unfold div_step, step_core. fold w. rewrite firstn_length_le by lia.
  assert (Etop : (num_n - 1 - i = w + div_n)%nat) by lia. rewrite Etop.
  rewrite (nth_slice snum w (div_n + 1) div_n) by lia.
  rewrite (nth_slice snum w (div_n + 1) (div_n - 1)) by lia.
  replace (w + div_n - 1)%nat with (w + (div_n - 1))%nat by lia.
  assert (En2 : (if (div_n =? 1)%nat then 0 else nth (w + div_n - 2) snum 0) =
                (if (div_n =? 1)%nat then 0 else nth (div_n - 2) (slice snum w (div_n + 1)) 0)).
  { destruct (Nat.eqb_spec div_n 1); [reflexivity|]. rewrite nth_slice by lia. f_equal. lia. }
  rewrite En2. clear En2.
  set (q := div_qhat _ _ _ d0 d1).
  pose proof (mul_words_length (firstn div_n sdiv) q) as Hml. rewrite firstn_length_le in Hml by lia.
  destruct (mul_words (firstn div_n sdiv) q) as [ml l0]. cbn [fst] in Hml.
  assert (HPl : length (ml ++ [l0]) = (div_n + 1)%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite <- HPl at 2. rewrite slice_splice_same by lia.
  set (win := slice snum w (div_n + 1)).
  assert (Hwl : length win = (div_n + 1)%nat) by (subst win; apply slice_length; lia).
  pose proof (sub_words_length win (ml ++ [l0])) as Hsl. rewrite Hwl, HPl, Nat.min_id in Hsl.
  destruct (sub_words win (ml ++ [l0])) as [sl bw]. cbn [fst] in Hsl.
  set (msk := map (fun x => Z.land x (negw bw)) (firstn div_n sdiv)).
  assert (Hmskl : length msk = div_n) by (subst msk; rewrite length_map, firstn_length_le; lia).
  (* [comment removed for export] *)
  assert (E1 : slice (splice snum w sl) w div_n = firstn div_n sl).
  { rewrite <- (firstn_slice _ w (length sl) div_n) by lia. rewrite slice_splice_same by lia. reflexivity. }
  rewrite E1.
  assert (E2 : slice (splice (splice tmp 0 (ml ++ [l0])) 0 msk) 0 div_n = msk).
  { pose proof (slice_splice_same (splice tmp 0 (ml ++ [l0])) 0 msk ltac:(rewrite splice_length; lia)) as Hx.
    rewrite Hmskl in Hx. exact Hx. }
  rewrite E2.
  pose proof (add_words_length (firstn div_n sl) msk) as Hal. rewrite firstn_length_le, Hmskl, Nat.min_id in Hal by lia.
  destruct (add_words (firstn div_n sl) msk) as [al cy]. cbn [fst] in Hal.
  f_equal. f_equal.
  rewrite splice_splice_same by lia. rewrite Hal.
  assert (Esk : skipn div_n sl = [nth div_n sl 0]).
  { apply list_eq_nth; [rewrite length_skipn; cbn [length]; lia|]. intros j Hj. rewrite length_skipn in Hj.
    assert (j = 0)%nat by lia. subst j. rewrite nth_skipn. cbn [nth]. f_equal. lia. }
  rewrite Esk.
  assert (Ent : nth (w + div_n) (splice snum w (al ++ [nth div_n sl 0])) 0 = nth div_n sl 0).
  { rewrite nth_splice by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length].
    destruct (Nat.leb_spec w (w + div_n)); [|lia]. destruct (Nat.ltb_spec (w + div_n) (w + (length al + 1))); [|lia].
    cbn [andb]. replace (w + div_n - w)%nat with div_n by lia. rewrite app_nth2 by lia. rewrite Hal, Nat.sub_diag. reflexivity. }
  rewrite Ent. rewrite upd_splice by (rewrite length_app; cbn [length]; lia).
  f_equal. unfold upd, splice. rewrite firstn_app, Hal, Nat.sub_diag, firstn_all2 by lia. cbn [firstn length].
  rewrite app_nil_r. rewrite skipn_all2 by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
Variable sdiv : list Z.
Variables div_n loop num_n : nat.
Variables d0 d1 : Z.
Hypothesis Hsdiv : limbs sdiv.
Hypothesis Hdn : (1 <= div_n)%nat.
Hypothesis Hsdl : (div_n <= length sdiv)%nat.
Hypothesis Hnum : num_n = (loop + div_n)%nat.
Hypothesis Hd0 : d0 = nth (div_n - 1) sdiv 0.
Hypothesis Hd1 : d1 = if (div_n =? 1)%nat then 0 else nth (div_n - 2) sdiv 0.
Hypothesis Hnorm : 2 ^ 63 <= d0.

Let V := firstn div_n sdiv.
Let v := lval V.

(* [comment removed for export] *)
Definition div_inv (N0 : Z) (Ls Lt Lr : nat) (i : nat) (st : list Z * list Z * list Z) : Prop :=
  let '(snum, tmp, res) := st in
  limbs snum /\ length snum = Ls /\ limbs tmp /\ length tmp = Lt /\ limbs res /\ length res = Lr /\
  lval (slice snum (loop - i) div_n) < v /\
  lval (firstn (num_n - i) snum) + v * Bp (loop - i) * lval (slice res (loop - i) i) = N0.

Lemma div_step_inv : forall N0 Ls Lt Lr i st,
  (num_n <= Ls)%nat -> (div_n + 1 <= Lt)%nat -> (loop <= Lr)%nat -> (i < loop)%nat ->
  div_inv N0 Ls Lt Lr i st -> div_inv N0 Ls Lt Lr (S i) (div_step sdiv div_n loop num_n d0 d1 i st).
Proof.
  intros N0 Ls Lt Lr i [[snum tmp] res] HLs HLt HLr Hi (Hsn & Hsnl & Htm & Html & Hrs & Hrsl & Htop & Hval).
  pose proof BW_pos as BWp.
  assert (HVl : length V = div_n) by (subst V; apply firstn_length_le; lia).
  assert (HVlimbs : limbs V) by (subst V; apply limbs_firstn; exact Hsdiv).
  assert (HVd0 : d0 = nth (length V - 1) V 0).
  { rewrite HVl, Hd0. subst V. rewrite nth_firstn. destruct (Nat.ltb_spec (div_n - 1) div_n); [reflexivity|lia]. }
  assert (HVd1 : d1 = if (length V =? 1)%nat then 0 else nth (length V - 2) V 0).
  { rewrite HVl, Hd1. destruct (Nat.eqb_spec div_n 1); [reflexivity|]. subst V. rewrite nth_firstn.
    destruct (Nat.ltb_spec (div_n - 2) div_n); [reflexivity|lia]. }
  rewrite div_step_eq by lia.
  set (w := (loop - 1 - i)%nat). set (win := slice snum w (div_n + 1)).
  assert (Hwl : length win = S div_n) by (subst win; rewrite slice_length; lia).
  assert (Hwin : limbs win) by (subst win; apply slice_limbs; exact Hsn).
  (* [comment removed for export] *)
  assert (Ewin : lval win = nth w snum 0 + BW * lval (slice snum (loop - i) div_n)).
  { subst win. replace (div_n + 1)%nat with (1 + div_n)%nat by lia. rewrite <- slice_app_slice, lval_app.
    rewrite slice_length by lia. rewrite Bp_1. replace (w + 1)%nat with (loop - i)%nat by lia.
    assert (E : slice snum w 1 = [nth w snum 0]).
    { apply list_eq_nth; [rewrite slice_length; cbn [length]; lia|]. intros j Hj. rewrite slice_length in Hj by lia.
      assert (j = 0)%nat by lia. subst j. rewrite nth_slice by lia. cbn [nth]. f_equal. lia. }
    rewrite E. cbn [lval]. lia. }
  assert (Hu : lval win < v * BW).
  { pose proof (limbs_nth snum w Hsn) as [_ Hx].
    assert (BW * lval (slice snum (loop - i) div_n) <= BW * (v - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  pose proof (step_core_spec V d0 d1 HVlimbs ltac:(lia) HVd0 HVd1 Hnorm win Hwin ltac:(lia) Hu) as Hc.
  rewrite HVl in Hc. fold v in Hc. fold V. fold win.
  destruct (step_core V d0 d1 win) as [[[win' t1] t2] q].
  destruct Hc as (Hw' & Hw'l & Hw'v & Hw'top & Hq & Hql & Ht1 & Ht1l & Ht2 & Ht2l).
  unfold div_inv.
  assert (Hvpos : 0 < v).
  { pose proof (lval_nonneg win Hwin). destruct (Z.le_gt_cases v 0); [|lia]. exfalso.
    assert (v * BW <= 0) by (apply Z.mul_nonpos_nonneg; lia). lia. }
  pose proof (Z.div_mod (lval win) v ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound (lval win) v Hvpos) as Hmb.
  (* [comment removed for export] *)
  assert (Ew'v : lval (firstn div_n win') = lval win mod v).
  { pose proof (nth_limb_val win' div_n Hw' ltac:(lia)) as E. rewrite Hw'top in E.
    rewrite (skipn_all2 win') in E by lia. cbn [lval] in E. rewrite !Z.mul_0_r, !Z.add_0_r in E. lia. }
  split; [apply splice_limbs; assumption|]. split; [rewrite splice_length; lia|].
  split; [apply splice_limbs; [apply splice_limbs|]; assumption|].
  split; [rewrite !splice_length; rewrite ?splice_length; lia|].
  split; [apply upd_limbs; assumption|]. split; [rewrite upd_length; lia|].
  replace (loop - S i)%nat with w by lia. replace (num_n - S i)%nat with (w + div_n)%nat by lia.
  assert (Es : slice (splice snum w win') w div_n = firstn div_n win').
  { rewrite <- (firstn_slice _ w (length win') div_n) by lia. rewrite slice_splice_same by lia. reflexivity. }
  split; [rewrite Es; lia|].
  (* [comment removed for export] *)
  assert (Ef' : lval (firstn (w + div_n) (splice snum w win')) = lval (firstn w snum) + Bp w * (lval win mod v)).
  { rewrite firstn_add, lval_app, firstn_splice_below by lia. rewrite firstn_length_le by lia.
    change (firstn div_n (skipn w (splice snum w win'))) with (slice (splice snum w win') w div_n).
    rewrite Es, Ew'v. reflexivity. }
  assert (Ef : lval (firstn (num_n - i) snum) = lval (firstn w snum) + Bp w * lval win).
  { replace (num_n - i)%nat with (w + (div_n + 1))%nat by lia. rewrite firstn_add, lval_app.
    rewrite firstn_length_le by lia. reflexivity. }
  assert (Er : lval (slice (upd res w q) w (S i)) = q + BW * lval (slice res (loop - i) i)).
  { replace (S i) with (1 + i)%nat by lia. rewrite <- slice_app_slice, lval_app.
    rewrite slice_length by (rewrite upd_length; lia). rewrite Bp_1.
    assert (E1 : slice (upd res w q) w 1 = [q]).
    { unfold upd. change 1%nat with (length [q]). apply slice_splice_same. cbn [length]. lia. }
    assert (E2 : slice (upd res w q) (w + 1) i = slice res (loop - i) i).
    { unfold upd. rewrite slice_splice_above by (cbn [length]; lia). f_equal. lia. }
    rewrite E1, E2. cbn [lval]. lia. }
  rewrite Ef', Er. rewrite Ef in Hval. replace (loop - i)%nat with (S w) in Hval by lia.
  rewrite Bp_S in Hval. rewrite <- Hval. rewrite Hq.
  replace (slice res (loop - i) i) with (slice res (S w) i) by (f_equal; lia).
  set (qa := lval win / v) in *. set (ma := lval win mod v) in *. rewrite Edm. ring.
Qed.

Lemma div_loop_inv : forall N0 Ls Lt Lr cnt i st,
  (num_n <= Ls)%nat -> (div_n + 1 <= Lt)%nat -> (loop <= Lr)%nat -> (i + cnt <= loop)%nat ->
  div_inv N0 Ls Lt Lr i st ->
  div_inv N0 Ls Lt Lr (i + cnt) (div_loop sdiv div_n loop num_n d0 d1 cnt i st).
Proof.
  intros N0 Ls Lt Lr cnt. induction cnt as [|c IH]; intros i st HLs HLt HLr Hic Hinv; cbn [div_loop].
  - rewrite Nat.add_0_r. exact Hinv.
  - replace (i + S c)%nat with (S i + c)%nat by lia. apply IH; try lia.
    apply div_step_inv; try lia. exact Hinv.
Qed.

(* [comment removed for export] *)
Theorem div_loop_spec : forall snum tmp res,
  limbs snum -> limbs tmp -> limbs res ->
  (num_n <= length snum)%nat -> (div_n + 1 <= length tmp)%nat -> (loop <= length res)%nat ->
  lval (slice snum loop div_n) < v ->
  let N0 := lval (firstn num_n snum) in
  let '(snum', tmp', res') := div_loop sdiv div_n loop num_n d0 d1 loop 0 (snum, tmp, res) in
  limbs snum' /\ length snum' = length snum /\ limbs tmp' /\ length tmp' = length tmp /\
  limbs res' /\ length res' = length res /\
  lval (firstn loop res') = N0 / v /\ lval (firstn div_n snum') = N0 mod v /\ 0 < v.
Proof.
  intros snum tmp res Hsn Htm Hrs HLs HLt HLr Htop N0.
  assert (Hinv0 : div_inv N0 (length snum) (length tmp) (length res) 0 (snum, tmp, res)).
  { unfold div_inv. rewrite !Nat.sub_0_r. repeat split; try assumption; try reflexivity.
    unfold slice at 1. cbn [firstn lval]. subst N0. lia. }
  pose proof (div_loop_inv N0 _ _ _ loop 0 _ HLs HLt HLr ltac:(lia) Hinv0) as H. cbn [Nat.add] in H.
  destruct (div_loop sdiv div_n loop num_n d0 d1 loop 0 (snum, tmp, res)) as [[snum' tmp'] res'].
  unfold div_inv in H. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  rewrite Nat.sub_diag in H7, H8. replace (num_n - loop)%nat with div_n in H8 by lia.
  rewrite Bp_0, Z.mul_1_r in H8. rewrite slice_0 in H7, H8.
  assert (Hr0 : 0 <= lval (firstn div_n snum')) by (apply lval_nonneg, limbs_firstn; exact H1).
  assert (Hvpos : 0 < v) by lia.
  repeat split; try assumption.
  - apply Z.div_unique with (lval (firstn div_n snum')); [left; lia|lia].
  - apply Z.mod_unique with (lval (firstn loop res')); [left; lia|lia].
Qed.

End Loop.
