(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnWordsCorrect BgWords BgSqrCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mont_carry_step : forall v0 carry old, 0 <= v0 < BW -> (carry = 0 \/ carry = 1) -> 0 <= old < BW ->
  let v := addw (addw v0 carry) old in
  v = (v0 + carry + old) mod BW /\
  (if v <? old then 1 else if v =? old then carry else 0) = (v0 + carry + old) / BW.
Proof.
  intros v0 carry old Hv Hc Ho. cbv zeta. unfold addw. rewrite Zplus_mod_idemp_l. split; [reflexivity|].
  set (sum := v0 + carry + old). assert (Hs : 0 <= sum < 2 * BW) by (unfold sum; lia).
  destruct (Z.lt_ge_cases sum BW) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. rewrite (Z.div_small sum BW) by lia.
    destruct (Z.ltb_spec sum old); [unfold sum in *; lia|]. destruct (Z.eqb_spec sum old); [unfold sum in *; lia|reflexivity].
  - assert (Em : sum mod BW = sum - BW) by (symmetry; apply (Z.mod_unique sum BW 1 (sum - BW)); lia).
    assert (Ed : sum / BW = 1) by (symmetry; apply (Z.div_unique sum BW 1 (sum - BW)); lia).
    rewrite Em, Ed. destruct (Z.ltb_spec (sum - BW) old); [reflexivity|].
    destruct (Z.eqb_spec (sum - BW) old); unfold sum in *; lia.
Qed.

Lemma firstn_upd_last' : forall buf t v, (t < length buf)%nat -> firstn (t + 1) (upd buf t v) = firstn t buf ++ [v].
Proof.
  intros buf t v H. unfold upd, splice. cbn [length]. rewrite firstn_app, firstn_length_le by lia.
  rewrite (firstn_all2 (firstn t buf)) by (rewrite firstn_length_le; lia).
  replace (t + 1 - t)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma mul_add_words_head : forall r a w, r <> [] -> a <> [] ->
  nth 0 (fst (mul_add_words r a w)) 0 = (nth 0 a 0 * w + nth 0 r 0) mod BW.
Proof.
  intros [|y r] [|x a] w Hr Ha; try contradiction. unfold mul_add_words. cbn [mul_add_words_c].
  destruct (mul_add_words_c r a w ((x * w + y + 0) / BW)) as [o c]. cbn [fst nth]. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma select_words_zero : forall a r, limbs r -> length a = length r -> select_words 0 a r = r.
Proof.
  induction a as [|x a IH]; intros [|y r] Hr Hl; cbn [length] in Hl; try discriminate; [reflexivity|].
  apply limbs_cons_inv in Hr. destruct Hr as [[Hy0 Hy1] Hr]. cbn [select_words]. rewrite IH by (try assumption; lia).
  f_equal. rewrite Z.land_0_l, Z.lor_0_l, Z.sub_0_r. rewrite Z.land_comm. change (BW - 1) with (Z.ones 64). rewrite Z.land_ones by lia.
  apply Z.mod_small. rewrite <- BW_pow. lia.
Qed.

Lemma select_words_ones : forall a r, limbs a -> length a = length r -> select_words (BW - 1) a r = a.
Proof.
  induction a as [|x a IH]; intros [|y r] Ha Hl; cbn [length] in Hl; try discriminate; [reflexivity|].
  apply limbs_cons_inv in Ha. destruct Ha as [[Hx0 Hx1] Ha]. cbn [select_words]. rewrite IH by (try assumption; lia).
  f_equal. replace (BW - 1 - (BW - 1)) with 0 by lia. rewrite Z.land_0_l, Z.lor_0_r. rewrite Z.land_comm.
  change (BW - 1) with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. rewrite <- BW_pow. lia.
Qed.

Section MontLoop.
Variable np : list Z.
Variable n0 : Z.
Variable rp0 : list Z.
Hypothesis Hnp : limbs np.
Let nl := length np.
Hypothesis Hnl : (1 <= nl)%nat.
Hypothesis Hn0 : 0 <= n0 < BW.
Hypothesis Hinv : (n0 * nth 0 np 0 + 1) mod BW = 0.
Hypothesis Hrp0 : limbs rp0.
Hypothesis Hlen0 : (2 * nl <= length rp0)%nat.
Let N := lval np.

Definition mont_inv (i : nat) (rp : list Z) (carry : Z) : Prop :=
  limbs rp /\ length rp = length rp0 /\ (carry = 0 \/ carry = 1) /\
  firstn i rp = repeat 0 i /\ skipn (i + nl) rp = skipn (i + nl) rp0 /\
  exists W, 0 <= W < Bp i /\ lval (firstn (i + nl) rp) + carry * Bp (i + nl) = lval (firstn (i + nl) rp0) + N * W.

Lemma mont_round : forall i rp carry, (i < nl)%nat -> mont_inv i rp carry ->
  let w := mulw (nth i rp 0) n0 in
  let '(seg, v) := mul_add_words (slice rp i nl) np w in
  let rp1 := splice rp i seg in
  let old := nth (i + nl) rp1 0 in
  let v' := addw (addw v carry) old in
  let carry' := if v' <? old then 1 else if v' =? old then carry else 0 in
  mont_inv (S i) (upd rp1 (i + nl) v') carry'.
Proof.
  intros i rp carry Hi (R1 & R2 & R3 & R4 & R5 & W & HW & HV). cbv zeta.
  set (x := nth i rp 0). set (w := mulw x n0).
  assert (Hx : 0 <= x < BW) by (apply limbs_nth; exact R1).
  assert (Hw : limb w) by apply mulw_limb.
  assert (Hwin : limbs (slice rp i nl) /\ length (slice rp i nl) = nl) by (split; [apply slice_limbs; exact R1|apply slice_length; lia]).
  destruct Hwin as [Hwl Hwlen].
  pose proof (mul_add_words_spec (slice rp i nl) np w Hwl Hnp ltac:(fold nl; lia) Hw) as Hm.
  pose proof (mul_add_words_head (slice rp i nl) np w ltac:(intros E; rewrite E in Hwlen; cbn in Hwlen; lia)
                ltac:(intros E; unfold nl in Hnl; rewrite E in Hnl; cbn in Hnl; lia)) as Hhead.
  destruct (mul_add_words (slice rp i nl) np w) as [seg v]. cbn [fst] in Hhead.
  destruct Hm as (M1 & M2 & M3 & M4). fold nl in M2, M4. fold N in M4.
  set (rp1 := splice rp i seg).
  assert (L1 : length rp1 = length rp) by (unfold rp1; apply splice_length; lia).
  assert (Hl1 : limbs rp1) by (unfold rp1; apply splice_limbs; assumption).
  assert (Eold : nth (i + nl) rp1 0 = nth (i + nl) rp0 0).
  { unfold rp1. rewrite nth_splice_above by lia.
    pose proof (f_equal (fun l => nth 0 l 0) R5) as E. cbn beta in E. rewrite !nth_skipn in E. rewrite !Nat.add_0_r in E. exact E. }
  set (old := nth (i + nl) rp1 0) in *.
  assert (Hold : 0 <= old < BW) by (apply limbs_nth; exact Hl1).
  destruct (mont_carry_step v carry old M3 R3 Hold) as [Ev Ec]. cbv zeta in Ev, Ec.
  set (v' := addw (addw v carry) old) in *. rewrite Ec.
  set (sum := v + carry + old) in *.
  assert (Hsum : 0 <= sum < 2 * BW) by (unfold sum; destruct M3; lia).
  assert (Hv' : limb v') by apply addw_limb.
  assert (Hc' : sum / BW = 0 \/ sum / BW = 1).
  { assert (0 <= sum / BW < 2) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia. }
  set (rp2 := upd rp1 (i + nl) v').
  assert (L2 : length rp2 = length rp1) by (unfold rp2; apply upd_length; lia).

  assert (Hpre : firstn (S i + nl) rp2 = firstn i rp ++ seg ++ [v']).
  { replace (S i + nl)%nat with ((i + nl) + 1)%nat by lia. unfold rp2. rewrite firstn_upd_last' by lia.
    unfold rp1. replace (i + nl)%nat with (i + length seg)%nat by lia. rewrite firstn_splice_end by lia. rewrite <- app_assoc. reflexivity. }
  split; [unfold rp2; apply upd_limbs; assumption|]. split; [lia|]. split; [exact Hc'|]. split; [|split].
  -
    assert (Es0 : nth 0 seg 0 = 0).
    { rewrite Hhead. unfold slice. rewrite nth_firstn. destruct (Nat.ltb_spec 0 nl); [|lia]. rewrite nth_skipn, Nat.add_0_r. fold x.
      unfold w, mulw. rewrite Zplus_mod, Zmult_mod_idemp_r, <- Zplus_mod.
      replace (nth 0 np 0 * (x * n0) + x) with (x * (n0 * nth 0 np 0 + 1)) by ring.
      rewrite <- Zmult_mod_idemp_r. rewrite Hinv, Z.mul_0_r. reflexivity. }
    assert (Ef : firstn (S i) rp2 = firstn (S i) (firstn (S i + nl) rp2)) by (rewrite firstn_firstn; f_equal; lia).
    rewrite Ef, Hpre. rewrite firstn_app, firstn_length_le by lia. rewrite (firstn_all2 (firstn i rp)) by (rewrite firstn_length_le; lia).
    replace (S i - i)%nat with 1%nat by lia. rewrite R4.
    destruct seg as [|s0 seg']; [cbn in M2; lia|]. cbn [nth] in Es0. subst s0. cbn [app firstn].
    replace (S i) with (i + 1)%nat by lia. rewrite repeat_app. reflexivity.
  - unfold rp2, upd. rewrite skipn_splice_above by (cbn [length]; lia). unfold rp1. rewrite skipn_splice_above by lia.
    replace (S i + nl)%nat with (1 + (i + nl))%nat by lia. rewrite <- (skipn_skipn 1 (i + nl) rp), <- (skipn_skipn 1 (i + nl) rp0). rewrite R5. reflexivity.
  - exists (W + Bp i * w). split.
    + rewrite Bp_S. destruct Hw. pose proof (Bp_pos i). nia.
    + rewrite Hpre. rewrite !lval_app, firstn_length_le, M2 by lia. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r.

      assert (Eo : lval (firstn (i + nl) rp) = lval (firstn i rp) + Bp i * lval (slice rp i nl)).
      { rewrite firstn_add, lval_app, firstn_length_le by lia. reflexivity. }
      assert (Eo0 : lval (firstn (S i + nl) rp0) = lval (firstn (i + nl) rp0) + Bp (i + nl) * old).
      { replace (S i + nl)%nat with ((i + nl) + 1)%nat by lia. rewrite firstn_add, lval_app, firstn_length_le by lia.
        f_equal. f_equal. rewrite Eold.
        destruct (skipn (i + nl) rp0) as [|y t] eqn:Es.
        - exfalso. assert (length (skipn (i + nl) rp0) = 0%nat) by (rewrite Es; reflexivity). rewrite length_skipn in H. lia.
        - cbn [firstn lval]. rewrite Z.mul_0_r, Z.add_0_r.
          rewrite <- (firstn_skipn (i + nl) rp0) at 1. rewrite Es, app_nth2 by (rewrite firstn_length_le; lia).
          rewrite firstn_length_le by lia. rewrite Nat.sub_diag. reflexivity. }
      rewrite Eo0. rewrite Eo in HV.
      pose proof (Z.div_mod sum BW ltac:(unfold BW; lia)) as Hdm. rewrite <- Ev in Hdm.
      replace (S i + nl)%nat with (S (i + nl)) by lia. rewrite Bp_S. rewrite (Bp_add i nl) in *.
      assert (E1 : Bp i * lval seg = Bp i * (N * w) + Bp i * lval (slice rp i nl) - Bp i * Bp nl * v) by nia.
      assert (E2 : Bp i * Bp nl * v' + sum / BW * (BW * (Bp i * Bp nl)) = Bp i * Bp nl * sum) by nia.
      assert (E3 : Bp i * Bp nl * sum = Bp i * Bp nl * v + Bp i * Bp nl * carry + Bp i * Bp nl * old) by (unfold sum; ring).
      lia.
Qed.

Lemma mont_reduce_loop_inv : forall cnt i rp carry, (i + cnt = nl)%nat -> mont_inv i rp carry ->
  let '(rp', carry') := mont_reduce_loop np n0 nl cnt i rp carry in mont_inv nl rp' carry'.
Proof.
  induction cnt as [|c IH]; intros i rp carry Hc Hinv'; cbn [mont_reduce_loop].
  - replace nl with i by lia. exact Hinv'.
  - pose proof (mont_round i rp carry ltac:(lia) Hinv') as Hr. cbv zeta in Hr.
    destruct (mul_add_words (slice rp i nl) np (mulw (nth i rp 0) n0)) as [seg v].
    apply IH; [lia|exact Hr].
Qed.

Theorem mont_reduce_loop_spec :
  let '(rp', carry) := mont_reduce_loop np n0 nl nl 0 rp0 0 in
  limbs rp' /\ length rp' = length rp0 /\ (carry = 0 \/ carry = 1) /\
  firstn nl rp' = repeat 0 nl /\ skipn (2 * nl) rp' = skipn (2 * nl) rp0 /\
  exists W, 0 <= W < Bp nl /\ (lval (slice rp' nl nl) + carry * Bp nl) * Bp nl = lval (firstn (2 * nl) rp0) + N * W.
Proof.
  assert (H0 : mont_inv 0 rp0 0).
  { split; [exact Hrp0|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists 0. rewrite Bp_0. split; [lia|]. lia. }
  pose proof (mont_reduce_loop_inv nl 0 rp0 0 ltac:(lia) H0) as H.
  destruct (mont_reduce_loop np n0 nl nl 0 rp0 0) as [rp' carry].
  destruct H as (R1 & R2 & R3 & R4 & R5 & W & HW & HV).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [replace (2 * nl)%nat with (nl + nl)%nat by lia; exact R5|].
  exists W. split; [exact HW|]. replace (2 * nl)%nat with (nl + nl)%nat by lia. rewrite <- HV.
  rewrite firstn_add, lval_app, firstn_length_le by lia. rewrite R4, lval_repeat0. fold (slice rp' nl nl).
  rewrite (Bp_add nl nl). ring.
Qed.

End MontLoop.

Lemma mont_final_spec : forall ap np carry, limbs ap -> limbs np -> length ap = length np -> (carry = 0 \/ carry = 1) ->
  lval ap + carry * Bp (length np) < 2 * lval np ->
  let res := mont_final ap np carry in
  limbs res /\ length res = length np /\
  lval res = (if lval np <=? lval ap + carry * Bp (length np) then lval ap + carry * Bp (length np) - lval np else lval ap) /\
  0 <= lval res < lval np.
Proof.
  intros ap np carry Ha Hn Hl Hc Hlt. cbv zeta. unfold mont_final.
  pose proof (sub_words_spec ap np Ha Hn Hl) as Hs. destruct (sub_words ap np) as [res borrow].
  destruct Hs as (S1 & S2 & S3 & S4). rewrite Hl in S2, S4.
  pose proof (lval_bound ap Ha) as Bap. rewrite Hl in Bap. pose proof (lval_bound np Hn) as Bnp.
  pose proof (lval_bound res S1) as Bres. rewrite S2 in Bres. pose proof (Bp_pos (length np)) as HR.
  assert (Hb : borrow = 0 \/ borrow = 1) by lia.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; rewrite ?Z.mul_0_l, ?Z.mul_1_l, ?Z.add_0_r in *.
  -
    replace (subw 0 0) with 0 by reflexivity. rewrite select_words_zero by (try assumption; lia).
    destruct (Z.leb_spec (lval np) (lval ap)); repeat split; try assumption; lia.
  -
    replace (subw 0 1) with (BW - 1) by reflexivity. rewrite select_words_ones by (try assumption; lia).
    destruct (Z.leb_spec (lval np) (lval ap)); repeat split; try assumption; lia.
  -
    exfalso. lia.
  -
    replace (subw 1 1) with 0 by reflexivity. rewrite select_words_zero by (try assumption; lia).
    destruct (Z.leb_spec (lval np) (lval ap + Bp (length np))); repeat split; try assumption; lia.
Qed.

Lemma lval_map_compl : forall l, limbs l -> lval (map (fun y => BW - 1 - y) l) = Bp (length l) - 1 - lval l /\ limbs (map (fun y => BW - 1 - y) l).
Proof.
  induction l as [|x l IH]; intros Hl.
  - cbn [map lval length]. rewrite Bp_0. split; [lia|constructor].
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. destruct (IH Hl) as [I1 I2]. cbn [map lval length]. rewrite Bp_S, I1.
    split; [lia|]. constructor; [unfold limb; lia|exact I2].
Qed.

Definition neg_limbs_pure (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: l' => negw x :: map (fun y => BW - 1 - y) l'
  end.

Lemma neg_limbs_spec : forall l, limbs l -> nth 0 l 0 <> 0 ->
  limbs (neg_limbs_pure l) /\ length (neg_limbs_pure l) = length l /\ lval (neg_limbs_pure l) = Bp (length l) - lval l.
Proof.
  intros [|x l] Hl Hx; [cbn in Hx; contradiction|]. cbn [nth] in Hx.
  apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. destruct (lval_map_compl l Hl) as [I1 I2].
  unfold neg_limbs_pure. cbn [lval length]. rewrite length_map, Bp_S, I1.
  assert (En : negw x = BW - x) by (unfold negw; symmetry; apply (Z.mod_unique (0 - x) BW (-1) (BW - x)); lia).
  rewrite En. split; [constructor; [unfold limb; lia|exact I2]|]. split; [reflexivity|lia].
Qed.
