(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Specs2.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma left_align_value : forall (l : list Z), limbs l -> (1 <= length l)%nat -> nth (length l - 1) l 0 <> 0 ->
  let sh := 64 - num_bits_word (nth (length l - 1) l 0) in
  let r := fst (lshift_limbs l sh 0) in
  0 <= sh < 64 /\ limbs r /\ length r = length l /\ lval r = lval l * 2 ^ sh /\ 2 ^ 63 <= nth (length l - 1) r 0.
Proof.
  intros l Hl Hlen Htop. cbv zeta. set (n := (length l - 1)%nat) in *. set (x := nth n l 0) in *.
  pose proof (limbs_nth l n Hl) as Hx. fold x in Hx. destruct Hx as [Hx0 Hx1].
  destruct (num_bits_word_spec x ltac:(lia)) as (Hb1 & Hb2 & Hb3).
  pose proof (num_bits_word_le x 64 ltac:(lia) ltac:(unfold BW in *; lia)) as Hb4.
  set (bits := num_bits_word x) in *. set (sh := 64 - bits).
  assert (Hsh : 0 <= sh < 64) by (subst sh; lia).
  pose proof (lshift_limbs_spec l sh 0 Hl Hsh ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as Hs.
  destruct (lshift_limbs l sh 0) as [r mo]. cbn [fst]. destruct Hs as (Hr & Hrl & Hmo & Hv).
  (* [comment removed for export] *)
  pose proof (nth_limb_val l n Hl ltac:(lia)) as El. fold x in El.
  rewrite (skipn_all2 l) in El by lia. cbn [lval] in El. rewrite Z.mul_0_r, Z.add_0_r in El.
  pose proof (lval_bound (firstn n l) (limbs_firstn n l Hl)) as Hlo. rewrite firstn_length_le in Hlo by lia.
  pose proof (Bp_pos n) as Hbn.
  assert (E2 : 2 ^ bits * 2 ^ sh = BW).
  { rewrite <- Z.pow_add_r by lia. subst sh. replace (bits + (64 - bits)) with 64 by lia. reflexivity. }
  assert (E3 : 2 ^ (bits - 1) * 2 ^ sh = 2 ^ 63).
  { rewrite <- Z.pow_add_r by lia. subst sh. f_equal. lia. }
  assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (EBl : Bp (length l) = BW * Bp n) by (rewrite <- Bp_S; f_equal; subst n; lia).
  (* [comment removed for export] *)
  assert (Hfit : lval l * 2 ^ sh < Bp (length l)).
  { rewrite EBl, <- E2. assert (lval l < Bp n * 2 ^ bits) by nia. nia. }
  assert (Emo : mo = 0).
  { pose proof (lval_nonneg r Hr). pose proof (Bp_pos (length l)). nia. }
  rewrite Emo, Z.mul_0_r, Z.add_0_r, Z.add_0_r in Hv.
  split; [exact Hsh|]. split; [exact Hr|]. split; [exact Hrl|]. split; [exact Hv|].
  (* [comment removed for export] *)
  pose proof (nth_limb_val r n Hr ltac:(lia)) as Er.
  rewrite (skipn_all2 r) in Er by lia. cbn [lval] in Er. rewrite Z.mul_0_r, Z.add_0_r in Er.
  pose proof (lval_bound (firstn n r) (limbs_firstn n r Hr)) as Hrlo. rewrite firstn_length_le in Hrlo by lia.
  assert (Hge : Bp n * 2 ^ 63 <= lval r).
  { rewrite Hv, <- E3. assert (Bp n * 2 ^ (bits - 1) <= lval l) by nia. nia. }
  destruct (Z.lt_ge_cases (nth n r 0) (2 ^ 63)) as [Hlt|]; [exfalso|assumption].
  assert (Bp n * nth n r 0 <= Bp n * (2 ^ 63 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma bn_left_align_spec : forall r s X (Q : Z -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref r s -> bn_norm (getbn r s) -> (1 <= bn_top (getbn r s))%nat ->
  (forall b' sh, let b := getbn r s in
     0 <= sh < 64 -> bn_ok b' -> bn_top b' = bn_top b -> bn_neg b' = bn_neg b -> bn_flags b' = bn_flags b ->
     bn_mag b' = bn_mag b * 2 ^ sh -> 2 ^ 63 <= nth (bn_top b - 1) (bn_buf b') 0 ->
     st_ok (setbn r b' s) -> own (setbn r b' s) X -> Q sh (setbn r b' s) X) ->
  bwp (bn_left_align ops r) s X Q.
Proof.
  intros r s X Q Hs Ho Hv Hn Htop HQ. unfold bn_left_align. apply bwp_bind, bwp_get.
  set (b := getbn r s) in *. pose proof (st_ok_getbn r s Hs Hv) as Hb. fold b in Hb.
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4). unfold bn_dmax in *.
  set (l := firstn (bn_top b) (bn_buf b)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact Hb1).
  assert (Hll : length l = bn_top b) by (apply firstn_length_le; lia).
  assert (Ent : nth (bn_top b - 1) l 0 = nth (bn_top b - 1) (bn_buf b) 0).
  { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
  destruct Hn as [Hn|Hn]; [lia|].
  pose proof (left_align_value l Hl ltac:(lia) ltac:(rewrite Hll, Ent; exact Hn)) as Hla. cbv zeta in Hla.
  rewrite Hll, Ent in Hla. destruct Hla as (L1 & L2 & L3 & L4 & L5).
  set (sh := 64 - num_bits_word (nth (bn_top b - 1) (bn_buf b) 0)) in *.
  set (rl := fst (lshift_limbs l sh 0)) in *.
  apply bwp_bind.
  set (b' := bn_with_buf b (splice (bn_buf b) 0 rl)).
  assert (Hlen : length (bn_buf b') = length (bn_buf b)) by (subst b'; cbn [bn_with_buf bn_buf]; apply splice_length; lia).
  assert (Hfn : firstn (bn_top b) (bn_buf b') = rl) by (subst b'; cbn [bn_with_buf bn_buf]; apply firstn_splice_0; lia).
  assert (Hb' : bn_ok b').
  { unfold bn_ok, bn_dmax. rewrite Hlen. subst b'. cbn [bn_with_buf bn_buf bn_top bn_flags].
    split; [apply splice_limbs; assumption|]. tauto. }
  apply bwp_update; try assumption; [apply bn_blocks_same; [reflexivity|exact Hlen]|].
  intros Hs' Ho'. apply bwp_ret. apply HQ; try assumption; try reflexivity.
  - unfold bn_mag. change (bn_top b') with (bn_top b). rewrite Hfn. exact L4.
  - assert (E : nth (bn_top b - 1) (bn_buf b') 0 = nth (bn_top b - 1) rl 0).
    { rewrite <- Hfn. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
    rewrite E. exact L5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_lshift_fixed_top_spec : forall rr ra n s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref rr s -> valid_ref ra s -> rr <> ra -> 0 <= n < 64 ->
  Z.of_nat (bn_top (getbn ra s)) + 1 <= DMAX_MAX ->
  (forall r' X', let a := getbn ra s in
     bn_ok r' -> bn_top r' = (bn_top a + 1)%nat -> bn_neg r' = bn_neg a -> bn_flags r' = bn_flags (getbn rr s) ->
     bn_mag r' = bn_mag a * 2 ^ n ->
     st_ok (setbn rr r' s) -> own (setbn rr r' s) X' -> Q tt (setbn rr r' s) X') ->
  bwp (bn_lshift_fixed_top ops rr ra n) s X Q.
Proof.
  intros rr ra n s X Q Hs Ho Hvr Hva Hne Hn Htop HQ. unfold bn_lshift_fixed_top.
  rewrite (bnref_eqb_neq rr ra Hne). destruct (Z.ltb_spec n 64) as [_|]; [|lia]. cbn [negb orb].
  apply bwp_bind, bwp_get. set (a := getbn ra s) in *.
  pose proof (st_ok_getbn ra s Hs Hva) as Ha. fold a in Ha. destruct Ha as (Ha1 & Ha2 & Ha3 & Ha4). unfold bn_dmax in *.
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|lia|].
  intros r1 X1 (E1 & E2 & E3 & E4 & Hr1 & E5 & E6) Hs1 Ho1.
  assert (Hvr1 : valid_ref rr (setbn rr r1 s)) by (apply valid_ref_setbn; exact Hvr).
  apply bwp_bind, bwp_get. rewrite getbn_setbn_same by assumption.
  apply bwp_set. rewrite setbn_setbn_same.
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
  set (l := firstn (bn_top a) (bn_buf a)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact Ha1).
  assert (Hll : length l = bn_top a) by (apply firstn_length_le; lia).
  set (buf' := if (bn_top a =? 0)%nat then upd (bn_buf r1) 0 0
               else let '(ls, mo) := lshift_limbs l n 0 in splice (bn_buf r1) 0 (ls ++ [mo])).
  assert (Hbuf : limbs buf' /\ length buf' = length (bn_buf r1) /\ lval (firstn (bn_top a + 1) buf') = lval l * 2 ^ n).
  { subst buf'. destruct (Nat.eqb_spec (bn_top a) 0) as [E0|E0].
    - split; [apply upd_limbs; [exact R1|exact limb_0]|]. split; [apply upd_length; lia|].
      rewrite E0. cbn [Nat.add]. unfold upd. rewrite firstn_splice_0 by (cbn [length]; lia).
      assert (l = []) by (subst l; rewrite E0; reflexivity). subst l. rewrite H. reflexivity.
    - pose proof (lshift_limbs_spec l n 0 Hl Hn ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as Hsp.
      destruct (lshift_limbs l n 0) as [ls mo]. destruct Hsp as (S1 & S2 & S3 & S4).
      assert (Hseg : limbs (ls ++ [mo])).
      { apply limbs_app; [exact S1|]. constructor; [|constructor]. unfold limb.
        assert (2 ^ n < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). unfold BW. lia. }
      assert (Hsegl : length (ls ++ [mo]) = (bn_top a + 1)%nat) by (rewrite length_app; cbn [length]; lia).
      split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|].
      rewrite firstn_splice_0 by lia. rewrite lval_app. cbn [lval]. rewrite S2. lia. }
  destruct Hbuf as (B1 & B2 & B3).
  set (r2 := mkBN (bn_d r1) buf' (bn_top a + 1) (bn_neg a) (bn_flags r1)).
  assert (Hr2 : bn_ok r2).
  { unfold bn_ok, bn_dmax. subst r2. cbn [bn_buf bn_top bn_flags]. rewrite B2. repeat split; try assumption; lia. }
  apply HQ; try assumption; try reflexivity.
  - rewrite <- (setbn_setbn_same rr r1 r2 s). apply st_ok_setbn; assumption.
  - rewrite <- (setbn_setbn_same rr r1 r2 s). apply own_setbn_same; try assumption.
    rewrite getbn_setbn_same by assumption. apply bn_blocks_same; [reflexivity|exact B2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_rshift_fixed_top_spec : forall rr ra n s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref rr s -> valid_ref ra s -> rr <> ra -> 0 <= n < 64 ->
  (1 <= bn_top (getbn ra s))%nat ->
  (forall r' X', let a := getbn ra s in
     bn_ok r' -> bn_top r' = bn_top a -> bn_neg r' = bn_neg a -> bn_flags r' = bn_flags (getbn rr s) ->
     bn_mag r' = bn_mag a / 2 ^ n ->
     st_ok (setbn rr r' s) -> own (setbn rr r' s) X' -> Q tt (setbn rr r' s) X') ->
  bwp (bn_rshift_fixed_top ops rr ra n) s X Q.
Proof.
  intros rr ra n s X Q Hs Ho Hvr Hva Hne Hn Htop HQ. unfold bn_rshift_fixed_top.
  rewrite (bnref_eqb_neq rr ra Hne). destruct (Z.ltb_spec n 64) as [_|]; [|lia]. cbn [negb orb].
  apply bwp_bind, bwp_get. set (a := getbn ra s) in *.
  pose proof (st_ok_getbn ra s Hs Hva) as Ha. fold a in Ha. destruct Ha as (Ha1 & Ha2 & Ha3 & Ha4). unfold bn_dmax in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [|_]; [lia|].
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|lia|].
  intros r1 X1 (E1 & E2 & E3 & E4 & Hr1 & E5 & E6) Hs1 Ho1.
  assert (Hvr1 : valid_ref rr (setbn rr r1 s)) by (apply valid_ref_setbn; exact Hvr).
  apply bwp_bind, bwp_get. rewrite getbn_setbn_same by assumption.
  apply bwp_set. rewrite setbn_setbn_same.
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
  set (l := firstn (bn_top a) (bn_buf a)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact Ha1).
  assert (Hll : length l = bn_top a) by (apply firstn_length_le; lia).
  destruct (rshift_limbs_spec l n Hl Hn) as (S1 & S2 & S3).
  set (r2 := mkBN (bn_d r1) (splice (bn_buf r1) 0 (rshift_limbs l n)) (bn_top a) (bn_neg a) (bn_flags r1)).
  assert (B2 : length (splice (bn_buf r1) 0 (rshift_limbs l n)) = length (bn_buf r1)) by (apply splice_length; lia).
  assert (Hr2 : bn_ok r2).
  { unfold bn_ok, bn_dmax. subst r2. cbn [bn_buf bn_top bn_flags]. rewrite B2.
    split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia. }
  apply HQ; try assumption; try reflexivity.
  - unfold bn_mag. subst r2. cbn [bn_buf bn_top]. rewrite firstn_splice_0 by lia. exact S3.
  - rewrite <- (setbn_setbn_same rr r1 r2 s). apply st_ok_setbn; assumption.
  - rewrite <- (setbn_setbn_same rr r1 r2 s). apply own_setbn_same; try assumption.
    rewrite getbn_setbn_same by assumption. apply bn_blocks_same; [reflexivity|exact B2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le_bytes_val_bound : forall bs, 0 <= le_bytes_val bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; cbn [le_bytes_val length].
  - cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof (Z.mod_pos_bound b 256 ltac:(lia)). lia.
Qed.

Lemma bytes_to_limbs_spec : forall n bs, limbs (bytes_to_limbs n bs) /\ length (bytes_to_limbs n bs) = n.
Proof.
  induction n as [|n IH]; intros bs; cbn [bytes_to_limbs length]; [split; [constructor|reflexivity]|].
  destruct (IH (skipn 8 bs)) as [H1 H2]. split; [|rewrite H2; reflexivity].
  constructor; [|exact H1]. pose proof (le_bytes_val_bound (firstn 8 bs)) as [Hb0 Hb1].
  assert (Hl : (length (firstn 8 bs) <= 8)%nat) by (rewrite length_firstn; lia).
  assert (256 ^ Z.of_nat (length (firstn 8 bs)) <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
  unfold limb. change BW with (256 ^ 8). lia.
Qed.

Lemma skip_zero_bytes_length : forall bs, (length (skip_zero_bytes bs) <= length bs)%nat.
Proof.
  induction bs as [|b bs IH]; cbn [skip_zero_bytes length]; [lia|].
  destruct b; cbn [length]; lia.
Qed.

Definition MAX_BYTES : Z := 256000.

Lemma BN_bin2bn_spec : forall bytes r s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref r s -> Z.of_nat (length bytes) <= MAX_BYTES ->
  (forall b' X', bn_ok b' -> bn_norm b' -> Z.of_nat (bn_top b') <= 32000 -> bn_flags b' = bn_flags (getbn r s) ->
     st_ok (setbn r b' s) -> own (setbn r b' s) X' -> Q tt (setbn r b' s) X') ->
  bwp (BN_bin2bn ops bytes r) s X Q.
Proof.
  intros bytes r s X Q Hs Ho Hv Hlen HQ. unfold BN_bin2bn. apply bwp_bind, bwp_get.
  set (b := getbn r s) in *. pose proof (st_ok_getbn r s Hs Hv) as Hb. fold b in Hb.
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4).
  destruct bytes as [|x bytes'].
  - (* [comment removed for export] *)
    set (b' := mkBN (bn_d b) (repeat 0 (bn_dmax b)) 0 false (bn_flags b)).
    assert (Hb' : bn_ok b').
    { unfold bn_ok, bn_dmax. subst b'. cbn [bn_buf bn_top bn_flags]. rewrite repeat_length.
      split; [apply limbs_repeat; exact limb_0|]. split; [lia|]. split; assumption. }
    apply bwp_update; try assumption.
    { apply bn_blocks_same; [reflexivity|]. subst b'. cbn [bn_buf]. apply repeat_length. }
    intros Hs' Ho'. apply HQ; try assumption; try reflexivity; try (left; reflexivity); try (cbn; lia).
  - set (bs := skip_zero_bytes (x :: bytes')).
    assert (Hbsl : (length bs <= length (x :: bytes'))%nat) by apply skip_zero_bytes_length.
    destruct bs as [|y bs'] eqn:Ebs.
    + (* [comment removed for export] *)
      assert (Hb' : bn_ok (bn_with_top b 0)).
      { unfold bn_ok, bn_with_top, bn_dmax. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
      apply bwp_update; try assumption; [reflexivity|].
      intros Hs' Ho'. apply HQ; try assumption; try reflexivity; try (left; reflexivity); try (cbn; lia).
    + set (n := ((length (y :: bs') - 1) / 8 + 1)%nat).
      assert (Hn : Z.of_nat n <= 32000).
      { subst n. unfold MAX_BYTES in Hlen. rewrite Nat2Z.inj_add, Nat2Z.inj_div.
        set (len := length (y :: bs')) in *.
        assert (Hl1 : (1 <= len)%nat) by (subst len; cbn [length]; lia).
        rewrite Nat2Z.inj_sub by exact Hl1. change (Z.of_nat 8) with 8. change (Z.of_nat 1) with 1.
        assert (Hx : Z.of_nat len <= 256000) by lia.
        assert ((Z.of_nat len - 1) / 8 < 32000); [|lia].
        apply Z.div_lt_upper_bound; lia. }
      apply bwp_bind. apply bn_wexpand_spec; try assumption; [repeat split; assumption|unfold DMAX_MAX; lia|].
      intros b1 X1 (E1 & E2 & E3 & E4 & Hb1' & E5 & E6) Hs1 Ho1.
      assert (Hv1 : valid_ref r (setbn r b1 s)) by (apply valid_ref_setbn; exact Hv).
      apply bwp_bind, bwp_get. rewrite getbn_setbn_same by assumption.
      apply bwp_set. rewrite setbn_setbn_same.
      destruct (bytes_to_limbs_spec n (rev (y :: bs'))) as [L1 L2].
      destruct Hb1' as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
      set (b2 := mkBN (bn_d b1) (splice (bn_buf b1) 0 (bin2bn_limbs (y :: bs'))) n false (bn_flags b1)).
      assert (B2 : length (bn_buf b2) = length (bn_buf b1)).
      { subst b2. cbn [bn_buf]. apply splice_length. unfold bin2bn_limbs. fold n. lia. }
      assert (Hb2' : bn_ok b2).
      { unfold bn_ok, bn_dmax. rewrite B2. subst b2. cbn [bn_buf bn_top bn_flags].
        split; [apply splice_limbs; [exact R1|unfold bin2bn_limbs; fold n; exact L1]|]. repeat split; try assumption; lia. }
      destruct (bn_correct_top_ok b2 Hb2') as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
      apply HQ; try assumption.
      * apply C2.
      * change (bn_top b2) with n in C4. lia.
      * rewrite <- (setbn_setbn_same r b1 _ s). apply st_ok_setbn; assumption.
      * rewrite <- (setbn_setbn_same r b1 _ s). apply own_setbn_same; try assumption.
        rewrite getbn_setbn_same by assumption. apply bn_blocks_same; [rewrite C6; reflexivity|rewrite C5; exact B2].
Qed.

End Specs2.
