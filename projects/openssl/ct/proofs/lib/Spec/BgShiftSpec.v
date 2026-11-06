(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs BnSpecs2 BnAddSpec BnMulSpec.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BgState BgWords BgLib BgInv BgSpecs BgLibSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ShiftSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_zeros_seg : forall buf nw seg, (nw + length seg <= length buf)%nat ->
  firstn (nw + length seg)
         (if (nw =? 0)%nat then splice buf nw seg else splice (splice buf nw seg) 0 (repeat 0 nw)) = repeat 0 nw ++ seg.
Proof.
  intros buf nw seg H. destruct (Nat.eqb_spec nw 0) as [->|Hnw].
  - cbn [repeat app Nat.add]. apply firstn_splice_0; [reflexivity|lia].
  - unfold splice. cbn [firstn app]. rewrite repeat_length. cbn [Nat.add].
    rewrite skipn_app, firstn_length_le by lia. rewrite Nat.sub_diag. cbn [skipn].
    rewrite (skipn_all2 (firstn nw buf)) by (rewrite firstn_length_le; lia). cbn [app].
    rewrite app_assoc, firstn_app, length_app, repeat_length.
    rewrite firstn_all2 by (rewrite length_app, repeat_length; lia).
    replace (nw + length seg - (nw + length seg))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma zeros_seg_length : forall buf nw seg, (nw + length seg <= length buf)%nat ->
  length (if (nw =? 0)%nat then splice buf nw seg else splice (splice buf nw seg) 0 (repeat 0 nw)) = length buf.
Proof.
  intros buf nw seg H. destruct (Nat.eqb_spec nw 0) as [->|Hnw]; [apply splice_length; lia|].
  rewrite splice_length; [apply splice_length; lia|]. rewrite repeat_length, splice_length by lia. lia.
Qed.

Lemma zeros_seg_limbs : forall buf nw seg, limbs buf -> limbs seg ->
  limbs (if (nw =? 0)%nat then splice buf nw seg else splice (splice buf nw seg) 0 (repeat 0 nw)).
Proof.
  intros buf nw seg Hb Hs. destruct (nw =? 0)%nat; [apply splice_limbs; assumption|].
  apply splice_limbs; [apply splice_limbs; assumption|apply limbs_repeat; exact limb_0].
Qed.

Lemma lval_zeros_app : forall n l, lval (repeat 0 n ++ l) = Bp n * lval l.
Proof. intros n l. rewrite lval_app, lval_repeat0, repeat_length. lia. Qed.

(* [comment removed for export] *)
Lemma operand_after_expand : forall rr ra (s : ST) words r1, st_wf s ->
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat ->
  gexpanded (getbn rr s) words r1 ->
  let a0 := getbn ra s in let a := getbn ra (setbn rr r1 s) in
  bn_top a = bn_top a0 /\ bn_neg a = bn_neg a0 /\ firstn (bn_top a0) (bn_buf a) = firstn (bn_top a0) (bn_buf a0) /\
  bg_okv a.
Proof.
  intros rr ra s words r1 Hs Hr Hn Ha Hex. cbv zeta. destruct (Nat.eq_dec rr ra) as [<-|Hne].
  - rewrite getbn_setbn_same by exact Hr. pose proof (gexpanded_prefix _ _ _ (st_wf_ok rr s Hs Hr Hn) Hex) as Hp.
    destruct Hex as (E1 & E2 & E3 & E4 & Hok & _). repeat split; try assumption; apply bg_ok_okv in Hok; destruct Hok; assumption.
  - rewrite getbn_setbn_other by exact Hne. pose proof (st_wf_okv ra s Hs Ha) as [H1 H2]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_lshift_fixed_top_spec : forall rr ra n F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> 0 <= n ->
  Z.of_nat (bn_top (getbn ra s)) + n / 64 + 1 <= BG_DMAX ->
  hoare F s (bn_lshift_fixed_top ops rr ra n) (upd1 rr s (fun r' =>
     bn_top r' = (bn_top (getbn ra s) + Z.to_nat (n / 64) + 1)%nat /\ bn_neg r' = bn_neg (getbn ra s) /\
     bn_mag r' = bn_mag (getbn ra s) * 2 ^ n)).
Proof.
  intros rr ra n F s Hr Hn Ha Hn0 Hsz. apply hoare_wf. intros Hs. unfold bn_lshift_fixed_top.
  destruct (Z.ltb_spec n 0); [lia|]. set (nw := Z.to_nat (n / 64)). set (lb := n mod 64).
  assert (Hq : 0 <= n / 64) by (apply Z.div_pos; lia).
  assert (Hlb : 0 <= lb < 64) by (apply Z.mod_pos_bound; lia).
  apply hoare_bind_get. set (a0 := getbn ra s) in *.
  eapply hoare_bind; [apply bn_wexpand_spec; [exact Hr|exact Hn|unfold nw; lia]|].
  intros [] s1 Hs1 (r1 & -> & Hr1). apply hoare_bind_get. apply hoare_bind_get.
  rewrite (getbn_setbn_same rr) by exact Hr.
  destruct (operand_after_expand rr ra s _ r1 Hs Hr Hn Ha Hr1) as (A1 & A2 & A3 & A4). fold a0 in A1, A2, A3.
  set (a := getbn ra (setbn rr r1 s)) in *.
  destruct Hr1 as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). pose proof Hok1 as (O1 & O2 & O3 & O4).
  pose proof (st_wf_okv ra s Hs Ha) as [Hal Hat]. fold a0 in Hal, Hat.
  set (src := firstn (bn_top a0) (bn_buf a0)).
  assert (Hsrc : limbs src) by (apply limbs_firstn; exact Hal).
  assert (Hsl : length src = bn_top a0) by (apply firstn_length_le; exact Hat).
  rewrite A1. replace (firstn (bn_top a0) (bn_buf a)) with src by (symmetry; exact A3).
  pose proof (lshift_limbs_spec src lb 0 Hsrc Hlb ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as Hls.
  destruct (lshift_limbs src lb 0) as [ls mo] eqn:Els. destruct Hls as (L1 & L2 & L3 & L4).
  set (seg := ls ++ [mo]).
  assert (Hseg : limbs seg) by (apply limbs_app; [exact L1|constructor; [unfold limb; rewrite BW_pow; split; [lia|]; eapply Z.lt_trans; [apply L3|apply Z.pow_lt_mono_r; lia]|constructor]]).
  assert (Hsegl : length seg = (bn_top a0 + 1)%nat) by (unfold seg; rewrite length_app; cbn [length]; lia).
  (* [comment removed for export] *)
  set (buf0 := if (bn_top a0 =? 0)%nat then upd (bn_buf r1) nw 0 else splice (bn_buf r1) nw seg).
  assert (Ebuf0 : buf0 = splice (bn_buf r1) nw seg).
  { unfold buf0. destruct (Nat.eqb_spec (bn_top a0) 0) as [E0|E0]; [|reflexivity].
    unfold seg. assert (src = []) by (destruct src; [reflexivity|cbn in Hsl; lia]). subst src. rewrite H0 in Els.
    cbn [lshift_limbs] in Els. injection Els as <- <-. reflexivity. }
  rewrite Ebuf0.
  set (buf := if (nw =? 0)%nat then splice (bn_buf r1) nw seg else splice (splice (bn_buf r1) nw seg) 0 (repeat 0 nw)).
  assert (Hfit : (nw + length seg <= length (bn_buf r1))%nat) by (unfold bn_dmax in Hd1; lia).
  assert (Hbl : length buf = length (bn_buf r1)) by (apply zeros_seg_length; exact Hfit).
  assert (Hbf : firstn (nw + length seg) buf = repeat 0 nw ++ seg) by (apply firstn_zeros_seg; exact Hfit).
  eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
  - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. fold buf. rewrite Hbl.
    split; [apply zeros_seg_limbs; assumption|]. split; [unfold bn_dmax in Hd1; lia|split; assumption].
  - rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold bn_mag. cbn [bn_top bn_neg bn_buf]. fold buf.
    split; [reflexivity|]. split; [exact A2|].
    replace (bn_top a0 + nw + 1)%nat with (nw + length seg)%nat by lia. rewrite Hbf, lval_zeros_app.
    assert (EL4 : lval ls + Bp (bn_top a0) * mo = lval src * 2 ^ lb) by (rewrite <- Hsl; lia).
    unfold seg. rewrite lval_app, L2, Hsl. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r.
    rewrite EL4. fold src. rewrite Bp_pow2. unfold nw. rewrite Z2Nat.id by lia.
    assert (En : 2 ^ n = 2 ^ (64 * (n / 64)) * 2 ^ lb).
    { rewrite <- Z.pow_add_r by lia. f_equal. apply Z.div_mod. lia. }
    rewrite En. unfold bn_mag. fold src. lia.
Qed.

Lemma BN_lshift_spec : forall rr ra n F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> 0 <= n ->
  Z.of_nat (bn_top (getbn ra s)) + n / 64 + 1 <= BG_DMAX ->
  hoare F s (BN_lshift ops rr ra n) (upd1 rr s (fun r' =>
     bn_canon r' /\ bn_mag r' = bn_mag (getbn ra s) * 2 ^ n /\
     bn_neg r' = (bn_neg (getbn ra s) && negb (bn_top r' =? 0)%nat) /\
     (bn_top r' <= bn_top (getbn ra s) + Z.to_nat (n / 64) + 1)%nat)).
Proof.
  intros rr ra n F s Hr Hn Ha Hn0 Hsz. unfold BN_lshift. destruct (Z.ltb_spec n 0); [lia|].
  eapply hoare_bind; [apply bn_lshift_fixed_top_spec; assumption|].
  intros [] s1 Hs1 (r1 & -> & T1 & T2 & T3).
  eapply hoare_mono; [apply correct_top_spec; [rewrite length_setbn; exact Hr|exact Hn]|].
  intros [] s2 Hs2 (r2 & -> & ->). rewrite setbn_setbn_same, getbn_setbn_same by exact Hr.
  pose proof (st_wf_ok rr _ Hs1 ltac:(rewrite length_setbn; exact Hr) Hn) as Hok1. rewrite getbn_setbn_same in Hok1 by exact Hr.
  destruct (bg_correct_top_ok r1 Hok1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  eexists. split; [reflexivity|]. rewrite K3, K7, T2, T3. repeat split; try assumption; try apply K2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mag_shift_words : forall (a : BN) nw, bg_okv a -> (nw <= bn_top a)%nat ->
  lval (slice (bn_buf a) nw (bn_top a - nw)) = bn_mag a / Bp nw.
Proof.
  intros a nw (Hl & Ht) Hnw. unfold bn_mag. set (l := firstn (bn_top a) (bn_buf a)).
  assert (Hll : limbs l) by (apply limbs_firstn; exact Hl).
  assert (Hlen : length l = bn_top a) by (apply firstn_length_le; exact Ht).
  rewrite slice_of_firstn by exact Hnw. fold l.
  pose proof (lval_split_le nw l ltac:(lia)) as Hsp.
  pose proof (lval_bound _ (limbs_firstn nw l Hll)) as Hlo. rewrite firstn_length_le in Hlo by lia.
  rewrite Hsp. rewrite Z.mul_comm, Z.div_add by (pose proof (Bp_pos nw); lia). rewrite Z.div_small by exact Hlo. lia.
Qed.

Lemma bn_rshift_fixed_top_spec : forall rr ra n F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> 0 <= n ->
  hoare F s (bn_rshift_fixed_top ops rr ra n) (upd1 rr s (fun r' =>
     bn_top r' = (bn_top (getbn ra s) - Z.to_nat (n / 64))%nat /\
     bn_neg r' = (if (bn_top (getbn ra s) <=? Z.to_nat (n / 64))%nat then false else bn_neg (getbn ra s)) /\
     bn_mag r' = bn_mag (getbn ra s) / 2 ^ n)).
Proof.
  intros rr ra n F s Hr Hn Ha Hn0. apply hoare_wf. intros Hs. unfold bn_rshift_fixed_top.
  destruct (Z.ltb_spec n 0); [lia|]. set (nw := Z.to_nat (n / 64)). set (rb := n mod 64).
  assert (Hq : 0 <= n / 64) by (apply Z.div_pos; lia).
  assert (Hrb : 0 <= rb < 64) by (apply Z.mod_pos_bound; lia).
  assert (E2n : 2 ^ n = Bp nw * 2 ^ rb).
  { rewrite Bp_pow2. unfold nw. rewrite Z2Nat.id by lia. rewrite <- Z.pow_add_r by lia. f_equal.
    pose proof (Z.div_mod n 64 ltac:(lia)). unfold rb. lia. }
  apply hoare_bind_get. set (a0 := getbn ra s) in *.
  pose proof (st_wf_okv ra s Hs Ha) as Hav. fold a0 in Hav. pose proof Hav as [Hal Hat].
  destruct (Nat.leb_spec (bn_top a0) nw) as [Hle|Hgt].
  - eapply hoare_mono; [apply BN_zero_spec; assumption|].
    intros [] s1 _ (r1 & -> & T1 & T2). exists r1. split; [reflexivity|]. rewrite T1. split; [lia|]. split; [exact T2|].
    rewrite (bn_mag_top0 r1 T1). symmetry. apply Z.div_small. split; [apply okv_mag_nonneg; exact Hav|].
    eapply Z.lt_le_trans; [apply okv_mag_lt; exact Hav|]. rewrite E2n.
    pose proof (Bp_mono (bn_top a0) nw Hle). pose proof (Bp_pos nw). assert (0 < 2 ^ rb) by (apply Z.pow_pos_nonneg; lia). nia.
  - set (top := (bn_top a0 - nw)%nat).
    eapply hoare_bind with (R := upd1 rr s (fun r1 => (top <= bn_dmax r1)%nat /\ getbn ra (setbn rr r1 s) = a0)).
    + destruct (Nat.eqb_spec rr ra) as [->|Hne].
      * apply hoare_ret. exists a0. split; [unfold a0; rewrite setbn_getbn_id; reflexivity|].
        split; [unfold top; lia|]. rewrite getbn_setbn_same by exact Hr. reflexivity.
      * eapply hoare_mono; [apply bn_wexpand_spec; [exact Hr|exact Hn|]|].
        -- pose proof (st_wf_top_le ra s Hs Ha). fold a0 in H0. unfold top. lia.
        -- intros [] s1 _ (r1 & -> & Hex). exists r1. split; [reflexivity|].
           destruct Hex as (_ & _ & _ & _ & _ & Hd & _). split; [exact Hd|]. rewrite getbn_setbn_other by exact Hne. reflexivity.
    + intros [] s1 Hs1 (r1 & -> & Hd1 & Ea). apply hoare_bind_get. rewrite Ea. apply hoare_bind_get.
      rewrite getbn_setbn_same by exact Hr.
      pose proof (st_wf_ok rr _ Hs1 ltac:(rewrite length_setbn; exact Hr) Hn) as Hok1. rewrite getbn_setbn_same in Hok1 by exact Hr.
      pose proof Hok1 as (O1 & O2 & O3 & O4).
      set (sl := slice (bn_buf a0) nw top).
      assert (Hsl : limbs sl) by (apply slice_limbs; exact Hal).
      assert (Hsll : length sl = top) by (apply slice_length; unfold top, bn_dmax in *; lia).
      destruct (rshift_limbs_spec sl rb Hsl Hrb) as (R1 & R2 & R3).
      assert (Hlen : length (splice (bn_buf r1) 0 (rshift_limbs sl rb)) = length (bn_buf r1))
        by (apply splice_length; rewrite R2, Hsll; unfold bn_dmax in Hd1; lia).
      eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
      * unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen.
        split; [apply splice_limbs; assumption|]. split; [unfold bn_dmax in Hd1; lia|split; assumption].
      * rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold bn_mag. cbn [bn_top bn_neg bn_buf].
        split; [reflexivity|]. split; [reflexivity|].
        rewrite firstn_splice_0 by (try (rewrite R2, Hsll; reflexivity); unfold bn_dmax in Hd1; lia).
        rewrite R3. unfold sl, top. rewrite mag_shift_words by (try assumption; lia).
        rewrite E2n, Z.div_div by (first [pose proof (Bp_pos nw); lia | apply Z.pow_pos_nonneg; lia]). reflexivity.
Qed.

Lemma BN_rshift_spec : forall rr ra n F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> 0 <= n ->
  hoare F s (BN_rshift ops rr ra n) (upd1 rr s (fun r' =>
     bn_canon r' /\ bn_mag r' = bn_mag (getbn ra s) / 2 ^ n /\
     (bn_neg (getbn ra s) = false -> bn_neg r' = false) /\
     (bn_top r' <= bn_top (getbn ra s))%nat)).
Proof.
  intros rr ra n F s Hr Hn Ha Hn0. unfold BN_rshift. destruct (Z.ltb_spec n 0); [lia|].
  eapply hoare_bind; [apply bn_rshift_fixed_top_spec; assumption|].
  intros [] s1 Hs1 (r1 & -> & T1 & T2 & T3).
  eapply hoare_mono; [apply correct_top_spec; [rewrite length_setbn; exact Hr|exact Hn]|].
  intros [] s2 Hs2 (r2 & -> & ->). rewrite setbn_setbn_same, getbn_setbn_same by exact Hr.
  pose proof (st_wf_ok rr _ Hs1 ltac:(rewrite length_setbn; exact Hr) Hn) as Hok1. rewrite getbn_setbn_same in Hok1 by exact Hr.
  destruct (bg_correct_top_ok r1 Hok1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  eexists. split; [reflexivity|]. rewrite K3, K7, T3. split; [exact K2|]. split; [reflexivity|]. split; [|lia].
  intros Hneg. rewrite T2, Hneg. destruct (bn_top (getbn ra s) <=? Z.to_nat (n / 64))%nat; reflexivity.
Qed.

End ShiftSpec.
