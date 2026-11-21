(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState DeflateLz DeflateInvHash DeflateSetters.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel DeflFastModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition chain_inv (Ins : Z -> Prop) (str ws : Z) (prev : arr) : Prop :=
  (forall p, Ins p -> 0 <= p < str)
  /\ (forall p, Ins p -> str - ws < p -> arr_get prev (p mod ws) = 0 \/ Ins (arr_get prev (p mod ws))).

Lemma hc_chain : forall Ins str ws head prev hs, hc_inv Ins str ws head prev hs -> chain_inv Ins str ws prev.
Proof. intros Ins str ws head prev hs (H1 & _ & H3). split; assumption. Qed.

Lemma chain_set_slot : forall Ins str ws prev v, 0 < ws ->
  chain_inv Ins str ws prev -> chain_inv Ins str ws (arr_set prev (str mod ws) v).
Proof.
  intros Ins str ws prev v Hws (H1 & H3). split; [exact H1|].
  intros p Hp Hq. pose proof (H1 p Hp).
  assert (Hne : str mod ws <> p mod ws).
  { intros E. assert (D : (str - p) mod ws = 0).
    { rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
    apply Z.mod_divide in D; [|lia]. destruct D as [k Hk].
    assert (0 < k) by nia. assert (k < 1) by nia. lia. }
  rewrite arr_get_set_other by exact Hne. exact (H3 p Hp Hq).
Qed.


Lemma lm_body_facts : forall s cur ch bl nice limit se1 se s' b' se1' se' cur' ch' cont,
  longest_match_body s cur ch bl nice limit se1 se = (s', b', se1', se', cur', ch', cont) ->
  ds_prev s' = ds_prev s /\ ds_w_mask s' = ds_w_mask s
  /\ (cont = true -> cur' = arr_get (ds_prev s) (Z.land cur (ds_w_mask s)) /\ limit < cur')
  /\ ((b' = bl /\ s' = s) \/ (bl < b' /\ b' <= MAX_MATCH /\ s' = set_match_start s cur)).
Proof.
  intros s cur ch bl nice limit se1 se s' b' se1' se' cur' ch' cont E. unfold longest_match_body in E.
  set (len := MAX_MATCH - (ds_strstart s + MAX_MATCH - lm_cmp_loop 33 (ds_window s) (ds_strstart s + 2) (cur + 2) (ds_strstart s + MAX_MATCH))) in E.
  assert (Hlen : len <= MAX_MATCH).
  { subst len. pose proof (lm_cmp_loop_bound 33 (ds_window s) (ds_strstart s + 2) (cur + 2) (ds_strstart s + MAX_MATCH)
      ltac:(unfold MAX_MATCH; lia) ltac:(unfold MAX_MATCH; replace (ds_strstart s + 258 - (ds_strstart s + 2)) with 256 by lia; reflexivity)). lia. }
  assert (K : forall (s1 : deflate_state) (b1 x1 x2 : Z),
             ds_prev s1 = ds_prev s -> ds_w_mask s1 = ds_w_mask s ->
             ((b1 = bl /\ s1 = s) \/ (bl < b1 /\ b1 <= MAX_MATCH /\ s1 = set_match_start s cur)) ->
             (let cur'' := arr_get (ds_prev s1) (Z.land cur (ds_w_mask s1)) in
              if limit <? cur''
              then (let chain_length := wrap32 (ch - 1) in
                    if negb (chain_length =? 0) then (s1, b1, x1, x2, cur'', chain_length, true)
                    else (s1, b1, x1, x2, cur'', chain_length, false))
              else (s1, b1, x1, x2, cur'', ch, false)) = (s', b', se1', se', cur', ch', cont) ->
             ds_prev s' = ds_prev s /\ ds_w_mask s' = ds_w_mask s
             /\ (cont = true -> cur' = arr_get (ds_prev s) (Z.land cur (ds_w_mask s)) /\ limit < cur')
             /\ ((b' = bl /\ s' = s) \/ (bl < b' /\ b' <= MAX_MATCH /\ s' = set_match_start s cur))).
  { intros s1 b1 x1 x2 P1 P2 HB E1. cbv zeta in E1. rewrite P1, P2 in E1.
    destruct (Z.ltb_spec limit (arr_get (ds_prev s) (Z.land cur (ds_w_mask s)))) as [L|L].
    - destruct (negb (wrap32 (ch - 1) =? 0)); injection E1 as <- <- _ _ <- _ <-; rewrite P1, P2; (split; [reflexivity|]); (split; [reflexivity|]);
        (split; [| exact HB]); [intros _; split; [reflexivity | exact L] | intros X; discriminate X].
    - injection E1 as <- <- _ _ <- _ <-. rewrite P1, P2. split; [reflexivity|]. split; [reflexivity|]. split; [intros X; discriminate X | exact HB]. }
  match type of E with context [if ?c then _ else _] => destruct c end.
  - cbv beta iota zeta in E. exact (K s bl se1 se eq_refl eq_refl ltac:(left; split; reflexivity) E).
  - destruct (Z.ltb_spec bl len) as [Lb|Lb].
    + destruct (nice <=? len).
      * cbv beta iota zeta in E. injection E as <- <- _ _ <- _ <-. split; [reflexivity|]. split; [reflexivity|].
        split; [intros X; discriminate X|]. right. split; [exact Lb|]. split; [exact Hlen | reflexivity].
      * cbv beta iota zeta in E. exact (K (set_match_start s cur) len _ _ eq_refl eq_refl ltac:(right; split; [exact Lb|]; split; [exact Hlen | reflexivity]) E).
    + cbv beta iota zeta in E. exact (K s bl se1 se eq_refl eq_refl ltac:(left; split; reflexivity) E).
Qed.

Lemma lm_loop_facts : forall Ins str ws f s cur ch bl nice limit se1 se,
  chain_inv Ins str ws (ds_prev s) ->
  (forall p, Z.land p (ds_w_mask s) = p mod ws) ->
  0 <= limit -> str - ws < limit -> Ins cur -> limit <= cur ->
  Forall (fun c => Ins c /\ limit <= c) (lm_curs f s cur ch bl nice limit se1 se)
  /\ let '(s', b') := longest_match_loop f s cur ch bl nice limit se1 se in
     exists v, s' = set_match_start s v /\ bl <= b'
               /\ ((b' = bl /\ v = ds_match_start s) \/ (bl < b' /\ b' <= MAX_MATCH /\ Ins v /\ limit <= v)).
Proof.
  intros Ins str ws f. induction f as [|f IH]; intros s cur ch bl nice limit se1 se HC Hm Hl0 Hlim Hcur Hcl; cbn [lm_curs longest_match_loop].
  - split; [constructor; [split; assumption | constructor]|]. exists (ds_match_start s). rewrite set_ms_self. split; [reflexivity|]. split; [lia|]. left. split; reflexivity.
  - destruct (longest_match_body s cur ch bl nice limit se1 se) as [[[[[[s' b'] se1'] se'] cur'] ch'] cont] eqn:E.
    destruct (lm_body_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (P1 & P2 & Hc & HB).
    assert (HB' : exists v0, s' = set_match_start s v0 /\ bl <= b' /\ ((b' = bl /\ v0 = ds_match_start s) \/ (bl < b' /\ b' <= MAX_MATCH /\ Ins v0 /\ limit <= v0))).
    { destruct HB as [[-> ->] | (Lb & Mb & ->)].
      - exists (ds_match_start s). rewrite set_ms_self. split; [reflexivity|]. split; [lia|]. left. split; reflexivity.
      - exists cur. split; [reflexivity|]. split; [lia|]. right. repeat split; assumption. }
    destruct cont.
    + destruct (Hc eq_refl) as [Ecur Hlt].
      pose proof HC as (H1 & H3).
      assert (Icur' : Ins cur').
      { destruct (H3 cur Hcur ltac:(lia)) as [Z0 | I]; [exfalso; rewrite Hm in Ecur; rewrite Z0 in Ecur; pose proof (H1 cur Hcur); lia|].
        rewrite Ecur, Hm. exact I. }
      destruct (IH s' cur' ch' b' nice limit se1' se' ltac:(rewrite P1; exact HC) ltac:(intros p; rewrite P2; apply Hm) Hl0 Hlim Icur' ltac:(lia)) as [HF HL].
      split; [constructor; [split; assumption | exact HF]|].
      destruct (longest_match_loop f s' cur' ch' b' nice limit se1' se') as [s'' b''].
      destruct HL as (v & Es'' & Lb & Alt). destruct HB' as (v0 & Es' & Lb0 & Alt0).
      destruct Alt as [[Eb Ev] | (L1 & M1 & I1 & C1)].
      * exists v0. rewrite Es'', Ev, set_ms_self. split; [exact Es'|]. split; [lia|]. rewrite Eb. exact Alt0.
      * exists v. rewrite Es'', Es', set_ms_twice. split; [reflexivity|]. split; [lia|]. right. repeat split; try assumption. lia.
    + split; [constructor; [split; assumption | constructor]|]. exact HB'.
Qed.


Definition lm_limit (s : deflate_state) : Z :=
  if ds_w_size s - MIN_LOOKAHEAD <? ds_strstart s then ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) else NIL.

Record lm_ctx (Ins : Z -> Prop) (s : deflate_state) (cur : Z) : Prop := MkLMCTX {
  lc_chain : chain_inv Ins (ds_strstart s) (ds_w_size s) (ds_prev s);
  lc_mask : ds_w_mask s = ds_w_size s - 1;
  lc_pow : exists k, 0 <= k /\ ds_w_size s = 2 ^ k;
  lc_ws : MIN_LOOKAHEAD < ds_w_size s;
  lc_cur : Ins cur;
  lc_nz : cur <> 0;
  lc_dist : ds_strstart s - cur <= ds_w_size s - MIN_LOOKAHEAD }.

Lemma lm_mask_mod : forall Ins s cur, lm_ctx Ins s cur -> forall p, Z.land p (ds_w_mask s) = p mod ds_w_size s.
Proof.
  intros Ins s cur C p. destruct (lc_pow _ _ _ C) as (k & Hk & E). rewrite (lc_mask _ _ _ C), E.
  replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). apply Z.land_ones. exact Hk.
Qed.

Lemma lm_limit_facts : forall Ins s cur, lm_ctx Ins s cur ->
  0 <= lm_limit s /\ ds_strstart s - ds_w_size s < lm_limit s /\ lm_limit s <= cur
  /\ ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) <= lm_limit s.
Proof.
  intros Ins s cur C. pose proof (lc_ws _ _ _ C). pose proof (lc_dist _ _ _ C). pose proof (proj1 (lc_chain _ _ _ C) cur (lc_cur _ _ _ C)).
  unfold lm_limit, NIL, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
  destruct (Z.ltb_spec (ds_w_size s - (258 + 3 + 1)) (ds_strstart s)); lia.
Qed.

Lemma lm_visited_facts : forall Ins s cur, lm_ctx Ins s cur ->
  Forall (fun c => 0 <= c < ds_strstart s /\ ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) <= c) (lm_visited s cur).
Proof.
  intros Ins s cur C. pose proof (lm_limit_facts _ _ _ C) as (L0 & L1 & L2 & L3).
  unfold lm_visited. fold (lm_limit s).
  destruct (lm_loop_facts Ins (ds_strstart s) (ds_w_size s)
              (Z.to_nat (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s))
              s cur (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
              (ds_prev_length s) (if ds_lookahead s <? ds_nice_match s then ds_lookahead s else ds_nice_match s) (lm_limit s)
              (arr_get (ds_window s) (ds_strstart s + ds_prev_length s - 1)) (arr_get (ds_window s) (ds_strstart s + ds_prev_length s))
              (lc_chain _ _ _ C) (lm_mask_mod _ _ _ C) L0 L1 (lc_cur _ _ _ C) L2) as [HF _].
  eapply Forall_impl; [| exact HF]. intros c [Ic Lc]. pose proof (proj1 (lc_chain _ _ _ C) c Ic). lia.
Qed.

Lemma longest_match_post : forall Ins s cur, lm_ctx Ins s cur ->
  let '(s', ml) := longest_match s cur in
  exists v, s' = set_match_start s v
    /\ ml <= ds_lookahead s /\ (0 <= ds_lookahead s -> Z.min (ds_prev_length s) (ds_lookahead s) <= ml)
    /\ ml <= Z.max (ds_prev_length s) MAX_MATCH
    /\ ((v = ds_match_start s /\ ml <= ds_prev_length s)
        \/ (0 <= v < ds_strstart s /\ ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) <= v)).
Proof.
  intros Ins s cur C. pose proof (lm_limit_facts _ _ _ C) as (L0 & L1 & L2 & L3).
  unfold longest_match. fold (lm_limit s).
  match goal with |- context [longest_match_loop ?f s cur ?ch ?bl ?nm ?lim ?e1 ?e2] =>
    destruct (lm_loop_facts Ins (ds_strstart s) (ds_w_size s) f s cur ch bl nm lim e1 e2
                (lc_chain _ _ _ C) (lm_mask_mod _ _ _ C) L0 L1 (lc_cur _ _ _ C) L2) as [_ HL];
    destruct (longest_match_loop f s cur ch bl nm lim e1 e2) as [s' b'] end.
  destruct HL as (v & Es' & Lb & Alt). rewrite Es'. rewrite sms_lookahead.
  pose proof (proj1 (lc_chain _ _ _ C)) as H1.
  destruct (Z.leb_spec b' (ds_lookahead s)) as [X|X]; exists v.
  - split; [reflexivity|]. split; [exact X|]. split; [intros; lia|]. split; [destruct Alt as [[-> _]|(A1 & A2 & _)]; lia|].
    destruct Alt as [[-> ->] | (A1 & A2 & A3 & A4)]; [left; split; [reflexivity | lia] | right]. pose proof (H1 v A3). lia.
  - split; [reflexivity|]. split; [lia|]. split; [intros; lia|]. split; [lia|].
    destruct Alt as [[-> ->] | (A1 & A2 & A3 & A4)]; [left; split; [reflexivity | lia] | right]. pose proof (H1 v A3). lia.
Qed.

Lemma lm_pre_intro : forall Ins s cur, lm_ctx Ins s cur ->
  0 <= cur < 2 ^ 32 ->
  4 <= ds_max_chain_length s <= 4096 ->
  0 <= ds_strstart s -> ds_strstart s + 258 < arr_len (ds_window s) -> arr_len (ds_window s) <= 65536 ->
  0 <= ds_w_mask s < arr_len (ds_prev s) -> arr_len (ds_prev s) <= 32768 ->
  1 <= ds_prev_length s <= 258 -> 0 <= ds_nice_match s <= 258 -> 0 <= ds_lookahead s < 2 ^ 31 ->
  0 <= ds_good_match s <= 258 -> ds_w_size s <= 32768 ->
  lm_pre s cur.
Proof.
  intros Ins s cur C Hcur Hch Hs0 Hs1 Hwl Hm Hpl Hp Hn Hl Hg Hws. pose proof (lc_ws _ _ _ C).
  unfold lm_pre. split; [exact Hcur|].
  split. { destruct (ds_good_match s <=? ds_prev_length s); [rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4|]; lia. }
  split. { eapply Forall_impl; [| exact (lm_visited_facts _ _ _ C)]. intros c [A B]. exact A. }
  unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. repeat split; lia.
Qed.
