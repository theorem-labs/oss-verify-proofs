(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Section Order.
Variables (FC DP : arr).

Definition lex (x y : Z) : Prop :=
  arr_get FC x < arr_get FC y \/ (arr_get FC x = arr_get FC y /\ arr_get DP x <= arr_get DP y).

Lemma lex_total : forall x y, lex x y \/ lex y x.
Proof. intros. unfold lex. lia. Qed.
Lemma lex_refl : forall x, lex x x.
Proof. intros. unfold lex. lia. Qed.
Lemma lex_trans : forall x y z, lex x y -> lex y z -> lex x z.
Proof. intros. unfold lex in *. lia. Qed.
Lemma lex_freq : forall x y, lex x y -> arr_get FC x <= arr_get FC y.
Proof. intros. unfold lex in *. lia. Qed.

Definition lexb (x y : Z) : bool :=
  (arr_get FC x <? arr_get FC y) || ((arr_get FC x =? arr_get FC y) && (arr_get DP x <=? arr_get DP y)).

Lemma lexb_spec : forall x y, lexb x y = true <-> lex x y.
Proof.
  intros. unfold lexb, lex. rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.
Lemma lexb_false : forall x y, lexb x y = false -> lex y x /\ ~ lex x y.
Proof.
  intros x y H. assert (~ lex x y) by (rewrite <- lexb_spec, H; discriminate).
  split; [destruct (lex_total x y); tauto| assumption].
Qed.
End Order.

Section Flat.
Variables (s : deflate_state) (t : tree_id).
Variables (FC DL : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Set Warnings "-notation-for-abbreviation".
Local Notation U HP := (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (only parsing).

Lemma smaller_flat : forall HP x y, smaller (U HP) t x y = lexb FC DP x y.
Proof. intros. unfold smaller, lexb. autorewrite with btupd. reflexivity. Qed.


Definition heap_ok (HP : arr) (k0 exc hl : Z) : Prop :=
  forall c, 2 <= c <= hl -> k0 <= c / 2 -> c / 2 <> exc -> lex FC DP (arr_get HP (c / 2)) (arr_get HP c).

Definition rearr (HP HP' : arr) (lo hi : Z) : Prop :=
  arr_len HP' = arr_len HP
  /\ (forall i, ~ (lo <= i <= hi) -> arr_get HP' i = arr_get HP i)
  /\ exists f g : Z -> Z, forall i, lo <= i <= hi ->
       lo <= f i <= hi /\ lo <= g i <= hi /\ g (f i) = i /\ f (g i) = i /\ arr_get HP' i = arr_get HP (f i).

Lemma rearr_refl : forall HP lo hi, rearr HP HP lo hi.
Proof.
  intros. split; [reflexivity|]. split; [intros; reflexivity|].
  exists (fun i => i), (fun i => i). intros. repeat split; try lia. 
Qed.

Lemma rearr_ext : forall HP HP1 HP2 lo hi, rearr HP HP1 lo hi ->
  arr_len HP2 = arr_len HP1 -> (forall i, arr_get HP2 i = arr_get HP1 i) -> rearr HP HP2 lo hi.
Proof.
  intros HP HP1 HP2 lo hi (L & O & f & g & B) L2 E. split; [congruence|]. split.
  - intros. rewrite E. apply O. assumption.
  - exists f, g. intros i Hi. destruct (B i Hi) as ([? ?]&[? ?]&?&?&?). rewrite E. repeat split; auto.
Qed.

Lemma rearr_trans : forall HP HP1 HP2 lo hi, rearr HP HP1 lo hi -> rearr HP1 HP2 lo hi -> rearr HP HP2 lo hi.
Proof.
  intros HP HP1 HP2 lo hi (L1 & O1 & f1 & g1 & B1) (L2 & O2 & f2 & g2 & B2).
  split; [congruence|]. split.
  - intros. rewrite O2, O1 by assumption. reflexivity.
  - exists (fun i => f1 (f2 i)), (fun i => g2 (g1 i)). intros i Hi.
    destruct (B2 i Hi) as (R2 & G2 & GF2 & FG2 & E2).
    destruct (B1 (f2 i) ltac:(lia)) as (R1 & G1 & GF1 & FG1 & E1).
    destruct (B1 i Hi) as (R1' & G1' & GF1' & FG1' & E1').
    destruct (B2 (g1 i) ltac:(lia)) as (R2' & G2' & GF2' & FG2' & E2').
    split; [lia|]. split; [lia|]. split; [rewrite GF1; exact GF2|]. split; [rewrite FG2'; exact FG1'|].
    rewrite E2, E1. reflexivity.
Qed.

Lemma rearr_widen : forall HP HP' lo hi lo' hi', rearr HP HP' lo hi -> lo' <= lo -> hi <= hi' -> rearr HP HP' lo' hi'.
Proof.
  intros HP HP' lo hi lo' hi' (L & O & f & g & B) Hlo Hhi. split; [exact L|]. split.
  - intros. apply O. lia.
  - exists (fun i => if (lo <=? i) && (i <=? hi) then f i else i), (fun i => if (lo <=? i) && (i <=? hi) then g i else i).
    intros i Hi. destruct (Z.leb_spec lo i); destruct (Z.leb_spec i hi); cbn [andb].
    + destruct (B i ltac:(lia)) as (R & G & GF & FG & E).
      replace ((lo <=? f i) && (f i <=? hi)) with true by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
      replace ((lo <=? g i) && (g i <=? hi)) with true by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
      repeat split; try lia.
    + replace ((lo <=? i) && (i <=? hi)) with false by (symmetry; rewrite Bool.andb_false_iff, !Z.leb_gt; lia).
      repeat split; try lia. apply O. lia.
    + replace ((lo <=? i) && (i <=? hi)) with false by (symmetry; rewrite Bool.andb_false_iff, !Z.leb_gt; lia).
      repeat split; try lia. apply O. lia.
    + replace ((lo <=? i) && (i <=? hi)) with false by (symmetry; rewrite Bool.andb_false_iff, !Z.leb_gt; lia).
      repeat split; try lia. apply O. lia.
Qed.

Lemma rearr_swap : forall HP lo hi p q, 0 <= lo -> hi < arr_len HP -> lo <= p <= hi -> lo <= q <= hi ->
  rearr HP (arr_set (arr_set HP p (arr_get HP q)) q (arr_get HP p)) lo hi.
Proof.
  intros HP lo hi p q Hlo Hhi Hp Hq.
  assert (G : forall i, arr_get (arr_set (arr_set HP p (arr_get HP q)) q (arr_get HP p)) i
                        = if i =? q then arr_get HP p else if i =? p then arr_get HP q else arr_get HP i).
  { intros i. rewrite !arr_get_set. unfold arr_inb. rewrite arr_len_set.
    replace ((0 <=? q) && (q <? arr_len HP)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    replace ((0 <=? p) && (p <? arr_len HP)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    rewrite !Bool.andb_true_r. rewrite (Z.eqb_sym q i), (Z.eqb_sym p i). reflexivity. }
  split; [rewrite !arr_len_set; reflexivity|]. split.
  - intros i Hi. rewrite G. destruct (Z.eqb_spec i q); [lia|]. destruct (Z.eqb_spec i p); [lia|]. reflexivity.
  - exists (fun i => if i =? p then q else if i =? q then p else i), (fun i => if i =? p then q else if i =? q then p else i).
    intros i Hi. rewrite G.
    destruct (Z.eqb_spec i p).
    + subst i. rewrite (Z.eqb_sym q p). destruct (Z.eqb_spec p q); rewrite ?Z.eqb_refl; repeat split; try lia; congruence.
    + destruct (Z.eqb_spec i q).
      * subst i. rewrite Z.eqb_refl. repeat split; lia.
      * destruct (Z.eqb_spec i p); [lia|]. destruct (Z.eqb_spec i q); [lia|]. repeat split; lia.
Qed.



Section Sift.
Variables (HP0 : arr) (k0 v : Z).
Hypothesis HLr : 1 <= k0 <= HL /\ HL <= 572.

Definition hc1 (B : arr) (k : Z) : Prop :=
  forall c, 2 <= c <= HL -> k0 <= c / 2 -> c / 2 <> k -> lex FC DP (arr_get B (c / 2)) (arr_get B c).
Definition hc2 (B : arr) (k : Z) : Prop :=
  k0 <= k / 2 -> forall c, 2 <= c <= HL -> c / 2 = k -> lex FC DP (arr_get B (k / 2)) (arr_get B c).

Lemma sift_loop : forall f HPc k,
  arr_len HPc = 573 -> k0 <= k <= HL -> (k = k0 \/ k0 <= k / 2) -> HL < k * 2 ^ (Z.of_nat f + 1) ->
  rearr HP0 (arr_set HPc k v) k0 HL -> hc1 (arr_set HPc k v) k -> hc2 (arr_set HPc k v) k ->
  let '(X', k') := pqdownheap_loop f (U HPc) t v k (Z.shiftl k 1) in
  exists HPf, X' = U HPf /\ arr_len HPf = 573 /\ k0 <= k' <= HL
    /\ rearr HP0 (arr_set HPf k' v) k0 HL /\ heap_ok (arr_set HPf k' v) k0 0 HL.
Proof.
  induction f as [|f IH]; intros HPc k LEN Hk Hk2 Hf RR C1 C2.
  - rewrite pqdownheap_loop_0. exists HPc. split; [reflexivity|]. split; [exact LEN|]. split; [lia|]. split; [exact RR|].
    rewrite Z.add_0_l, Z.pow_1_r in Hf.
    intros c Hc Hck0 _. destruct (Z.eq_dec (c / 2) k); [lia|]. apply C1; lia.
  - rewrite pqdownheap_loop_S. autorewrite with btupd. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
    destruct (Z.leb_spec (k * 2) HL) as [Hj|Hj].
    2:{ hnf. exists HPc. split; [reflexivity|]. split; [exact LEN|]. split; [lia|]. split; [exact RR|].
        intros c Hc Hck0 _. destruct (Z.eq_dec (c / 2) k); [lia|]. apply C1; lia. }
    cbv zeta. rewrite !smaller_flat.
    set (j := if (k * 2 <? HL) && lexb FC DP (arr_get HPc (k * 2 + 1)) (arr_get HPc (k * 2)) then k * 2 + 1 else k * 2).
    assert (Hj1 : k * 2 <= j <= HL /\ j / 2 = k /\ j <= k * 2 + 1).
    { subst j. destruct (Z.ltb_spec (k * 2) HL); cbn [andb]; [destruct (lexb _ _ _ _)|]; lia. }
    assert (Hsib : forall c, 2 <= c <= HL -> c / 2 = k -> lex FC DP (arr_get HPc j) (arr_get HPc c)).
    { intros c Hc Hck. assert (c = k * 2 \/ c = k * 2 + 1) by lia. subst j.
      destruct (Z.ltb_spec (k * 2) HL); cbn [andb].
      - destruct (lexb FC DP (arr_get HPc (k * 2 + 1)) (arr_get HPc (k * 2))) eqn:E.
        + apply lexb_spec in E. destruct H as [-> | ->]; [exact E| apply lex_refl].
        + apply lexb_false in E. destruct H as [-> | ->]; [apply lex_refl| tauto].
      - destruct H as [-> | ->]; [apply lex_refl| lia]. }
    clearbody j. autorewrite with btupd.
    assert (Bk : forall i, arr_get (arr_set HPc k v) i = if i =? k then v else arr_get HPc i).
    { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LEN.
      destruct (Z.eqb_spec k i), (Z.eqb_spec i k); try lia; cbn [andb]; [|reflexivity].
      replace ((0 <=? k) && (k <? 573)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia). reflexivity. }
    destruct (lexb FC DP v (arr_get HPc j)) eqn:Ev.
    +
      apply lexb_spec in Ev. hnf.
      exists HPc. split; [reflexivity|]. split; [exact LEN|]. split; [lia|]. split; [exact RR|].
      intros c Hc Hck0 _. destruct (Z.eq_dec (c / 2) k).
      * rewrite !Bk. rewrite e, Z.eqb_refl. destruct (Z.eqb_spec c k); [lia|].
        eapply lex_trans; [exact Ev|]. apply Hsib; lia.
      * apply C1; lia.
    +
      apply lexb_false in Ev. destruct Ev as [Ev _].
      specialize (IH (arr_set HPc k (arr_get HPc j)) j).
      replace (k * 2 ^ (Z.of_nat (S f) + 1)) with (k * 2 * 2 ^ (Z.of_nat f + 1)) in Hf
        by (rewrite <- Z.mul_assoc; f_equal; rewrite <- (Z.pow_succ_r 2) by lia; f_equal; lia).
      set (B := arr_set HPc k v) in *. set (B' := arr_set (arr_set HPc k (arr_get HPc j)) j v) in *.
      assert (LB : arr_len B = 573) by (subst B; rewrite arr_len_set; exact LEN).
      assert (B'k : forall i, arr_get B' i = if i =? j then arr_get B k else if i =? k then arr_get B j else arr_get B i).
      { intros i. subst B' B. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LEN.
        replace ((0 <=? j) && (j <? 573)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
        replace ((0 <=? k) && (k <? 573)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
        rewrite Z.eqb_refl. cbn [andb].
        destruct (Z.eqb_spec j i), (Z.eqb_spec i j), (Z.eqb_spec k i), (Z.eqb_spec i k), (Z.eqb_spec k j); try lia; reflexivity. }
      destruct (pqdownheap_loop f (U (arr_set HPc k (arr_get HPc j))) t v j (Z.shiftl j 1)) as [X' k'].
      apply IH.
      * rewrite arr_len_set. exact LEN.
      * lia.
      * right. lia.
      * pose proof (Z.pow_pos_nonneg 2 (Z.of_nat f + 1)). nia.
      *
        eapply rearr_ext with (HP1 := arr_set (arr_set B k (arr_get B j)) j (arr_get B k)).
        -- eapply rearr_trans; [exact RR|]. apply rearr_swap; lia.
        -- subst B' B. rewrite !arr_len_set. reflexivity.
        -- intros i. rewrite B'k. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LB.
           replace ((0 <=? j) && (j <? 573)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
           replace ((0 <=? k) && (k <? 573)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
           cbn [andb]. destruct (Z.eqb_spec i j), (Z.eqb_spec j i), (Z.eqb_spec i k), (Z.eqb_spec k i); try lia; reflexivity.
      *
        intros c Hc Hck0 Hcj. rewrite !B'k.
        assert (Bkk : arr_get B k = v) by (rewrite Bk, Z.eqb_refl; reflexivity).
        assert (Bo : forall i, i <> k -> arr_get B i = arr_get HPc i).
        { intros i Hi. rewrite Bk. destruct (Z.eqb_spec i k); [lia| reflexivity]. }
        destruct (Z.eqb_spec (c / 2) j); [lia|].
        destruct (Z.eqb_spec c j).
        --
           subst c. replace (j / 2 =? k) with true by (symmetry; apply Z.eqb_eq; lia).
           rewrite Bkk, Bo by lia. exact Ev.
        -- destruct (Z.eqb_spec (c / 2) k).
           ++
              destruct (Z.eqb_spec c k); [lia|]. rewrite !Bo by lia. apply Hsib; lia.
           ++ destruct (Z.eqb_spec c k).
              **
                 subst c. apply C2; lia.
              ** apply C1; lia.
      *
        intros Hj2 c Hc Hcj. rewrite !B'k.
        replace (j / 2) with k by lia. rewrite Z.eqb_refl.
        destruct (Z.eqb_spec k j); [lia|].
        destruct (Z.eqb_spec c j); [lia|]. destruct (Z.eqb_spec c k); [lia|].
        rewrite <- Hcj. apply C1; lia.
Qed.

End Sift.

Theorem pqdownheap_flat : forall HP k0,
  arr_len HP = 573 -> 1 <= k0 <= HL -> HL <= 572 ->
  heap_ok HP k0 k0 HL ->
  exists HP', pqdownheap (U HP) t k0 = U HP' /\ arr_len HP' = 573
    /\ rearr HP HP' k0 HL /\ heap_ok HP' k0 0 HL.
Proof.
  intros HP k0 LEN Hk0 HHL OK. unfold pqdownheap. autorewrite with btupd.
  assert (Hf : HL < k0 * 2 ^ (Z.of_nat 32 + 1)).
  { change (HL < k0 * 2 ^ 33). pose proof (Z.pow_le_mono_r 2 10 33). nia. }
  assert (E0 : forall i, arr_get (arr_set HP k0 (arr_get HP k0)) i = arr_get HP i).
  { intros i. rewrite arr_get_set. destruct (Z.eqb_spec k0 i); [subst; destruct (arr_inb HP i); reflexivity| reflexivity]. }
  pose proof (sift_loop HP k0 (arr_get HP k0) ltac:(lia) 32 HP k0 LEN ltac:(lia) ltac:(left; reflexivity) Hf) as SLP.
  destruct (pqdownheap_loop 32 (U HP) t (arr_get HP k0) k0 (Z.shiftl k0 1)) as [X' k'].
  destruct SLP as (HPf & -> & LENf & Hk' & RR & OK').
  - eapply rearr_ext; [apply rearr_refl| rewrite arr_len_set; reflexivity| exact E0].
  - intros c Hc H1 H2. rewrite !E0. apply OK; lia.
  - intros H c Hc Hck. lia.
  - autorewrite with btupd. exists (arr_set HPf k' (arr_get HP k0)). split; [reflexivity|].
    split; [rewrite arr_len_set; exact LENf|]. split; [exact RR| exact OK'].
Qed.


Theorem heap_root_min : forall HP hl, heap_ok HP 1 0 hl -> forall i, 1 <= i <= hl -> lex FC DP (arr_get HP 1) (arr_get HP i).
Proof.
  intros HP hl OK i. remember (Z.to_nat i) as n eqn:En. revert i En.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros i En Hi.
  destruct (Z.eq_dec i 1) as [->|]; [apply lex_refl|].
  eapply lex_trans; [apply (IH (Z.to_nat (i / 2)) ltac:(lia) (i / 2)); lia|].
  apply OK; lia.
Qed.

Theorem heapify_flat : forall fuel HP n, arr_len HP = 573 -> 0 <= n -> n <= HL <= 572 -> (Z.to_nat n <= fuel)%nat ->
  heap_ok HP (n + 1) 0 HL ->
  exists HP', build_tree_loop3 fuel (U HP) t n = U HP' /\ arr_len HP' = 573 /\ rearr HP HP' 1 HL /\ heap_ok HP' 1 0 HL.
Proof.
  induction fuel as [|fuel IH]; intros HP n LEN Hn HnHL Hf OK.
  - exists HP. cbn [build_tree_loop3]. split; [reflexivity|]. split; [exact LEN|]. split; [apply rearr_refl|].
    replace n with 0 in OK by lia. exact OK.
  - cbn [build_tree_loop3]. destruct (Z.leb_spec 1 n).
    + destruct (pqdownheap_flat HP n LEN ltac:(lia) ltac:(lia)) as (HP1 & E1 & LEN1 & RR1 & OK1).
      { intros c Hc H1 H2. apply OK; lia. }
      rewrite E1.
      destruct (IH HP1 (n - 1) LEN1 ltac:(lia) ltac:(lia) ltac:(lia)) as (HP' & E' & LEN' & RR' & OK').
      { replace (n - 1 + 1) with n by lia. exact OK1. }
      exists HP'. split; [exact E'|]. split; [exact LEN'|]. split; [|exact OK'].
      eapply rearr_trans; [|exact RR']. eapply rearr_widen; [exact RR1| lia| lia].
    + exists HP. split; [reflexivity|]. split; [exact LEN|]. split; [apply rearr_refl|].
      replace n with 0 in OK by lia. exact OK.
Qed.

Corollary heapify_flat0 : forall HP, arr_len HP = 573 -> 0 <= HL <= 572 ->
  exists HP', build_tree_loop3 (Z.to_nat (HL / 2)) (U HP) t (HL / 2) = U HP' /\ arr_len HP' = 573
    /\ rearr HP HP' 1 HL /\ heap_ok HP' 1 0 HL.
Proof.
  intros HP LEN HHL. apply heapify_flat; [exact LEN| lia| lia| lia|].
  intros c Hc H1 H2. lia.
Qed.

End Flat.

Ltac Zify.zify_post_hook ::= idtac.
