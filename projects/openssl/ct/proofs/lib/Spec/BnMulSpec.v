(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnDivSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lval_firstn_small : forall l m, limbs l -> lval l < Bp m -> lval (firstn m l) = lval l.
Proof.
  intros l m Hl Hv. destruct (Nat.le_gt_cases (length l) m) as [Hle|Hgt]; [rewrite firstn_all2 by lia; reflexivity|].
  pose proof (lval_split_le m l ltac:(lia)) as E.
  pose proof (lval_nonneg _ (limbs_firstn m l Hl)). pose proof (lval_nonneg _ (limbs_skipn m l Hl)) as Hs.
  pose proof (Bp_pos m). assert (lval (skipn m l) = 0) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma kara_j_facts : forall al bl : nat, (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  Z.of_nat al + Z.of_nat bl <= 32001 ->
  let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
  let j := Nat.pow 2 kj in
  (4 <= kj)%nat /\ (j <= Nat.max al bl)%nat /\ (Nat.max al bl < 2 * j)%nat /\ Z.of_nat j <= 8192.
Proof.
  intros al bl Ha Hb H1 H2 Hsum. cbv zeta. set (m := Nat.max al bl).
  assert (Hm16 : 16 <= Z.of_nat m) by (subst m; lia).
  assert (Hm : Z.of_nat m <= 16001) by (subst m; lia).
  destruct (num_bits_word_spec (Z.of_nat m) ltac:(lia)) as (B1 & B2 & B3).
  set (bits := num_bits_word (Z.of_nat m)) in *.
  set (kj := Z.to_nat (bits - 1)). assert (Ekj : Z.of_nat kj = bits - 1) by (subst kj; lia).
  assert (Ej : Z.of_nat (Nat.pow 2 kj) = 2 ^ (bits - 1)) by (rewrite Nat2Z.inj_pow, Ekj; reflexivity).
  assert (Hk4 : 4 <= bits - 1).
  { destruct (Z.lt_ge_cases (bits - 1) 4) as [Hlt|]; [exfalso|assumption].
    assert (2 ^ bits <= 2 ^ 4) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hk13 : bits - 1 <= 13).
  { destruct (Z.le_gt_cases (bits - 1) 13) as [|Hgt]; [assumption|exfalso].
    assert (2 ^ 14 <= 2 ^ (bits - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (E2 : 2 ^ bits = 2 * 2 ^ (bits - 1)).
  { replace bits with (Z.succ (bits - 1)) at 1 by lia. apply Z.pow_succ_r. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Ej. assert (2 ^ (bits - 1) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Section MulSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
Definition same1234 (s s' : LS) : Prop :=
  getbn RB1 s' = getbn RB1 s /\ getbn RB2 s' = getbn RB2 s /\ getbn RB3 s' = getbn RB3 s /\ getbn RB4 s' = getbn RB4 s.

Lemma BN_mul_spec : forall s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_rest (ls_ctx s) ->
  Z.of_nat (bn_top (getbn RB3 s)) + Z.of_nat (bn_top (getbn RB2 s)) <= 32001 ->
  (forall s' X', st_ok s' -> own s' X' -> ctx_rest (ls_ctx s') -> same1234 s s' ->
     let a := getbn RB3 s in let b := getbn RB2 s in let r := getbn RB5 s' in
     bn_canon r -> bn_mag r = bn_mag a * bn_mag b ->
     bn_neg r = (xorb (bn_neg a) (bn_neg b) && negb (bn_top r =? 0)%nat) ->
     (bn_top r <= bn_top a + bn_top b)%nat ->
     Q tt s' X') ->
  bwp (BN_mul ops RB5 RB3 RB2) s X Q.
Proof.
  intros s X Q Hs Ho Hrest Hsum HQ. unfold BN_mul, bn_mul_fixed_top.
  apply bwp_bind. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  set (a := getbn RB3 s) in *. set (b := getbn RB2 s) in *.
  pose proof (st_ok_getbn RB3 s Hs I) as Ha. fold a in Ha. pose proof (st_ok_getbn RB2 s Hs I) as Hb. fold b in Hb.
  set (al := bn_top a) in *. set (bl := bn_top b) in *.
  (* [comment removed for export] *)
  assert (Htail : forall s2 X2, st_ok s2 -> own s2 X2 -> ctx_rest (ls_ctx s2) -> same1234 s s2 ->
            bn_mag (getbn RB5 s2) = bn_mag a * bn_mag b -> bn_neg (getbn RB5 s2) = xorb (bn_neg a) (bn_neg b) \/ bn_top (getbn RB5 s2) = 0%nat ->
            (bn_top (getbn RB5 s2) <= al + bl)%nat ->
            bwp (bbind ops (bget ops RB5) (fun b0 => bset ops RB5 (bn_correct_top_pure b0))) s2 X2 Q).
  { intros s2 X2 Hs2 Ho2 Hr2 Hsame Hmag Hneg Htop. apply bwp_bind, bwp_get.
    destruct (bn_correct_top_ok (getbn RB5 s2) (st_ok_getbn RB5 s2 Hs2 I)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    apply bwp_update; try assumption; try exact I; [apply bn_blocks_same; [exact C6|rewrite C5; reflexivity]|].
    intros Hs3 Ho3. set (s3 := setbn RB5 (bn_correct_top_pure (getbn RB5 s2)) s2) in *.
    assert (G5 : getbn RB5 s3 = bn_correct_top_pure (getbn RB5 s2)) by reflexivity.
    apply HQ; try assumption; rewrite ?G5; try assumption.
    - rewrite C3. exact Hmag.
    - rewrite C8. destruct Hneg as [E|E]; [rewrite E; reflexivity|].
      assert (E0 : bn_top (bn_correct_top_pure (getbn RB5 s2)) = 0%nat) by lia. rewrite E0. cbn [Nat.eqb negb]. rewrite !andb_false_r. reflexivity.
    - fold al bl. lia. }
  destruct ((al =? 0) || (bl =? 0))%nat eqn:Ez.
  - (* [comment removed for export] *)
    apply bwp_bind, bwp_get.
    apply bwp_update; try assumption; try exact I; [apply bn_ok_zero, st_ok_getbn; [assumption|exact I]|reflexivity|].
    intros Hs1 Ho1. apply Htail; try assumption.
    + repeat split; reflexivity.
    + cbn [getbn setbn ls_b5]. unfold bn_mag at 1. unfold bn_zero_pure. cbn [bn_top bn_buf firstn lval].
      apply orb_prop in Ez. destruct Ez as [E|E]; apply Nat.eqb_eq in E.
      * rewrite (bn_mag_top0 a E). ring.
      * rewrite (bn_mag_top0 b E). ring.
    + right. reflexivity.
    + cbn [getbn setbn ls_b5]. unfold bn_zero_pure. cbn [bn_top]. lia.
  - apply orb_false_elim in Ez. destruct Ez as [Ea0 Eb0]. apply Nat.eqb_neq in Ea0, Eb0.
    apply bwp_bind. apply BN_CTX_start_spec; try assumption.
    intros s0 X0 F0 Hs0 Ho0 Hw0 Hfr0 Hu0.
    cbn [bnref_eqb orb].
    destruct Ha as (A1 & A2 & A3 & A4). destruct Hb as (B1 & B2 & B3 & B4). unfold bn_dmax in *.
    set (la := firstn al (bn_buf a)). set (lb := firstn bl (bn_buf b)).
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1). assert (Hlb : limbs lb) by (apply limbs_firstn; exact B1).
    assert (Hlal : length la = al) by (apply firstn_length_le; lia). assert (Hlbl : length lb = bl) by (apply firstn_length_le; lia).
    assert (Hprod : lval la * lval lb < Bp (al + bl)).
    { rewrite Bp_add. pose proof (lval_bound la Hla). pose proof (lval_bound lb Hlb). rewrite Hlal, Hlbl in *. apply mul_bound_lt; assumption. }
    (* [comment removed for export] *)
    apply bwp_bind.
    assert (Halg : forall (Q' : unit -> LS -> blocks -> Prop),
       (forall s2 X2, st_ok s2 -> own s2 X2 -> ctx_wf (ls_ctx s2) -> cx_frames (ls_ctx s2) = [0%nat] -> same1234 s s2 ->
          bn_top (getbn RB5 s2) = (al + bl)%nat -> bn_mag (getbn RB5 s2) = lval la * lval lb -> Q' tt s2 X2) ->
       bwp (if ((al =? bl) && (al =? 8))%nat
            then bbind ops (bn_wexpand ops RB5 16) (fun _ => bbind ops (bget ops RB5) (fun r =>
                   bset ops RB5 (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_comba8 (firstn 8 (bn_buf a)) (firstn 8 (bn_buf b)))) 16 (bn_neg r) (bn_flags r))))
            else if ((16 <=? al) && (16 <=? bl) && (al <=? bl + 1) && (bl <=? al + 1))%nat
                 then let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
                      let j := Nat.pow 2 kj in
                      bbind ops (BN_CTX_get ops) (fun t =>
                        if ((j <? al) || (j <? bl))%nat
                        then bbind ops (bn_wexpand ops t (8 * j)) (fun _ => bbind ops (bn_wexpand ops RB5 (8 * j)) (fun _ =>
                               bbind ops (bget ops t) (fun tb => bbind ops (bget ops RB5) (fun r =>
                                 let '(ro, to) := mul_part_recursive kj kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (al - j) (bl - j)
                                                                     (firstn (4 * j) (bn_buf r)) (bn_buf tb) in
                                 bbind ops (bset ops t (bn_with_buf tb to)) (fun _ =>
                                   bset ops RB5 (mkBN (bn_d r) (splice (bn_buf r) 0 ro) (al + bl) (bn_neg r) (bn_flags r)))))))
                        else bbind ops (bn_wexpand ops t (4 * j)) (fun _ => bbind ops (bn_wexpand ops RB5 (4 * j)) (fun _ =>
                               bbind ops (bget ops t) (fun tb => bbind ops (bget ops RB5) (fun r =>
                                 let '(ro, to) := mul_recursive kj (firstn al (bn_buf a)) (firstn bl (bn_buf b)) (j - al) (j - bl)
                                                                (firstn (2 * j) (bn_buf r)) (bn_buf tb) in
                                 bbind ops (bset ops t (bn_with_buf tb to)) (fun _ =>
                                   bset ops RB5 (mkBN (bn_d r) (splice (bn_buf r) 0 ro) (al + bl) (bn_neg r) (bn_flags r))))))))
                 else bbind ops (bn_wexpand ops RB5 (al + bl)) (fun _ => bbind ops (bget ops RB5) (fun r =>
                        bset ops RB5 (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_normal (firstn al (bn_buf a)) (firstn bl (bn_buf b)))) (al + bl)
                                           (bn_neg r) (bn_flags r))))) s0 X0 Q').
    { intros Q' HQ'.
      assert (Hsame0 : same1234 s s0) by (repeat split; apply F0).
      (* [comment removed for export] *)
      assert (Hstore : forall s1 X1 words (P : list Z) (Q'' : unit -> LS -> blocks -> Prop),
                st_ok s1 -> own s1 X1 -> same1234 s s1 -> ctx_wf (ls_ctx s1) -> cx_frames (ls_ctx s1) = [0%nat] ->
                Z.of_nat words <= DMAX_MAX -> limbs P -> (length P <= words)%nat -> (al + bl <= length P)%nat -> lval P = lval la * lval lb ->
                (forall s2 X2, st_ok s2 -> own s2 X2 -> ctx_wf (ls_ctx s2) -> cx_frames (ls_ctx s2) = [0%nat] -> same1234 s s2 ->
                   bn_top (getbn RB5 s2) = (al + bl)%nat -> bn_mag (getbn RB5 s2) = lval la * lval lb -> Q'' tt s2 X2) ->
                forall r1, bn_ok r1 -> (words <= bn_dmax r1)%nat -> getbn RB5 s1 = r1 ->
                bwp (bset ops RB5 (mkBN (bn_d r1) (splice (bn_buf r1) 0 P) (al + bl) (bn_neg r1) (bn_flags r1))) s1 X1 Q'').
      { intros s1 X1 words P Q'' Hs1 Ho1 Hsm1 Hw1 Hf1 Hwd HP HPl Htw HPv HQ'' r1 Hr1 Hr1d Eg.
        destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
        set (r2 := mkBN (bn_d r1) (splice (bn_buf r1) 0 P) (al + bl) (bn_neg r1) (bn_flags r1)).
        assert (L2 : length (bn_buf r2) = length (bn_buf r1)) by (subst r2; cbn [bn_buf]; apply splice_length; lia).
        assert (Hr2 : bn_ok r2).
        { unfold bn_ok, bn_dmax. rewrite L2. subst r2. cbn [bn_buf bn_top bn_flags].
          split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia. }
        apply bwp_update; try assumption; try exact I; [rewrite Eg; apply bn_blocks_same; [reflexivity|exact L2]|].
        intros Hs2 Ho2. apply HQ''; try assumption.
        - reflexivity.
        - cbn [getbn setbn ls_b5]. unfold bn_mag. subst r2. cbn [bn_buf bn_top].
          assert (Ef : firstn (al + bl) (splice (bn_buf r1) 0 P) = firstn (al + bl) (P ++ skipn (length P) (bn_buf r1))) by reflexivity.
          rewrite Ef. destruct (Nat.le_gt_cases (al + bl) (length P)) as [Hle|Hgt].
          + rewrite firstn_app. replace (al + bl - length P)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
            rewrite lval_firstn_small; [exact HPv|exact HP|rewrite HPv; exact Hprod].
          + rewrite firstn_app, firstn_all2 by lia. rewrite lval_app.
            (* [comment removed for export] *)
            exfalso. lia. }
      destruct ((al =? bl) && (al =? 8))%nat eqn:Ec8.
      - (* [comment removed for export] *)
        apply andb_prop in Ec8. destruct Ec8 as [E1 E2]. apply Nat.eqb_eq in E1, E2.
        apply bwp_bind. apply bn_wexpand_spec; try assumption; try exact I; [apply st_ok_getbn; [assumption|exact I]|unfold DMAX_MAX; lia|].
        intros r1 X1 (_ & _ & _ & _ & Hr1 & Hd1 & _) Hs1 Ho1. apply bwp_bind, bwp_get.
        assert (E8a : firstn 8 (bn_buf a) = la) by (subst la; rewrite E2; reflexivity).
        assert (E8b : firstn 8 (bn_buf b) = lb) by (subst lb; rewrite <- E1, E2; reflexivity).
        rewrite E8a, E8b.
        destruct (mul_comba8_spec la lb Hla Hlb ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
        change (getbn RB5 (setbn RB5 r1 s0)) with r1. replace 16%nat with (al + bl)%nat by lia.
        eapply (Hstore _ _ (al + bl)%nat); try eassumption; try lia; try reflexivity.
        unfold DMAX_MAX; lia.
      - destruct ((16 <=? al) && (16 <=? bl) && (al <=? bl + 1) && (bl <=? al + 1))%nat eqn:Ek.
        + (* [comment removed for export] *)
          apply andb_prop in Ek. destruct Ek as [Ek K4]. apply andb_prop in Ek. destruct Ek as [Ek K3].
          apply andb_prop in Ek. destruct Ek as [K1 K2]. apply Nat.leb_le in K1, K2, K3, K4.
          pose proof (kara_j_facts al bl K1 K2 K3 K4 Hsum) as Hj. cbv zeta in Hj |- *.
          set (kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) in *. set (j := Nat.pow 2 kj) in *.
          destruct Hj as (J1 & J2 & J3 & J4).
          apply bwp_bind. apply (BN_CTX_get_spec s0 X0 0%nat); try assumption; try lia.
          intros sa Xa Hva _ Fa Hsa Hoa Hwa Hfra Hua.
          assert (Hsamea : same1234 s sa).
          { destruct Hsame0 as (S1 & S2 & S3 & S4). repeat split; rewrite Fa by congruence; assumption. }
          assert (Ega : getbn RB3 sa = a) by apply Hsamea. assert (Egb : getbn RB2 sa = b) by apply Hsamea.
          destruct ((j <? al) || (j <? bl))%nat eqn:Epart.
          * (* [comment removed for export] *)
            apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|unfold DMAX_MAX; lia|].
            intros t1 X1 (_ & _ & _ & _ & Ht1 & Hd1 & _) Hs1 Ho1. set (s1 := setbn (RPool 0) t1 sa) in *.
            assert (Hv1 : valid_ref (RPool 0) s1) by (subst s1; apply valid_ref_setbn; exact Hva).
            apply bwp_bind. apply bn_wexpand_spec; try assumption; try exact I; [apply st_ok_getbn; [assumption|exact I]|unfold DMAX_MAX; lia|].
            intros r1 X2 (_ & _ & _ & _ & Hr1 & Hd2 & _) Hs2 Ho2. set (s2 := setbn RB5 r1 s1) in *.
            apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
            assert (Egt : getbn (RPool 0) s2 = t1) by (subst s2 s1; rewrite getbn_setbn_other by congruence; apply getbn_setbn_same; assumption).
            assert (Egr : getbn RB5 s2 = r1) by reflexivity.
            rewrite Egt, Egr. fold la lb.
            apply orb_prop in Epart.
            assert (Hmin : (j <= al /\ j <= bl)%nat) by (destruct Epart as [E|E]; apply Nat.ltb_lt in E; lia).
            destruct Ht1 as (T1 & T2 & T3 & T4). pose proof Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
            pose proof (mul_part_recursive_spec kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf r1)) (bn_buf t1)
                          Hla Hlb (limbs_firstn _ _ R1) T1 ltac:(lia) ltac:(lia) ltac:(fold j; lia) ltac:(fold j; lia) ltac:(lia) ltac:(lia)
                          ltac:(fold j; lia) ltac:(fold j; lia) ltac:(rewrite firstn_length_le by lia; fold j; lia) ltac:(fold j; lia)) as Hm.
            destruct (mul_part_recursive kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf r1)) (bn_buf t1)) as [ro to].
            destruct Hm as (M1 & M2 & M3 & M4 & M5). rewrite firstn_length_le in M2 by lia.
            apply bwp_bind. apply bwp_update; try assumption;
              [unfold bn_ok, bn_dmax; cbn [bn_with_buf bn_buf bn_top bn_flags]; rewrite M5; repeat split; assumption
              |rewrite Egt; apply bn_blocks_same; [reflexivity|exact M5]|].
            intros Hs3 Ho3. set (s3 := setbn (RPool 0) (bn_with_buf t1 to) s2) in *.
            eapply (Hstore s3 X2 (8 * j)%nat ro); try eassumption; try lia; try reflexivity.
            subst s3 s2 s1. repeat (eapply ctx_wf_same; [apply ctx_same_setbn|]). exact Hwa.
          * (* [comment removed for export] *)
            apply orb_false_elim in Epart. destruct Epart as [E1 E2]. apply Nat.ltb_ge in E1, E2.
            apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|unfold DMAX_MAX; lia|].
            intros t1 X1 (_ & _ & _ & _ & Ht1 & Hd1 & _) Hs1 Ho1. set (s1 := setbn (RPool 0) t1 sa) in *.
            assert (Hv1 : valid_ref (RPool 0) s1) by (subst s1; apply valid_ref_setbn; exact Hva).
            apply bwp_bind. apply bn_wexpand_spec; try assumption; try exact I; [apply st_ok_getbn; [assumption|exact I]|unfold DMAX_MAX; lia|].
            intros r1 X2 (_ & _ & _ & _ & Hr1 & Hd2 & _) Hs2 Ho2. set (s2 := setbn RB5 r1 s1) in *.
            apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
            assert (Egt : getbn (RPool 0) s2 = t1) by (subst s2 s1; rewrite getbn_setbn_other by congruence; apply getbn_setbn_same; assumption).
            assert (Egr : getbn RB5 s2 = r1) by reflexivity.
            rewrite Egt, Egr. fold la lb.
            destruct Ht1 as (T1 & T2 & T3 & T4). pose proof Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
            pose proof (scratch_rec_le kj) as Hsc. fold j in Hsc.
            pose proof (mul_recursive_spec kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf r1)) (bn_buf t1)
                          Hla Hlb (limbs_firstn _ _ R1) T1 ltac:(lia) ltac:(lia) ltac:(lia)
                          ltac:(fold j; lia) ltac:(fold j; lia) ltac:(rewrite firstn_length_le by lia; fold j; lia) ltac:(lia)) as Hm.
            destruct (mul_recursive kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf r1)) (bn_buf t1)) as [ro to].
            destruct Hm as (M1 & M2 & M3 & M4 & M5). rewrite firstn_length_le in M2 by lia.
            apply bwp_bind. apply bwp_update; try assumption;
              [unfold bn_ok, bn_dmax; cbn [bn_with_buf bn_buf bn_top bn_flags]; rewrite M5; repeat split; assumption
              |rewrite Egt; apply bn_blocks_same; [reflexivity|exact M5]|].
            intros Hs3 Ho3. set (s3 := setbn (RPool 0) (bn_with_buf t1 to) s2) in *.
            eapply (Hstore s3 X2 (4 * j)%nat ro); try eassumption; try lia; try reflexivity.
            subst s3 s2 s1. repeat (eapply ctx_wf_same; [apply ctx_same_setbn|]). exact Hwa.
        + (* [comment removed for export] *)
          apply bwp_bind. apply bn_wexpand_spec; try assumption; try exact I; [apply st_ok_getbn; [assumption|exact I]|unfold DMAX_MAX; lia|].
          intros r1 X1 (_ & _ & _ & _ & Hr1 & Hd1 & _) Hs1 Ho1. apply bwp_bind, bwp_get. fold la lb.
          destruct (mul_normal_spec la lb Hla Hlb) as (N1 & N2 & N3).
          assert (N3' : length (mul_normal la lb) = (al + bl)%nat).
          { rewrite N3, Hlal, Hlbl. destruct (Nat.eqb_spec al 0); [lia|]. destruct (Nat.eqb_spec bl 0); [lia|]. reflexivity. }
          eapply (Hstore _ _ (al + bl)%nat); try eassumption; try lia; try reflexivity.
          unfold DMAX_MAX; lia. }
    apply Halg. clear Halg. intros s2 X2 Hs2 Ho2 Hw2 Hf2 Hsm2 Etop2 Emag2.
    (* [comment removed for export] *)
    apply bwp_bind. apply bwp_bind, bwp_get.
    set (r2 := getbn RB5 s2) in *. pose proof (st_ok_getbn RB5 s2 Hs2 I) as Hr2. fold r2 in Hr2.
    apply bwp_update; [exact Hs2|exact Ho2|exact I| |reflexivity|].
    { destruct Hr2 as (R1 & R2 & R3 & R4). unfold bn_ok, bn_dmax in *. cbn [bn_with_neg bn_buf bn_top bn_flags]. tauto. }
    intros Hs3 Ho3. set (s3 := setbn RB5 (bn_with_neg r2 (xorb (bn_neg a) (bn_neg b))) s2) in *.
    apply BN_CTX_end_spec; try assumption.
    intros s4 F4 Hs4 Ho4 Hr4. apply Htail; try assumption.
    + destruct Hsm2 as (S1 & S2 & S3 & S4). repeat split; rewrite F4; assumption.
    + rewrite F4. exact Emag2.
    + left. rewrite F4. reflexivity.
    + rewrite F4. change (bn_top (getbn RB5 s3)) with (bn_top r2). lia.
Qed.

End MulSpec.
