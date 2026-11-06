(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgInv BgSpecs BgLibSpec BgShiftSpec BgAddSpec BgWordSpec BgDivSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma kara_j_small : forall al bl : nat, (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  (al <= 127)%nat -> (bl <= 127)%nat ->
  let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
  let j := Nat.pow 2 kj in
  (4 <= kj)%nat /\ (j <= Nat.max al bl)%nat /\ (Nat.max al bl < 2 * j)%nat /\ (j <= 64)%nat.
Proof.
  intros al bl Ha Hb H1 H2 Ha' Hb'. pose proof (kara_j_facts al bl Ha Hb H1 H2 ltac:(lia)) as H. cbv zeta in *.
  set (kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) in *. destruct H as (J1 & J2 & J3 & _).
  repeat split; try assumption.
  destruct (Nat.le_gt_cases kj 6) as [Hle|Hgt].
  - apply (Nat.pow_le_mono_r 2 kj 6) in Hle; [|lia]. cbn in Hle. cbn. lia.
  - assert (Hp : (2 ^ 7 <= 2 ^ kj)%nat) by (apply Nat.pow_le_mono_r; lia). cbn in Hp. lia.
Qed.

Lemma mul_bound_lt' : forall a b A B, 0 <= a < A -> 0 <= b < B -> a * b < A * B.
Proof. intros. nia. Qed.

Section MulSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition mul_pre (rr ra rb : bnref) (s : ST) : Prop :=
  live rr s /\ live ra s /\ live rb s /\ ndiff rr ROne /\ ndiff rr ra /\ ndiff rr rb /\
  (length (gx_frames (st_ctx s)) < BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 1 <= BG_POOL)%nat /\
  (bn_top (getbn ra s) <= 127)%nat /\ (bn_top (getbn rb s) <= 127)%nat.

Lemma bn_mul_fixed_top_spec : forall rr ra rb F s,
  mul_pre rr ra rb s ->
  hoare F s (bn_mul_fixed_top ops rr ra rb) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     let a := getbn ra s in let b := getbn rb s in let r := getbn rr s' in
     bn_mag r = bn_mag a * bn_mag b /\
     (bn_top r = (if ((bn_top a =? 0) || (bn_top b =? 0))%nat then 0 else bn_top a + bn_top b)%nat) /\
     (bn_neg r = xorb (bn_neg a) (bn_neg b) \/ bn_top r = 0%nat /\ bn_neg r = false)).
Proof.
  intros rr ra rb F s (Lr & La & Lb & Nr1 & Nra & Nrb & Hdepth & Hpool & Hal & Hbl).
  apply hoare_wf. intros Hs. unfold bn_mul_fixed_top.
  apply hoare_live; [constructor; [exact Lr|]; constructor; [exact La|]; constructor; [exact Lb|constructor]|].
  set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va. pose proof (live_valid rb s Hs Lb) as Vb.
  apply hoare_bind_get. apply hoare_bind_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *.
  pose proof (st_wf_okv ra s Hs Va) as Ha. fold a in Ha. pose proof (st_wf_okv rb s Hs Vb) as Hb. fold b in Hb.
  set (al := bn_top a) in *. set (bl := bn_top b) in *.
  destruct ((al =? 0) || (bl =? 0))%nat eqn:Ez.
  -
    eapply hoare_mono; [apply BN_zero_spec; [exact Vr|exact Nr1]|].
    intros [] s1 _ (r1 & -> & T1 & T2). split; [apply keeps_setbn|]. cbv zeta. rewrite getbn_setbn_same by exact Vr.
    split; [|split; [exact T1|right; split; assumption]].
    rewrite (bn_mag_top0 r1 T1). apply orb_prop in Ez. destruct Ez as [E|E]; apply Nat.eqb_eq in E.
    + rewrite (bn_mag_top0 a E). ring.
    + rewrite (bn_mag_top0 b E). ring.
  - apply orb_false_elim in Ez. destruct Ez as [Ea0 Eb0]. apply Nat.eqb_neq in Ea0, Eb0.
    eapply hoare_bind; [apply BN_CTX_start_spec; exact Hdepth|].
    intros [] s0 Hs0 (Eb0' & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
    assert (G0 : forall x, getbn x s0 = getbn x s) by (intros x; unfold getbn; rewrite Eb0'; reflexivity).
    assert (Len0 : length (st_bns s0) = length (st_bns s)) by (rewrite Eb0'; reflexivity).
    destruct (Nat.eqb_spec rr ra) as [E|_]; [exfalso; exact (Nra E)|]. destruct (Nat.eqb_spec rr rb) as [E|_]; [exfalso; exact (Nrb E)|].
    cbn [orb].
    destruct Ha as (A1 & A2). destruct Hb as (B1 & B2). unfold bn_dmax in *.
    set (la := firstn al (bn_buf a)). set (lb := firstn bl (bn_buf b)).
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1). assert (Hlb : limbs lb) by (apply limbs_firstn; exact B1).
    assert (Hlal : length la = al) by (apply firstn_length_le; lia). assert (Hlbl : length lb = bl) by (apply firstn_length_le; lia).
    assert (Hprod : lval la * lval lb < Bp (al + bl)).
    { rewrite Bp_add. pose proof (lval_bound la Hla). pose proof (lval_bound lb Hlb). rewrite Hlal, Hlbl in *. apply mul_bound_lt'; assumption. }

    eapply hoare_bind with (R := fun _ s2 => (length (st_bns s) <= length (st_bns s2))%nat /\
          gx_frames (st_ctx s2) = gx_frames (st_ctx s) ++ [u] /\ scal_same s s2 /\ slots_same u [rr] s s2 /\
          bn_top (getbn rr s2) = (al + bl)%nat /\ bn_mag (getbn rr s2) = lval la * lval lb).
    2:{ intros [] s2 Hs2 (Len2 & Ef2 & Sc2 & Sl2 & Etop2 & Emag2).
        assert (Vr2 : (rr < length (st_bns s2))%nat) by lia.

        pose proof (st_wf_ok rr s2 Hs2 Vr2 Nr1) as Hr2.
        apply hoare_bind_update; try assumption; try reflexivity.
        set (s3 := setbn rr (bn_with_neg (getbn rr s2) (xorb (bn_neg a) (bn_neg b))) s2).
        eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef2|].
        intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4).
        assert (G4 : forall x, getbn x s4 = getbn x s3) by (intros x; unfold getbn; rewrite Eb4; reflexivity).
        split.
        - split; [split|].
          + unfold ctx_keep. rewrite Eb4. unfold s3. rewrite length_setbn. auto.
          + intros x Hx Hnin. rewrite G4. unfold s3. rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity).
            apply Sl2; assumption.
          + eapply scal_same_trans; [exact Sc2|]. exact Sc4.
        - cbv zeta. rewrite G4. unfold s3. rewrite getbn_setbn_same by exact Vr2.
          split; [exact Emag2|]. split; [cbn [bn_with_neg bn_top]; exact Etop2|left; reflexivity]. }

    assert (Hstore : forall s1 words (P : list Z) r1,
              st_wf s1 -> (rr < length (st_bns s1))%nat -> getbn rr s1 = r1 -> (words <= bn_dmax r1)%nat ->
              limbs P -> (length P <= words)%nat -> (al + bl <= length P)%nat -> lval P = lval la * lval lb ->
              hoare F s1 (bset ops rr (mkBN (bn_d r1) (splice (bn_buf r1) 0 P) (al + bl) (bn_neg r1) (bn_flags r1)))
                    (fun _ s2 => exists r2, s2 = setbn rr r2 s1 /\ bn_top r2 = (al + bl)%nat /\ bn_mag r2 = lval la * lval lb)).
    { intros s1 words P r1 Hs1 Vr1 Eg Hr1d HP HPl Htw HPv.
      pose proof (st_wf_ok rr s1 Hs1 Vr1 Nr1) as Hr1. rewrite Eg in Hr1. destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
      assert (L2 : length (splice (bn_buf r1) 0 P) = length (bn_buf r1)) by (apply splice_length; lia).
      eapply hoare_set; try rewrite Eg; try assumption; try reflexivity.
      - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite L2. split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia.
      - eexists. split; [reflexivity|]. split; [reflexivity|]. unfold bn_mag. cbn [bn_buf bn_top].
        assert (Ef : firstn (al + bl) (splice (bn_buf r1) 0 P) = firstn (al + bl) (P ++ skipn (length P) (bn_buf r1))) by reflexivity.
        rewrite Ef. rewrite firstn_app. replace (al + bl - length P)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
        rewrite lval_firstn_small; [exact HPv|exact HP|rewrite HPv; exact Hprod]. }
    destruct ((al =? bl) && (al =? 8))%nat eqn:Ec8.
    +
      apply andb_prop in Ec8. destruct Ec8 as [E1 E2]. apply Nat.eqb_eq in E1, E2.
      eapply hoare_bind; [apply bn_wexpand_spec; [rewrite Len0; exact Vr|exact Nr1|unfold BG_DMAX; lia]|].
      intros [] s1 Hs1 (r1 & -> & (_ & _ & _ & _ & Hr1 & Hd1 & _)). apply hoare_bind_get.
      rewrite getbn_setbn_same by (rewrite Len0; exact Vr).
      assert (E8a : firstn 8 (bn_buf a) = la) by (subst la; rewrite E2; reflexivity).
      assert (E8b : firstn 8 (bn_buf b) = lb) by (subst lb; rewrite <- E1, E2; reflexivity).
      rewrite E8a, E8b.
      destruct (mul_comba8_spec la lb Hla Hlb ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
      replace 16%nat with (al + bl)%nat by lia.
      eapply hoare_mono; [apply (Hstore _ (al + bl)%nat (mul_comba8 la lb) r1); try assumption; try lia|].
      * rewrite length_setbn, Len0. exact Vr.
      * apply getbn_setbn_same. rewrite Len0. exact Vr.
      * intros [] s2 _ (r2 & -> & T2 & M2). rewrite setbn_setbn_same. rewrite length_setbn, Len0. cbn [setbn set_bns st_ctx]. rewrite Ef0.
        split; [lia|]. split; [reflexivity|]. split; [exact Sc0|]. split.
        -- intros x Hx Hnin. rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity). apply G0.
        -- rewrite getbn_setbn_same by (rewrite Len0; exact Vr). split; assumption.
    + destruct ((16 <=? al) && (16 <=? bl) && (al <=? bl + 1) && (bl <=? al + 1))%nat eqn:Ek.
      *
        apply andb_prop in Ek. destruct Ek as [Ek K4]. apply andb_prop in Ek. destruct Ek as [Ek K3].
        apply andb_prop in Ek. destruct Ek as [K1 K2]. apply Nat.leb_le in K1, K2, K3, K4.
        pose proof (kara_j_small al bl K1 K2 K3 K4 Hal Hbl) as Hj. cbv zeta in Hj |- *.
        set (kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) in *. set (j := Nat.pow 2 kj) in *.
        destruct Hj as (J1 & J2 & J3 & J4).
        eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
        intros t sa Hsa (Et & Eua & Efa & Sca & Lena & Otha & _). rewrite Eu0 in Et, Eua.
        assert (Vt : (t < length (st_bns sa))%nat) by (apply live_valid; [exact Hsa|]; unfold live; rewrite Eua, Et; unfold RPool; lia).
        assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).
        assert (Ntr : ndiff t rr) by (rewrite Et; unfold ndiff, RPool, live in *; fold u in Lr; lia).
        assert (Vra : (rr < length (st_bns sa))%nat) by lia.

        assert (Hkara : forall w (ro to : list Z) t1 r1,
                  st_wf (setbn rr r1 (setbn t t1 sa)) -> bg_ok t1 -> (w <= bn_dmax r1)%nat ->
                  limbs ro -> (length ro <= w)%nat -> (al + bl <= length ro)%nat -> lval ro = lval la * lval lb ->
                  limbs to -> length to = length (bn_buf t1) ->
                  hoare F (setbn rr r1 (setbn t t1 sa))
                    (bbind ops (bset ops t (bn_with_buf t1 to)) (fun _ =>
                       bset ops rr (mkBN (bn_d r1) (splice (bn_buf r1) 0 ro) (al + bl) (bn_neg r1) (bn_flags r1))))
                    (fun _ s2 => (length (st_bns s) <= length (st_bns s2))%nat /\
                       gx_frames (st_ctx s2) = gx_frames (st_ctx s) ++ [u] /\ scal_same s s2 /\ slots_same u [rr] s s2 /\
                       bn_top (getbn rr s2) = (al + bl)%nat /\ bn_mag (getbn rr s2) = lval la * lval lb)).
        { intros w ro to t1 r1 Hs2 Ht1 Hd2 M1 M2 M3 M4 M5 M6.
          set (s2 := setbn rr r1 (setbn t t1 sa)) in *.
          assert (L2 : length (st_bns s2) = length (st_bns sa)) by (unfold s2; rewrite !length_setbn; reflexivity).
          assert (Egt : getbn t s2 = t1) by (unfold s2; rewrite getbn_setbn_other by (apply ndiff_sym; exact Ntr); apply getbn_setbn_same; exact Vt).
          destruct Ht1 as (T1 & T2 & T3 & T4). unfold bn_dmax in *.
          apply hoare_bind_set; try rewrite L2; try rewrite Egt; try assumption; try reflexivity.
          { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite M6. repeat split; assumption. }
          set (s3 := setbn t (bn_with_buf t1 to) s2).
          eapply hoare_wf. intros Hs3.
          eapply hoare_mono; [apply (Hstore s3 w ro r1); try assumption|].
          - unfold s3. rewrite length_setbn, L2. exact Vra.
          - unfold s3, s2. rewrite getbn_setbn_other by exact Ntr. apply getbn_setbn_same. rewrite length_setbn. exact Vra.
          - intros [] s4 _ (r2 & -> & T2' & M2'). unfold s3, s2.
            rewrite !length_setbn. cbn [setbn set_bns st_ctx]. rewrite Efa, Ef0.
            split; [lia|]. split; [reflexivity|]. split; [eapply scal_same_trans; [exact Sc0|exact Sca]|]. split.
            + intros x Hx Hnin. rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity).
              rewrite getbn_setbn_other by (rewrite Et; unfold RPool; lia).
              rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity).
              rewrite getbn_setbn_other by (rewrite Et; unfold RPool; lia).
              rewrite Otha by (rewrite Et; unfold RPool; lia). apply G0.
            + rewrite getbn_setbn_same by (rewrite !length_setbn; exact Vra). split; assumption. }
        assert (Ega : getbn ra sa = a) by (rewrite Otha by (rewrite Et; unfold RPool, live in *; fold u in La; lia); apply G0).
        assert (Egb : getbn rb sa = b) by (rewrite Otha by (rewrite Et; unfold RPool, live in *; fold u in Lb; lia); apply G0).
        destruct ((j <? al) || (j <? bl))%nat eqn:Epart.
        --
           eapply hoare_bind; [apply bn_wexpand_spec; [exact Vt|exact Nt1|unfold BG_DMAX; lia]|].
           intros [] s1 Hs1 (t1 & -> & (_ & _ & _ & _ & Ht1 & Hd1 & _)).
           eapply hoare_bind; [apply bn_wexpand_spec; [rewrite length_setbn; exact Vra|exact Nr1|unfold BG_DMAX; lia]|].
           intros [] s2 Hs2 (r1 & -> & (_ & _ & _ & _ & Hr1 & Hd2 & _)).
           apply hoare_bind_get. apply hoare_bind_get.
           rewrite (getbn_setbn_other rr t) by (apply ndiff_sym; exact Ntr). rewrite (getbn_setbn_same t) by exact Vt.
           rewrite (getbn_setbn_same rr) by (rewrite length_setbn; exact Vra). fold la lb.
           apply orb_prop in Epart.
           assert (Hmin : (j <= al /\ j <= bl)%nat) by (destruct Epart as [E|E]; apply Nat.ltb_lt in E; lia).
           pose proof Ht1 as (T1 & T2 & T3 & T4). pose proof Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
           pose proof (mul_part_recursive_spec kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf r1)) (bn_buf t1)
                         Hla Hlb (limbs_firstn _ _ R1) T1 ltac:(lia) ltac:(lia) ltac:(fold j; lia) ltac:(fold j; lia) ltac:(lia) ltac:(lia)
                         ltac:(fold j; lia) ltac:(fold j; lia) ltac:(rewrite firstn_length_le by lia; fold j; lia) ltac:(fold j; lia)) as Hm.
           destruct (mul_part_recursive kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf r1)) (bn_buf t1)) as [ro to].
           destruct Hm as (M1 & M2 & M3 & M4 & M5). rewrite firstn_length_le in M2 by lia.
           apply (Hkara (8 * j)%nat ro to t1 r1); try assumption; try lia.
        --
           apply orb_false_elim in Epart. destruct Epart as [E1 E2]. apply Nat.ltb_ge in E1, E2.
           eapply hoare_bind; [apply bn_wexpand_spec; [exact Vt|exact Nt1|unfold BG_DMAX; lia]|].
           intros [] s1 Hs1 (t1 & -> & (_ & _ & _ & _ & Ht1 & Hd1 & _)).
           eapply hoare_bind; [apply bn_wexpand_spec; [rewrite length_setbn; exact Vra|exact Nr1|unfold BG_DMAX; lia]|].
           intros [] s2 Hs2 (r1 & -> & (_ & _ & _ & _ & Hr1 & Hd2 & _)).
           apply hoare_bind_get. apply hoare_bind_get.
           rewrite (getbn_setbn_other rr t) by (apply ndiff_sym; exact Ntr). rewrite (getbn_setbn_same t) by exact Vt.
           rewrite (getbn_setbn_same rr) by (rewrite length_setbn; exact Vra). fold la lb.
           pose proof Ht1 as (T1 & T2 & T3 & T4). pose proof Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
           pose proof (scratch_rec_le kj) as Hsc. fold j in Hsc.
           pose proof (mul_recursive_spec kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf r1)) (bn_buf t1)
                         Hla Hlb (limbs_firstn _ _ R1) T1 ltac:(lia) ltac:(lia) ltac:(lia)
                         ltac:(fold j; lia) ltac:(fold j; lia) ltac:(rewrite firstn_length_le by lia; fold j; lia) ltac:(lia)) as Hm.
           destruct (mul_recursive kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf r1)) (bn_buf t1)) as [ro to].
           destruct Hm as (M1 & M2 & M3 & M4 & M5). rewrite firstn_length_le in M2 by lia.
           apply (Hkara (4 * j)%nat ro to t1 r1); try assumption; try lia.
      *
        eapply hoare_bind; [apply bn_wexpand_spec; [rewrite Len0; exact Vr|exact Nr1|unfold BG_DMAX; lia]|].
        intros [] s1 Hs1 (r1 & -> & (_ & _ & _ & _ & Hr1 & Hd1 & _)). apply hoare_bind_get.
        rewrite getbn_setbn_same by (rewrite Len0; exact Vr). fold la lb.
        destruct (mul_normal_spec la lb Hla Hlb) as (N1 & N2 & N3).
        assert (N3' : length (mul_normal la lb) = (al + bl)%nat).
        { rewrite N3, Hlal, Hlbl. destruct (Nat.eqb_spec al 0); [lia|]. destruct (Nat.eqb_spec bl 0); [lia|]. reflexivity. }
        eapply hoare_mono; [apply (Hstore _ (al + bl)%nat (mul_normal la lb) r1); try assumption; try lia|].
        -- rewrite length_setbn, Len0. exact Vr.
        -- apply getbn_setbn_same. rewrite Len0. exact Vr.
        -- intros [] s2 _ (r2 & -> & T2 & M2). rewrite setbn_setbn_same. rewrite length_setbn, Len0. cbn [setbn set_bns st_ctx]. rewrite Ef0.
           split; [lia|]. split; [reflexivity|]. split; [exact Sc0|]. split.
           ++ intros x Hx Hnin. rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity). apply G0.
           ++ rewrite getbn_setbn_same by (rewrite Len0; exact Vr). split; assumption.
Qed.

Lemma BN_mul_spec : forall rr ra rb F s,
  mul_pre rr ra rb s ->
  hoare F s (BN_mul ops rr ra rb) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     let a := getbn ra s in let b := getbn rb s in let r := getbn rr s' in
     bn_canon r /\ bn_mag r = bn_mag a * bn_mag b /\
     bn_neg r = (xorb (bn_neg a) (bn_neg b) && negb (bn_top r =? 0)%nat) /\
     (bn_top r <= bn_top a + bn_top b)%nat).
Proof.
  intros rr ra rb F s Hpre. pose proof Hpre as (Lr & _ & _ & Nr1 & _). unfold BN_mul.
  eapply hoare_bind; [apply bn_mul_fixed_top_spec; exact Hpre|].
  intros [] s1 Hs1 (K1 & M1 & T1 & N1). cbv zeta in M1, T1, N1.
  assert (Vr1 : (rr < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|eapply keeps_live; eassumption]).
  eapply hoare_mono; [apply correct_top_spec; [exact Vr1|exact Nr1]|].
  intros [] s2 _ (r2 & -> & ->). split.
  - eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
    intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; exact Hin.
  - cbv zeta. rewrite getbn_setbn_same by exact Vr1.
    destruct (bg_correct_top_ok (getbn rr s1) (st_wf_ok rr s1 Hs1 Vr1 Nr1)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    split; [exact C2|]. split; [rewrite C3; exact M1|]. split.
    + rewrite C7. destruct N1 as [E|[E1 E2]]; [rewrite E; reflexivity|].
      assert (E0 : bn_top (bn_correct_top_pure (getbn rr s1)) = 0%nat) by lia. rewrite E0, E2. cbn [Nat.eqb negb]. rewrite !andb_false_r. reflexivity.
    + rewrite T1 in C4. destruct ((bn_top (getbn ra s) =? 0) || (bn_top (getbn rb s) =? 0))%nat; lia.
Qed.

End MulSpec.
