(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgInv BgSpecs BgLibSpec BgShiftSpec BgAddSpec BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section SqrSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition sqr_pre (rr ra : bnref) (s : ST) : Prop :=
  live rr s /\ live ra s /\ ndiff rr ROne /\ ndiff rr ra /\
  (length (gx_frames (st_ctx s)) < BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 1 <= BG_POOL)%nat /\
  (bn_top (getbn ra s) <= 127)%nat.

Lemma bn_sqr_fixed_top_spec : forall rr ra F s,
  sqr_pre rr ra s ->
  hoare F s (bn_sqr_fixed_top ops rr ra) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     let a := getbn ra s in let r := getbn rr s' in
     bn_mag r = bn_mag a * bn_mag a /\ bn_top r = (2 * bn_top a)%nat /\ bn_neg r = false).
Proof.
  intros rr ra F s (Lr & La & Nr1 & Nra & Hdepth & Hpool & Hal).
  apply hoare_wf. intros Hs. unfold bn_sqr_fixed_top.
  apply hoare_live; [constructor; [exact Lr|]; constructor; [exact La|constructor]|].
  set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va.
  apply hoare_bind_get. set (a := getbn ra s) in *.
  pose proof (st_wf_okv ra s Hs Va) as Ha. fold a in Ha. set (al := bn_top a) in *.
  destruct (Nat.eqb_spec al 0) as [Ez|Ez].
  -
    pose proof (st_wf_ok rr s Hs Vr Nr1) as Hr.
    apply (hoare_update rr (fun r => mkBN (bn_d r) (bn_buf r) 0%nat false (bn_flags r))); try assumption; try reflexivity.
    { destruct Hr as (R1 & R2 & R3 & R4). unfold bg_ok, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
    split; [apply keeps_setbn|]. cbv zeta. rewrite getbn_setbn_same by exact Vr. unfold bn_mag at 1. cbn [bn_top bn_buf bn_neg firstn lval].
    rewrite (bn_mag_top0 a Ez). split; [ring|]. split; [lia|reflexivity].
  - eapply hoare_bind; [apply BN_CTX_start_spec; exact Hdepth|].
    intros [] s0 Hs0 (Eb0' & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
    assert (G0 : forall x, getbn x s0 = getbn x s) by (intros x; unfold getbn; rewrite Eb0'; reflexivity).
    assert (Len0 : length (st_bns s0) = length (st_bns s)) by (rewrite Eb0'; reflexivity).

    eapply hoare_bind with (R := fun _ s3 => (length (st_bns s) <= length (st_bns s3))%nat /\
          gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u] /\ scal_same s s3 /\ slots_same u [rr] s s3 /\
          bn_mag (getbn rr s3) = bn_mag a * bn_mag a /\ bn_top (getbn rr s3) = (2 * al)%nat /\ bn_neg (getbn rr s3) = false).
    2:{ intros [] s3 Hs3 (Len3 & Ef3 & Sc3 & Sl3 & M3 & T3 & N3).
        eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3|].
        intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4).
        assert (G4 : forall x, getbn x s4 = getbn x s3) by (intros x; unfold getbn; rewrite Eb4; reflexivity).
        split.
        - split; [split|].
          + unfold ctx_keep. rewrite Eb4. split; [lia|]. auto.
          + intros x Hx Hnin. rewrite G4. apply Sl3; assumption.
          + eapply scal_same_trans; [exact Sc3|exact Sc4].
        - cbv zeta. rewrite G4. auto. }
    destruct (Nat.eqb_spec rr ra) as [E|_]; [exfalso; exact (Nra E)|].
    eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
    intros t sa Hsa (Et & Eua & Efa & Sca & Lena & Otha & _). rewrite Eu0 in Et, Eua.
    assert (Vt : (t < length (st_bns sa))%nat) by (apply live_valid; [exact Hsa|]; unfold live; rewrite Eua, Et; unfold RPool; lia).
    assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).
    assert (Ntr : ndiff t rr) by (rewrite Et; unfold ndiff, RPool, live in *; fold u in Lr; lia).
    assert (Vra : (rr < length (st_bns sa))%nat) by lia.
    set (max := (2 * al)%nat).
    eapply hoare_bind; [apply bn_wexpand_spec; [exact Vra|exact Nr1|unfold BG_DMAX, max; lia]|].
    intros [] s1 Hs1 (r1 & -> & (_ & _ & _ & _ & Hr1 & Hd1 & _)).
    destruct Ha as (A1 & A2). unfold bn_dmax in *.
    set (la := firstn al (bn_buf a)).
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1).
    assert (Hlal : length la = al) by (apply firstn_length_le; lia).
    pose proof Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.

    eapply hoare_bind with (R := fun _ s2 => length (st_bns s2) = length (st_bns sa) /\ st_ctx s2 = st_ctx sa /\ scal_same sa s2 /\
          (forall x, x <> rr -> x <> t -> getbn x s2 = getbn x sa) /\
          (max <= bn_dmax (getbn rr s2))%nat /\ lval (firstn max (bn_buf (getbn rr s2))) = lval la * lval la).
    2:{ intros [] s2 Hs2 (Len2 & Ectx2 & Sc2 & Oth2 & Hd2 & Emag2).
        assert (Vr2 : (rr < length (st_bns s2))%nat) by lia.
        pose proof (st_wf_ok rr s2 Hs2 Vr2 Nr1) as Hr2.
        apply (hoare_update rr (fun r => mkBN (bn_d r) (bn_buf r) max false (bn_flags r))); try assumption; try reflexivity.
        { destruct Hr2 as (Q1 & Q2 & Q3 & Q4). unfold bg_ok, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption. }
        rewrite length_setbn. cbn [setbn set_bns st_ctx]. rewrite Ectx2, Efa, Ef0.
        split; [lia|]. split; [reflexivity|]. split; [eapply scal_same_trans; [exact Sc0|]; eapply scal_same_trans; [exact Sca|exact Sc2]|]. split.
        - intros x Hx Hnin. fold (setbn rr (mkBN (bn_d (getbn rr s2)) (bn_buf (getbn rr s2)) max false (bn_flags (getbn rr s2))) s2).
          rewrite getbn_setbn_other by (intros ->; apply Hnin; left; reflexivity).
          rewrite Oth2; [|intros ->; apply Hnin; left; reflexivity|rewrite Et; unfold RPool; lia].
          rewrite Otha by (rewrite Et; unfold RPool; lia). apply G0.
        - fold (setbn rr (mkBN (bn_d (getbn rr s2)) (bn_buf (getbn rr s2)) max false (bn_flags (getbn rr s2))) s2).
          rewrite getbn_setbn_same by exact Vr2. unfold bn_mag at 1. cbn [bn_top bn_buf bn_neg].
          split; [exact Emag2|]. split; reflexivity. }
    set (s1 := setbn rr r1 sa).
    assert (L1 : length (st_bns s1) = length (st_bns sa)) by (unfold s1; apply length_setbn).
    assert (Egr : getbn rr s1 = r1) by (unfold s1; apply getbn_setbn_same; exact Vra).
    assert (Ega : getbn ra s1 = a).
    { unfold s1. rewrite getbn_setbn_other by exact Nra. rewrite Otha by (rewrite Et; unfold RPool, live in *; fold u in La; lia). apply G0. }

    assert (Hstore : forall sx (P : list Z), st_wf sx -> length (st_bns sx) = length (st_bns sa) -> getbn rr sx = r1 ->
              st_ctx sx = st_ctx sa -> scal_same sa sx -> (forall x, x <> rr -> x <> t -> getbn x sx = getbn x sa) ->
              limbs P -> length P = max -> lval P = lval la * lval la ->
              hoare F sx (bset ops rr (bn_with_buf r1 (splice (bn_buf r1) 0 P)))
                (fun _ s2 => length (st_bns s2) = length (st_bns sa) /\ st_ctx s2 = st_ctx sa /\ scal_same sa s2 /\
                   (forall x, x <> rr -> x <> t -> getbn x s2 = getbn x sa) /\
                   (max <= bn_dmax (getbn rr s2))%nat /\ lval (firstn max (bn_buf (getbn rr s2))) = lval la * lval la)).
    { intros sx P Hsx Lx Egx Ecx Scx Othx HP HPl HPv.
      assert (L2 : length (splice (bn_buf r1) 0 P) = length (bn_buf r1)) by (apply splice_length; lia).
      eapply hoare_set; try rewrite Lx; try rewrite Egx; try assumption; try reflexivity.
      - unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite L2. split; [apply splice_limbs; assumption|]. repeat split; assumption.
      - rewrite length_setbn. split; [exact Lx|]. split; [exact Ecx|]. split; [exact Scx|]. split.
        + intros x X1 X2. rewrite getbn_setbn_other by (intros E; apply X1; symmetry; exact E). apply Othx; assumption.
        + rewrite getbn_setbn_same by (rewrite Lx; exact Vra). unfold bn_dmax. cbn [bn_with_buf bn_buf]. rewrite L2.
          split; [lia|]. rewrite firstn_splice_0 by lia. exact HPv. }
    assert (Hs1' : scal_same sa s1 /\ (forall x, x <> rr -> x <> t -> getbn x s1 = getbn x sa)).
    { split; [unfold scal_same, s1; repeat split; reflexivity|]. intros x X1 X2. unfold s1. apply getbn_setbn_other. intros E; apply X1; symmetry; exact E. }
    destruct Hs1' as [Sc1 Oth1].
    destruct (Nat.eqb_spec al 4) as [E4|N4].
    { apply hoare_bind_get. rewrite Egr.
      assert (E4a : firstn 4 (bn_buf a) = la) by (unfold la; rewrite E4; reflexivity). rewrite E4a.
      destruct (sqr_comba_spec la 4 Hla ltac:(lia)) as (C1 & C2 & C3). change (2 * 4)%nat with 8%nat in *.
      apply (Hstore s1 (sqr_comba4 la)); try assumption; try reflexivity. unfold sqr_comba4. unfold max. lia. }
    destruct (Nat.eqb_spec al 8) as [E8|N8].
    { apply hoare_bind_get. rewrite Egr.
      assert (E8a : firstn 8 (bn_buf a) = la) by (unfold la; rewrite E8; reflexivity). rewrite E8a.
      destruct (sqr_comba_spec la 8 Hla ltac:(lia)) as (C1 & C2 & C3). change (2 * 8)%nat with 16%nat in *.
      apply (Hstore s1 (sqr_comba8 la)); try assumption; try reflexivity. unfold sqr_comba8. unfold max. lia. }
    destruct (Nat.ltb_spec al 16) as [Hlt|Hge].
    { apply hoare_bind_get. rewrite Egr. fold la.
      pose proof (sqr_normal_spec la Hla (firstn max (bn_buf r1)) ltac:(lia) (limbs_firstn _ _ R1) ltac:(rewrite firstn_length_le; unfold max in *; lia)) as Hn.
      destruct (sqr_normal la (firstn max (bn_buf r1))) as [ro tmp]. cbn [fst]. destruct Hn as (N1 & N2 & N3 & _). rewrite Hlal in N2.
      apply (Hstore s1 ro); try assumption; try reflexivity. }

    pose proof (kara_j_small al al Hge Hge ltac:(lia) ltac:(lia) Hal Hal) as Hj. cbv zeta in Hj |- *. rewrite Nat.max_id in Hj.
    set (kj := Z.to_nat (num_bits_word (Z.of_nat al) - 1)) in *. set (j := Nat.pow 2 kj) in *.
    destruct Hj as (J1 & J2 & J3 & J4).
    assert (Vt1 : (t < length (st_bns s1))%nat) by (rewrite L1; exact Vt).
    destruct (Nat.eqb_spec al j) as [Ej|Nj].
    +
      eapply hoare_bind; [apply bn_wexpand_spec; [exact Vt1|exact Nt1|unfold BG_DMAX; lia]|].
      intros [] s2 Hs2 (t1 & -> & (_ & _ & _ & _ & Ht1 & Hdt & _)).
      apply hoare_bind_get. apply hoare_bind_get.
      rewrite (getbn_setbn_same t) by exact Vt1. rewrite (getbn_setbn_other t rr) by exact Ntr. rewrite Egr. fold la.
      pose proof Ht1 as (T1 & T2 & T3 & T4). unfold bn_dmax in *.
      pose proof (sqr_scratch_le kj) as Hsc. fold j in Hsc.
      pose proof (sqr_recursive_spec kj la (firstn max (bn_buf r1)) (bn_buf t1) Hla (limbs_firstn _ _ R1) T1
                    ltac:(fold j; lia) ltac:(rewrite firstn_length_le; unfold max in *; fold j; lia) ltac:(lia)) as Hm.
      destruct (sqr_recursive kj la (firstn max (bn_buf r1)) (bn_buf t1)) as [ro to].
      destruct Hm as (M1 & M2 & M3 & M4 & M5). rewrite firstn_length_le in M2 by (unfold max in *; lia).
      set (s2 := setbn t t1 s1) in *.
      assert (L2 : length (st_bns s2) = length (st_bns sa)) by (unfold s2; rewrite length_setbn; exact L1).
      apply hoare_bind_set; try rewrite L2; try (unfold s2; rewrite getbn_setbn_same by exact Vt1); try assumption; try reflexivity.
      { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite M5. repeat split; assumption. }
      unfold s2. rewrite setbn_setbn_same. eapply hoare_wf. intros Hs3.
      apply (Hstore _ ro); try assumption; try reflexivity.
      * rewrite length_setbn. exact L1.
      * rewrite getbn_setbn_other by exact Ntr. exact Egr.
      * intros x X1 X2. rewrite getbn_setbn_other by (intros E; apply X2; symmetry; exact E). apply Oth1; assumption.
    +
      eapply hoare_bind; [apply bn_wexpand_spec; [exact Vt1|exact Nt1|unfold BG_DMAX, max; lia]|].
      intros [] s2 Hs2 (t1 & -> & (_ & _ & _ & _ & Ht1 & Hdt & _)).
      apply hoare_bind_get. apply hoare_bind_get.
      rewrite (getbn_setbn_same t) by exact Vt1. rewrite (getbn_setbn_other t rr) by exact Ntr. rewrite Egr. fold la.
      pose proof Ht1 as (T1 & T2 & T3 & T4). unfold bn_dmax in *.
      pose proof (sqr_normal_spec la Hla (firstn max (bn_buf r1)) ltac:(lia) (limbs_firstn _ _ R1) ltac:(rewrite firstn_length_le; unfold max in *; lia)) as Hn.
      destruct (sqr_normal la (firstn max (bn_buf r1))) as [ro to]. destruct Hn as (N1 & N2 & N3 & N4'). rewrite Hlal in N2.
      destruct (sqr_words_spec la Hla) as (W1 & W2 & W3). rewrite Hlal in W2. subst to.
      set (s2 := setbn t t1 s1) in *.
      assert (L2 : length (st_bns s2) = length (st_bns sa)) by (unfold s2; rewrite length_setbn; exact L1).
      assert (Ltb : length (splice (bn_buf t1) 0 (sqr_words la)) = length (bn_buf t1)) by (apply splice_length; unfold max in *; lia).
      apply hoare_bind_set; try rewrite L2; try (unfold s2; rewrite getbn_setbn_same by exact Vt1); try assumption; try reflexivity.
      { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite Ltb. split; [apply splice_limbs; assumption|]. repeat split; assumption. }
      unfold s2. rewrite setbn_setbn_same. eapply hoare_wf. intros Hs3.
      apply (Hstore _ ro); try assumption; try reflexivity.
      * rewrite length_setbn. exact L1.
      * rewrite getbn_setbn_other by exact Ntr. exact Egr.
      * intros x X1 X2. rewrite getbn_setbn_other by (intros E; apply X2; symmetry; exact E). apply Oth1; assumption.
Qed.

Lemma BN_sqr_spec : forall rr ra F s,
  sqr_pre rr ra s ->
  hoare F s (BN_sqr ops rr ra) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     let a := getbn ra s in let r := getbn rr s' in
     bn_canon r /\ bn_mag r = bn_mag a * bn_mag a /\ bn_neg r = false /\ (bn_top r <= 2 * bn_top a)%nat).
Proof.
  intros rr ra F s Hpre. pose proof Hpre as (Lr & _ & Nr1 & _). unfold BN_sqr.
  eapply hoare_bind; [apply bn_sqr_fixed_top_spec; exact Hpre|].
  intros [] s1 Hs1 (K1 & M1 & T1 & N1). cbv zeta in M1, T1, N1.
  assert (Vr1 : (rr < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|eapply keeps_live; eassumption]).
  eapply hoare_mono; [apply correct_top_spec; [exact Vr1|exact Nr1]|].
  intros [] s2 _ (r2 & -> & ->). split.
  - eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
    intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; exact Hin.
  - cbv zeta. rewrite getbn_setbn_same by exact Vr1.
    destruct (bg_correct_top_ok (getbn rr s1) (st_wf_ok rr s1 Hs1 Vr1 Nr1)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    split; [exact C2|]. split; [rewrite C3; exact M1|]. split; [rewrite C7, N1; reflexivity|lia].
Qed.

End SqrSpec.
