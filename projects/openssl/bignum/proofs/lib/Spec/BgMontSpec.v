(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MontSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition mont_ok (s : ST) (N : Z) (nl : nat) : Prop :=
  let n := getbn RMontN s in
  bn_top n = nl /\ (1 <= nl <= 127)%nat /\ bn_neg n = false /\ bn_mag n = N /\ Z.odd N = true /\ 1 <= N /\
  0 <= st_n0 s < BW /\ (st_n0 s * nth 0 (bn_buf n) 0 + 1) mod BW = 0 /\
  let rr := getbn RMontRR s in
  bn_top rr = nl /\ bn_neg rr = false /\ bn_mag rr = (Bp nl * Bp nl) mod N.

Lemma mont_ok_keeps : forall u o (s s' : ST) N nl, keeps u o s s' -> ~ In RMontN o -> ~ In RMontRR o -> mont_ok s N nl -> mont_ok s' N nl.
Proof.
  intros u o s s' N nl K H1 H2 Hm. unfold mont_ok in *. cbv zeta in *.
  destruct K as [[_ Sl] (_ & En0 & _ & _)].
  assert (E1 : getbn RMontN s' = getbn RMontN s) by (apply Sl; [unfold RMontN, NFIX; lia|exact H1]).
  assert (E2 : getbn RMontRR s' = getbn RMontRR s) by (apply Sl; [unfold RMontRR, NFIX; lia|exact H2]).
  rewrite E1, E2, En0. exact Hm.
Qed.

Definition from_mont_pre (ret r : bnref) (s : ST) (nl : nat) : Prop :=
  live ret s /\ live r s /\ ndiff ret ROne /\ ndiff r ROne /\ ndiff ret r /\ ndiff ret RMontN /\ ndiff r RMontN /\
  (bn_top (getbn r s) <= 2 * nl)%nat /\ bn_neg (getbn r s) = false.

Lemma bn_from_montgomery_word_spec : forall ret r F s N nl,
  mont_ok s N nl -> from_mont_pre ret r s nl -> bn_mag (getbn r s) < N * Bp nl ->
  hoare F s (bn_from_montgomery_word ops ret r) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [ret; r] s s' /\
     let x := getbn ret s' in
     bn_top x = nl /\ bn_neg x = false /\ 0 <= bn_mag x < N /\ (bn_mag x * Bp nl) mod N = bn_mag (getbn r s) mod N).
Proof.
  intros ret r F s N nl Hm (Lret & Lr & Nret1 & Nr1 & Nrr & NretN & NrN & Htop & Hneg) HT.
  apply hoare_wf. intros Hs. unfold bn_from_montgomery_word.
  replace ((ret =? r)%nat || (ret =? RMontN)%nat || (r =? RMontN)%nat) with false
    by (symmetry; rewrite !orb_false_iff, !Nat.eqb_neq; repeat split; assumption).
  set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid ret s Hs Lret) as Vret. pose proof (live_valid r s Hs Lr) as Vr.
  unfold mont_ok in Hm. cbv zeta in Hm. destruct Hm as (Etn & Hnl & Enn & EmN & HoddN & HN1 & Hn0 & Hinv & _).
  apply hoare_bind_get. set (n := getbn RMontN s) in *. rewrite Etn.
  destruct (Nat.eqb_spec nl 0) as [|_]; [lia|].
  assert (VN : (RMontN < length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; unfold RMontN, NFIX; lia).
  pose proof (st_wf_okv RMontN s Hs VN) as Hnv. fold n in Hnv. destruct Hnv as (Hnl1 & Hnl2). unfold bn_dmax in Hnl2.
  set (max := (2 * nl)%nat). set (T := bn_mag (getbn r s)) in *.
  pose proof (st_wf_okv r s Hs Vr) as Hrv.
  eapply hoare_bind; [apply bn_wexpand_spec; [exact Vr|exact Nr1|unfold BG_DMAX, max; lia]|].
  intros [] s1 Hs1 (r1 & -> & Hex).
  pose proof (gexpanded_prefix _ _ _ (st_wf_ok r s Hs Vr Nr1) Hex) as Hpre.
  destruct Hex as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). pose proof Hok1 as (O1 & O2 & O3 & O4). unfold bn_dmax in *.
  apply hoare_bind_get. rewrite (getbn_setbn_same r) by exact Vr. apply hoare_bind_get.
  rewrite (getbn_setbn_other r RMontN) by exact NrN. fold n. apply hoare_bind_getst.
  change (st_n0 (setbn r r1 s)) with (st_n0 s).
  replace ((0 <=? st_n0 s) && (st_n0 s <? 18446744073709551616)) with true
    by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; unfold BW in Hn0; exact Hn0).
  cbn [negb].
  set (np := firstn nl (bn_buf n)).
  assert (Hnp : limbs np) by (apply limbs_firstn; exact Hnl1).
  assert (Lnp : length np = nl) by (apply firstn_length_le; lia).
  assert (ENp : lval np = N) by (rewrite <- EmN; unfold bn_mag; rewrite Etn; reflexivity).
  assert (Enp0 : nth 0 np 0 = nth 0 (bn_buf n) 0) by (unfold np; rewrite nth_firstn; destruct (Nat.ltb_spec 0 nl); [reflexivity|lia]).

  set (buf := splice (bn_buf r1) (bn_top r1) (repeat 0 (max - bn_top r1))).
  assert (Lbuf : length buf = length (bn_buf r1)) by (apply splice_length; rewrite repeat_length; lia).
  assert (Hbufl : limbs buf) by (apply splice_limbs; [exact O1|apply limbs_repeat; exact limb_0]).
  assert (Ebuf : lval (firstn (2 * nl) buf) = T).
  { fold max. replace max with (bn_top r1 + (max - bn_top r1))%nat at 1 by lia. unfold buf. rewrite firstn_pad_zeros by lia.
    rewrite lval_app, lval_repeat0, Z.mul_0_r, Z.add_0_r. rewrite E1, Hpre. reflexivity. }
  pose proof (mont_reduce_loop_spec np (st_n0 s) buf Hnp ltac:(lia) ltac:(rewrite Enp0; exact Hinv) Hbufl ltac:(rewrite Lnp; unfold max in *; lia)) as Hloop.
  rewrite Lnp in Hloop. destruct (mont_reduce_loop np (st_n0 s) nl nl 0 buf 0) as [buf' carry].
  destruct Hloop as (P1 & P2 & P3 & P4 & P5 & W & HW & HV). rewrite Ebuf, ENp in HV.
  rewrite Hneg in E2. rewrite E2, Enn. cbn [xorb].
  apply hoare_bind_set; try rewrite length_setbn; try rewrite (getbn_setbn_same r) by exact Vr; try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite P2, Lbuf. repeat split; try assumption; try (unfold max in *; lia). }
  { cbn [bn_buf]. rewrite P2, Lbuf. reflexivity. }
  rewrite setbn_setbn_same. set (r2 := mkBN (bn_d r1) buf' max false (bn_flags r1)). set (s2 := setbn r r2 s).
  assert (L2 : length (st_bns s2) = length (st_bns s)) by (unfold s2; apply length_setbn).
  eapply hoare_bind; [apply bn_wexpand_spec; [rewrite L2; exact Vret|exact Nret1|unfold BG_DMAX; lia]|].
  intros [] s3 Hs3 (rt1 & -> & Hex3). destruct Hex3 as (G1 & G2 & G3 & G4 & Hokt & Hdt1 & Hdt2). pose proof Hokt as (Q1 & Q2 & Q3 & Q4). unfold bn_dmax in *.
  apply hoare_bind_get. rewrite (getbn_setbn_same ret) by (rewrite L2; exact Vret). apply hoare_bind_get.
  assert (Egr2 : getbn r (setbn ret rt1 s2) = r2) by (rewrite (getbn_setbn_other ret r) by exact Nrr; unfold s2; apply getbn_setbn_same; exact Vr).
  rewrite Egr2. cbn [r2 bn_buf bn_neg].
  set (ap := slice buf' nl nl).
  assert (Hap : limbs ap /\ length ap = nl) by (split; [apply slice_limbs; exact P1|apply slice_length; unfold max in *; lia]).
  destruct Hap as [Hapl Lap].
  assert (HR : 0 < Bp nl) by apply Bp_pos.
  assert (Hlt2 : lval ap + carry * Bp (length np) < 2 * lval np).
  { rewrite Lnp, ENp. fold ap in HV. assert (N * W < N * Bp nl) by nia. nia. }
  pose proof (mont_final_spec ap np carry Hapl Hnp ltac:(lia) P3 Hlt2) as Hfin. cbv zeta in Hfin.
  destruct Hfin as (F1 & F2 & F3 & F4). rewrite Lnp in F2, F3. rewrite ENp in F3, F4.
  set (res := mont_final ap np carry) in *.
  assert (Lres : length (splice (bn_buf rt1) 0 res) = length (bn_buf rt1)) by (apply splice_length; lia).
  apply hoare_bind_set; try rewrite length_setbn; try rewrite L2; try rewrite (getbn_setbn_same ret) by (rewrite L2; exact Vret); try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lres. split; [apply splice_limbs; assumption|]. repeat split; try assumption. }
  rewrite setbn_setbn_same. set (rt2 := mkBN (bn_d rt1) (splice (bn_buf rt1) 0 res) nl false (bn_flags rt1)). set (s4 := setbn ret rt2 s2).
  assert (L4 : length (st_bns s4) = length (st_bns s)) by (unfold s4; rewrite length_setbn; exact L2).
  assert (Eg4 : getbn r s4 = r2) by (unfold s4, s2; rewrite getbn_setbn_other by exact Nrr; apply getbn_setbn_same; exact Vr).
  assert (Lz : length (splice buf' nl (repeat 0 nl)) = length buf') by (apply splice_length; rewrite repeat_length; unfold max in *; lia).
  apply (hoare_update r (fun rb => bn_with_buf rb (splice (bn_buf rb) nl (repeat 0 nl)))); try rewrite L4; try rewrite Eg4; try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [r2 bn_with_buf bn_buf bn_top bn_flags]. rewrite Lz, P2, Lbuf.
    split; [apply splice_limbs; [exact P1|apply limbs_repeat; exact limb_0]|]. repeat split; try assumption; try (unfold max in *; lia). }
  split.
  - unfold s4, s2. eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [eapply keeps_trans; [apply keeps_setbn|apply keeps_setbn]|apply keeps_setbn]].
    intros x Hin _. cbn [app] in Hin. destruct Hin as [E|[E|[E|[]]]]; subst x; cbn; auto.
  - cbv zeta. rewrite getbn_setbn_other by (apply ndiff_sym; exact Nrr). unfold s4. rewrite getbn_setbn_same by (rewrite L2; exact Vret).
    unfold bn_mag at 1 2 3. cbn [rt2 bn_top bn_buf bn_neg]. rewrite firstn_splice_0 by lia.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact F4|].

    assert (Eres : (lval res) mod N = (lval ap + carry * Bp nl) mod N).
    { rewrite F3. destruct (Z.leb_spec N (lval ap + carry * Bp nl)) as [Hge|Hlt].
      - replace (lval ap + carry * Bp nl) with ((lval ap + carry * Bp nl - N) + 1 * N) at 2 by lia. rewrite Z.mod_add by lia. reflexivity.
      - destruct P3 as [-> | ->]; [rewrite Z.mul_0_l, Z.add_0_r; reflexivity|].

        exfalso. pose proof (lval_nonneg ap Hapl). pose proof (lval_bound np Hnp) as Bn. rewrite Lnp, ENp in Bn. lia. }
    rewrite Zmult_mod, Eres, <- Zmult_mod. fold ap in HV. rewrite HV. fold T.
    rewrite (Z.mul_comm N W), Z.mod_add by lia. reflexivity.
Qed.

Definition mul_mont_pre (rr ra rb : bnref) (s : ST) (N : Z) (nl : nat) : Prop :=
  live rr s /\ live ra s /\ live rb s /\ ndiff rr ROne /\ ndiff rr RMontN /\ ndiff rr RMontRR /\
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 2 <= BG_POOL)%nat /\
  (bn_top (getbn ra s) + bn_top (getbn rb s) <= 2 * nl)%nat /\ (bn_top (getbn ra s) <= 127)%nat /\ (bn_top (getbn rb s) <= 127)%nat /\
  bn_neg (getbn ra s) = false /\ bn_neg (getbn rb s) = false /\
  bn_mag (getbn ra s) * bn_mag (getbn rb s) < N * Bp nl.

Definition mont_res (N : Z) (nl : nat) (T : Z) (x : BN) : Prop :=
  bn_top x = nl /\ bn_neg x = false /\ 0 <= bn_mag x < N /\ (bn_mag x * Bp nl) mod N = T mod N.

Lemma bn_mul_mont_fixed_top_spec : forall rr ra rb F s N nl,
  mont_ok s N nl -> mul_mont_pre rr ra rb s N nl ->
  hoare F s (bn_mul_mont_fixed_top ops rr ra rb) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\ mont_ok s' N nl /\
     mont_res N nl (bn_mag (getbn ra s) * bn_mag (getbn rb s)) (getbn rr s')).
Proof.
  intros rr ra rb F s N nl Hm (Lr & La & Lb & Nr1 & NrN & NrRR & Hdepth & Hpool & Htops & Hal & Hbl & Hna & Hnb & HT).
  unfold bn_mul_mont_fixed_top. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, La, Lb. fold u in Lr, La, Lb.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *.
  apply hoare_bind_get. apply hoare_bind_get. apply hoare_bind_get. fold a b.
  pose proof Hm as Hm'. unfold mont_ok in Hm'. cbv zeta in Hm'. destruct Hm' as (Etn & Hnl & _). rewrite Etn.
  destruct (Nat.ltb_spec (2 * nl) (bn_top a + bn_top b)) as [|_]; [lia|].
  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros t s1 Hs1 (Et & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Et, Eu1.
  pose proof (inner_get u t s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Et; unfold RPool; lia)) as I1.
  pose proof (inner_trans _ _ _ _ _ _ I0 I1) as I01. cbn [app] in I01.
  assert (G1 : forall x, (x < NFIX + u)%nat -> getbn x s1 = getbn x s) by (intros x Hx; apply (inner_get_slot _ _ _ _ x I01 Hx); intros []).
  assert (Lt1 : live t s1) by (unfold live; rewrite Eu1, Et; unfold RPool; lia).
  assert (Hl1 : forall x, (x < NFIX + u)%nat -> live x s1) by (intros x Hx; unfold live; rewrite Eu1; lia).
  assert (Ntx : forall x, (x < NFIX + u)%nat -> ndiff t x) by (intros x Hx; rewrite Et; unfold ndiff, RPool; lia).
  assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).

  eapply hoare_bind with (R := fun _ s2 => keeps (S u) [t] s1 s2 /\ bn_neg (getbn t s2) = false /\
        bn_mag (getbn t s2) = bn_mag a * bn_mag b /\ (bn_top (getbn t s2) <= 2 * nl)%nat).
  { destruct (Nat.eqb_spec ra rb) as [Eab|Nab].
    - eapply hoare_mono; [apply bn_sqr_fixed_top_spec; unfold sqr_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 ra La); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact La|]. split; [exact Nt1|]. split; [apply Ntx; exact La|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|exact Hal].
      + intros [] s2 _ (K2 & M2 & T2 & N2). rewrite Eu1 in K2. rewrite (G1 ra La) in M2, T2. fold a in M2, T2.
        split; [exact K2|]. split; [exact N2|]. split; [rewrite M2; unfold b; rewrite <- Eab; reflexivity|].
        rewrite T2. unfold b in Htops. rewrite <- Eab in Htops. fold a in Htops. lia.
    - eapply hoare_mono; [apply bn_mul_fixed_top_spec; unfold mul_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 ra La), (G1 rb Lb); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact La|]. split; [apply Hl1; exact Lb|]. split; [exact Nt1|].
        split; [apply Ntx; exact La|]. split; [apply Ntx; exact Lb|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; assumption.
      + intros [] s2 _ (K2 & M2 & T2 & N2). rewrite Eu1 in K2. rewrite (G1 ra La), (G1 rb Lb) in M2, T2, N2. fold a b in M2, T2, N2.
        split; [exact K2|]. split; [destruct N2 as [E|[_ E]]; [rewrite E, Hna, Hnb; reflexivity|exact E]|]. split; [exact M2|].
        rewrite T2. destruct ((bn_top a =? 0) || (bn_top b =? 0))%nat; lia. }
  intros [] s2 Hs2 (K2 & N2 & M2 & T2).
  pose proof (inner_of_keeps u _ _ _ _ K2 ltac:(lia)) as I2.
  assert (G2 : forall x, (x < NFIX + u)%nat -> getbn x s2 = getbn x s).
  { intros x Hx. rewrite (inner_get_slot _ _ _ _ x I2 Hx) by (intros [E|[]]; rewrite Et in E; unfold RPool in E; lia). apply G1. exact Hx. }
  assert (Hm2 : mont_ok s2 N nl).
  { unfold mont_ok in *. cbv zeta in *. rewrite (G2 RMontN) by (unfold RMontN, NFIX; lia). rewrite (G2 RMontRR) by (unfold RMontRR, NFIX; lia).
    destruct I2 as (_ & (_ & En2 & _) & _). destruct I01 as (_ & (_ & En1 & _) & _). rewrite En2, En1. exact Hm. }
  eapply hoare_bind.
  { apply (bn_from_montgomery_word_spec rr t F s2 N nl Hm2).
    - unfold from_mont_pre, live. rewrite (keeps_used _ _ _ _ K2), Eu1.
      split; [lia|]. split; [rewrite Et; unfold RPool; lia|]. split; [exact Nr1|]. split; [exact Nt1|].
      split; [unfold ndiff; apply ndiff_sym, Ntx; exact Lr|]. split; [exact NrN|]. split; [apply Ntx; unfold RMontN, NFIX; lia|]. split; assumption.
    - rewrite M2. exact HT. }
  intros [] s3 Hs3 (K3 & P3). rewrite (keeps_used _ _ _ _ K2), Eu1 in K3. rewrite M2 in P3.
  pose proof (inner_of_keeps u _ _ _ _ K3 ltac:(lia)) as I3.
  assert (Ef3 : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]).
  { rewrite (keeps_frames _ _ _ _ K3), (keeps_frames _ _ _ _ K2), Ef1. exact Ef0. }
  eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3|].
  intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4).
  pose proof (inner_bns_eq u s3 s4 Eb4 Sc4) as I4.
  assert (K4 : keeps u [rr] s s4).
  { apply keeps_of_inner; [|exact Eu4|exact Ef4].
    eapply inner_weaken; [|eapply inner_trans; [eapply inner_trans; [eapply inner_trans; [exact I01|exact I2]|exact I3]|exact I4]].
    intros r Hin Hr. cbn [app] in Hin. destruct Hin as [E|[E|[E|[]]]]; try (left; exact E); rewrite <- E, Et in Hr; unfold RPool in Hr; lia. }
  split; [exact K4|]. split.
  - apply (mont_ok_keeps u [rr] s s4 N nl K4); [intros [E|[]]; apply NrN; exact E|intros [E|[]]; apply NrRR; exact E|exact Hm].
  - assert (Eg : getbn rr s4 = getbn rr s3) by (unfold getbn; rewrite Eb4; reflexivity). rewrite Eg. exact P3.
Qed.

Definition mont_res_canon (N : Z) (nl : nat) (T : Z) (x : BN) : Prop :=
  bn_canon x /\ (bn_top x <= nl)%nat /\ bn_neg x = false /\ 0 <= bn_mag x < N /\ (bn_mag x * Bp nl) mod N = T mod N.

Lemma BN_mod_mul_montgomery_spec : forall rr ra rb F s N nl,
  mont_ok s N nl -> mul_mont_pre rr ra rb s N nl ->
  hoare F s (BN_mod_mul_montgomery ops rr ra rb) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\ mont_ok s' N nl /\
     mont_res_canon N nl (bn_mag (getbn ra s) * bn_mag (getbn rb s)) (getbn rr s')).
Proof.
  intros rr ra rb F s N nl Hm Hpre. pose proof Hpre as (Lr & _ & _ & Nr1 & NrN & NrRR & _). unfold BN_mod_mul_montgomery.
  eapply hoare_bind; [apply bn_mul_mont_fixed_top_spec; eassumption|].
  intros [] s1 Hs1 (K1 & Hm1 & (T1 & N1 & B1 & V1)).
  assert (Vr1 : (rr < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|eapply keeps_live; eassumption]).
  eapply hoare_mono; [apply correct_top_spec; [exact Vr1|exact Nr1]|].
  intros [] s2 _ (r2 & -> & ->).
  assert (K2 : keeps (gx_used (st_ctx s)) [rr] s (setbn rr (bn_correct_top_pure (getbn rr s1)) s1)).
  { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
    intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; exact Hin. }
  split; [exact K2|]. split.
  - apply (mont_ok_keeps _ [rr] s _ N nl K2); [intros [E|[]]; apply NrN; exact E|intros [E|[]]; apply NrRR; exact E|exact Hm].
  - rewrite getbn_setbn_same by exact Vr1.
    destruct (bg_correct_top_ok (getbn rr s1) (st_wf_ok rr s1 Hs1 Vr1 Nr1)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    unfold mont_res_canon. rewrite C3, C7, N1. split; [exact C2|]. split; [lia|]. split; [reflexivity|]. split; assumption.
Qed.

Lemma to_mont_pre_ok : forall rr ra (s : ST) N nl, mont_ok s N nl ->
  live rr s -> live ra s -> ndiff rr ROne -> ndiff rr RMontN -> ndiff rr RMontRR ->
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 2 <= BG_POOL)%nat ->
  (bn_top (getbn ra s) <= nl)%nat -> bn_neg (getbn ra s) = false -> bn_mag (getbn ra s) < Bp nl ->
  0 <= bn_mag (getbn ra s) ->
  mul_mont_pre rr ra RMontRR s N nl.
Proof.
  intros rr ra s N nl Hm Lr La N1 N2 N3 Hd Hp Ht Hn Hlt H0. unfold mont_ok in Hm. cbv zeta in Hm.
  destruct Hm as (_ & Hnl & _ & _ & _ & HN1 & _ & _ & Trr & Nrr & Mrr).
  unfold mul_mont_pre. rewrite Trr, Nrr, Mrr.
  split; [exact Lr|]. split; [exact La|]. split; [unfold live, RMontRR, NFIX; lia|]. repeat split; try assumption; try lia.
  pose proof (Z.mod_pos_bound (Bp nl * Bp nl) N ltac:(lia)) as Hb. pose proof (Bp_pos nl). nia.
Qed.

Lemma bn_to_mont_value : forall N nl a x, 1 <= N -> Z.odd N = true ->
  (x * Bp nl) mod N = (a * ((Bp nl * Bp nl) mod N)) mod N -> x mod N = (a * Bp nl) mod N.
Proof.
  intros N nl a x HN Hodd H. apply (mont_cancel (Bp nl) N); [lia|rewrite Bp_pow2; apply gcd_pow2_odd; [lia|exact Hodd]|].
  rewrite H. rewrite Zmult_mod_idemp_r. f_equal. ring.
Qed.

Definition from_mont_top_pre (ret ra : bnref) (s : ST) (N : Z) (nl : nat) : Prop :=
  live ret s /\ live ra s /\ ndiff ret ROne /\ ndiff ret RMontN /\ ndiff ret RMontRR /\
  (length (gx_frames (st_ctx s)) + 1 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 1 <= BG_POOL)%nat /\
  (bn_top (getbn ra s) <= 2 * nl)%nat /\ bn_neg (getbn ra s) = false /\ bn_mag (getbn ra s) < N * Bp nl.

Lemma bn_from_mont_fixed_top_spec : forall ret ra F s N nl,
  mont_ok s N nl -> from_mont_top_pre ret ra s N nl ->
  hoare F s (bn_from_mont_fixed_top ops ret ra) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [ret] s s' /\ mont_ok s' N nl /\ mont_res N nl (bn_mag (getbn ra s)) (getbn ret s')).
Proof.
  intros ret ra F s N nl Hm (Lr & La & Nr1 & NrN & NrRR & Hdepth & Hpool & Htop & Hneg & HT).
  unfold bn_from_mont_fixed_top. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, La. fold u in Lr, La.
  set (a := getbn ra s) in *.
  pose proof Hm as Hm'. unfold mont_ok in Hm'. cbv zeta in Hm'. destruct Hm' as (Etn & Hnl & _).
  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros t s1 Hs1 (Et & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Et, Eu1.
  pose proof (inner_get u t s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Et; unfold RPool; lia)) as I1.
  pose proof (inner_trans _ _ _ _ _ _ I0 I1) as I01. cbn [app] in I01.
  assert (G1 : forall x, (x < NFIX + u)%nat -> getbn x s1 = getbn x s) by (intros x Hx; apply (inner_get_slot _ _ _ _ x I01 Hx); intros []).
  assert (Vt : (t < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|]; unfold live; rewrite Eu1, Et; unfold RPool; lia).
  assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).
  assert (Va1 : (ra < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|]; unfold live; rewrite Eu1; lia).
  eapply hoare_bind; [apply BN_copy_spec; assumption|].
  intros [] s2 Hs2 (t2 & -> & T2 & N2 & B2). rewrite (G1 ra La) in T2, N2, B2. fold a in T2, N2, B2.
  set (s2 := setbn t t2 s1) in *.
  pose proof (inner_setbn u t t2 s1) as I2. fold s2 in I2.
  assert (G2 : forall x, (x < NFIX + u)%nat -> getbn x s2 = getbn x s).
  { intros x Hx. unfold s2. rewrite getbn_setbn_other by (rewrite Et; unfold RPool; lia). apply G1. exact Hx. }
  assert (Hm2 : mont_ok s2 N nl).
  { unfold mont_ok in *. cbv zeta in *. rewrite (G2 RMontN) by (unfold RMontN, NFIX; lia). rewrite (G2 RMontRR) by (unfold RMontRR, NFIX; lia).
    destruct I01 as (_ & (_ & En1 & _) & _). change (st_n0 s2) with (st_n0 s1). rewrite En1. exact Hm. }
  assert (Eg2 : getbn t s2 = t2) by (unfold s2; apply getbn_setbn_same; exact Vt).
  assert (Em2 : bn_mag t2 = bn_mag a) by (apply mag_of_firstn_eq; assumption).
  eapply hoare_bind.
  { apply (bn_from_montgomery_word_spec ret t F s2 N nl Hm2).
    - unfold from_mont_pre, live. change (gx_used (st_ctx s2)) with (gx_used (st_ctx s1)). rewrite Eu1, Eg2, T2, N2.
      split; [lia|]. split; [rewrite Et; unfold RPool; lia|]. split; [exact Nr1|]. split; [exact Nt1|].
      split; [rewrite Et; unfold ndiff, RPool; lia|]. split; [exact NrN|]. split; [rewrite Et; unfold ndiff, RPool, RMontN, NFIX; lia|]. split; assumption.
    - rewrite Eg2, Em2. exact HT. }
  intros [] s3 Hs3 (K3 & P3). change (gx_used (st_ctx s2)) with (gx_used (st_ctx s1)) in K3. rewrite Eu1 in K3. rewrite Eg2, Em2 in P3.
  pose proof (inner_of_keeps u _ _ _ _ K3 ltac:(lia)) as I3.
  assert (Ef3 : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]).
  { rewrite (keeps_frames _ _ _ _ K3). change (gx_frames (st_ctx s2)) with (gx_frames (st_ctx s1)). rewrite Ef1. exact Ef0. }
  eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3|].
  intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4).
  pose proof (inner_bns_eq u s3 s4 Eb4 Sc4) as I4.
  assert (K4 : keeps u [ret] s s4).
  { apply keeps_of_inner; [|exact Eu4|exact Ef4].
    eapply inner_weaken; [|eapply inner_trans; [eapply inner_trans; [eapply inner_trans; [exact I01|exact I2]|exact I3]|exact I4]].
    intros r Hin Hr. cbn [app] in Hin. destruct Hin as [E|[E|[E|[]]]]; try (left; exact E); rewrite <- E, Et in Hr; unfold RPool in Hr; lia. }
  split; [exact K4|]. split.
  - apply (mont_ok_keeps u [ret] s s4 N nl K4); [intros [E|[]]; apply NrN; exact E|intros [E|[]]; apply NrRR; exact E|exact Hm].
  - assert (Eg : getbn ret s4 = getbn ret s3) by (unfold getbn; rewrite Eb4; reflexivity). rewrite Eg. exact P3.
Qed.

Lemma BN_from_montgomery_spec : forall ret ra F s N nl,
  mont_ok s N nl -> from_mont_top_pre ret ra s N nl ->
  hoare F s (BN_from_montgomery ops ret ra) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [ret] s s' /\ mont_ok s' N nl /\ mont_res_canon N nl (bn_mag (getbn ra s)) (getbn ret s')).
Proof.
  intros ret ra F s N nl Hm Hpre. pose proof Hpre as (Lr & _ & Nr1 & NrN & NrRR & _). unfold BN_from_montgomery.
  eapply hoare_bind; [apply bn_from_mont_fixed_top_spec; eassumption|].
  intros [] s1 Hs1 (K1 & Hm1 & (T1 & N1 & B1 & V1)).
  assert (Vr1 : (ret < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|eapply keeps_live; eassumption]).
  eapply hoare_mono; [apply correct_top_spec; [exact Vr1|exact Nr1]|].
  intros [] s2 _ (r2 & -> & ->).
  assert (K2 : keeps (gx_used (st_ctx s)) [ret] s (setbn ret (bn_correct_top_pure (getbn ret s1)) s1)).
  { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
    intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; exact Hin. }
  split; [exact K2|]. split.
  - apply (mont_ok_keeps _ [ret] s _ N nl K2); [intros [E|[]]; apply NrN; exact E|intros [E|[]]; apply NrRR; exact E|exact Hm].
  - rewrite getbn_setbn_same by exact Vr1.
    destruct (bg_correct_top_ok (getbn ret s1) (st_wf_ok ret s1 Hs1 Vr1 Nr1)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    unfold mont_res_canon. rewrite C3, C7, N1. split; [exact C2|]. split; [lia|]. split; [reflexivity|]. split; assumption.
Qed.

End MontSpec.
