(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory Zpow_facts.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgExp BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory BgMontSpec BgRecpSpec BgInvSpec BgMontSpec2
  BgCtxSpec BgExpLoops.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mod_mod_mul : forall x y N, 0 < N -> ((x mod N) * (y mod N)) mod N = (x * y) mod N.
Proof. intros x y N HN. rewrite <- Z.mul_mod by lia. reflexivity. Qed.

Lemma pow_mod_base : forall a p N, 0 < N -> 0 <= p -> ((a mod N) ^ p) mod N = (a ^ p) mod N.
Proof. intros a p N HN Hp. symmetry. apply Zpower_mod. lia. Qed.

Section ExpSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Definition exp_post (A P M : Z) (r : BN) : Prop := bn_canon r /\ bn_neg r = false /\ bn_mag r = (A ^ P) mod M.

Lemma inner_Fr_weaken : forall u u' o o' (s s' : ST),
  (u' <= u)%nat -> (forall r, In r o -> (r < NFIX + u')%nat -> In r o') -> inner u o s s' -> inner u' o' s s'.
Proof. intros u u' o o' s s' Hu Ho (A & B & C). split; [exact A|]. split; [exact B|]. eapply slots_same_weaken; eassumption. Qed.

Lemma inner_Fr_slot : forall u o (s s' : ST) r, inner u o s s' -> (r < NFIX + u)%nat -> ~ In r o -> ~ In r [] -> getbn r s' = getbn r s.
Proof. intros u o s s' r H Hr Hn _. exact (inner_get_slot u o s s' r H Hr Hn). Qed.

Lemma inner_Fr_len : forall u o (s s' : ST), inner u o s s' -> (length (st_bns s) <= length (st_bns s'))%nat.
Proof. intros u o s s' (A & _ & _). exact A. Qed.

Section Simple.
Variable rm : bnref.
Variable m0 : BN.

Definition InvS (s : ST) : Prop := getbn rm s = m0.
Definition RepS (x : Z) (b : BN) : Prop :=
  bn_canon b /\ bn_neg b = false /\ bn_mag b = x mod bn_mag m0 /\ (bn_top b <= bn_top m0)%nat.
Definition rfreeS (r : bnref) : Prop := ndiff r rm.
Definition mulS (r a b : bnref) : BMu unit := BN_mod_mul ops r a b rm.

Hypothesis Hm0 : bn_norm m0 /\ (1 <= bn_top m0 <= 64)%nat /\ (rm < NFIX)%nat.

Lemma InvS_get : forall a s s', InvS s -> scal_same s s' -> (forall r, r <> a -> getbn r s' = getbn r s) ->
  (NFIX + gx_used (st_ctx s) <= a)%nat -> InvS s'.
Proof. intros a s s' E _ H Ha. unfold InvS in *. rewrite H; [exact E|]. destruct Hm0 as (_ & _ & Hr). intros ->. lia. Qed.

Lemma rfreeS_pool : forall j, rfreeS (RPool j).
Proof. intros j. unfold rfreeS, ndiff, RPool. destruct Hm0 as (_ & _ & Hr). lia. Qed.

Lemma mulS_ok : 0 < bn_mag m0 -> forall u r a b F s x y,
  InvS s -> (u <= gx_used (st_ctx s))%nat ->
  live r s -> live a s -> live b s -> ndiff r ROne -> rfreeS r ->
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 5 <= BG_POOL)%nat ->
  RepS x (getbn a s) -> RepS y (getbn b s) ->
  hoare F s (mulS r a b) (fun _ s' => inner u [r] s s' /\ ctx_keep s s' /\ InvS s' /\ RepS (x * y) (getbn r s')).
Proof.
  intros HM u r a b F s x y HI Hu Lr La Lb Nr Rr Hd Hp (Cx & Nx & Mx & Tx) (Cy & Ny & My & Ty). unfold mulS.
  destruct Hm0 as (Nm & Tm & Hrm). unfold InvS in HI.
  eapply hoare_mono.
  { apply BN_mod_mul_spec. unfold mod_mul_pre. rewrite HI.
    split; [exact Lr|]. split; [exact La|]. split; [exact Lb|]. split; [unfold live; lia|]. split; [exact Nr|]. split; [exact Rr|].
    split; [exact Hd|]. split; [exact Hp|]. split; [exact Nm|]. split; [lia|]. split; [unfold BG_DMAX; lia|].
    split; [lia|]. split; [lia|]. split; [exact Nx|exact Ny]. }
  intros [] s' _ (K & (C1 & N1 & M1 & T1)). rewrite HI in M1, T1.
  split; [eapply inner_of_keeps; [exact K|exact Hu]|]. split; [destruct K as [[CK _] _]; exact CK|]. split.
  - unfold InvS. rewrite <- HI. apply (keeps_get _ _ _ _ rm K); [lia|]. intros [E|[]]. apply Rr. exact E.
  - unfold RepS. split; [exact C1|]. split; [exact N1|]. split; [|exact T1]. rewrite M1, Mx, My. apply mod_mod_mul. exact HM.
Qed.

Definition kitS (HM : 0 < bn_mag m0) : exp_kit :=
  mkKit mulS InvS RepS rfreeS [] inner 2 5
        inner_refl inner_trans inner_Fr_weaken inner_Fr_slot inner_Fr_len inner_get InvS_get rfreeS_pool
        (fun q (H : In q []) => match H with end) (mulS_ok HM).

End Simple.

Section Recp.
Variables (N nb : Z) (tN : nat).

Definition InvR (s : ST) : Prop := recp_ok s N nb /\ recp_st s N nb /\ bn_top (getbn RRecpN s) = tN.
Definition RepR (x : Z) (b : BN) : Prop := bn_canon b /\ bn_neg b = false /\ bn_mag b = x mod N /\ (bn_top b <= tN)%nat.
Definition rfreeR (r : bnref) : Prop := ndiff r RRecpN /\ ndiff r RRecpNr.
Definition FrR (u : nat) (o : list bnref) (s s' : ST) : Prop :=
  (length (st_bns s) <= length (st_bns s'))%nat /\ slots_same u (RRecpNr :: o) s s' /\
  st_ri s' = st_ri s /\ st_n0 s' = st_n0 s /\ st_rbits s' = st_rbits s.
Definition mulR (r a b : bnref) : BMu unit := BN_mod_mul_reciprocal ops r a b.

Lemma FrR_refl : forall u o s, FrR u o s s.
Proof. intros. unfold FrR. split; [lia|]. split; [apply slots_same_refl|]. repeat split; reflexivity. Qed.

Lemma FrR_trans : forall u o1 o2 s s1 s2, FrR u o1 s s1 -> FrR u o2 s1 s2 -> FrR u (o1 ++ o2) s s2.
Proof.
  intros u o1 o2 s s1 s2 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold FrR. split; [lia|]. split.
  - intros r Hr Hn. rewrite (B2 r Hr), (A2 r Hr); [reflexivity| |]; intros Hin; apply Hn; cbn in Hin |- *; rewrite in_app_iff; tauto.
  - rewrite B3, B4, B5. auto.
Qed.

Lemma FrR_weaken : forall u u' o o' s s',
  (u' <= u)%nat -> (forall r, In r o -> (r < NFIX + u')%nat -> In r o') -> FrR u o s s' -> FrR u' o' s s'.
Proof.
  intros u u' o o' s s' Hu Ho (A1 & A2 & A3). unfold FrR. split; [exact A1|]. split; [|exact A3].
  intros r Hr Hn. apply A2; [lia|]. intros [E|Hin]; apply Hn; [left; exact E|right; apply Ho; assumption].
Qed.

Lemma FrR_slot : forall u o s s' r, FrR u o s s' -> (r < NFIX + u)%nat -> ~ In r o -> ~ In r [RRecpNr] -> getbn r s' = getbn r s.
Proof. intros u o s s' r (_ & A2 & _) Hr Hn Hw. apply A2; [exact Hr|]. intros [E|Hin]; [apply Hw; left; exact E|apply Hn; exact Hin]. Qed.

Lemma FrR_len : forall u o s s', FrR u o s s' -> (length (st_bns s) <= length (st_bns s'))%nat.
Proof. intros u o s s' (A & _). exact A. Qed.

Lemma FrR_get : forall u a s s', (length (st_bns s) <= length (st_bns s'))%nat -> scal_same s s' ->
  (forall r, r <> a -> getbn r s' = getbn r s) -> (NFIX + u <= a)%nat -> FrR u [] s s'.
Proof.
  intros u a s s' L (S1 & S2 & S3 & S4) H Ha. unfold FrR. split; [exact L|]. split; [|auto].
  intros r Hr _. apply H. lia.
Qed.

Lemma InvR_get : forall a s s', InvR s -> scal_same s s' -> (forall r, r <> a -> getbn r s' = getbn r s) ->
  (NFIX + gx_used (st_ctx s) <= a)%nat -> InvR s'.
Proof.
  intros a s s' (A & B & C) (S1 & S2 & S3 & S4) H Ha. unfold InvR, recp_ok, recp_st in *. cbv zeta in *.
  rewrite !H by (unfold RRecpN, RRecpNr, NFIX in *; lia). rewrite S3, S4. auto.
Qed.

Lemma rfreeR_pool : forall j, rfreeR (RPool j).
Proof. intros j. unfold rfreeR, ndiff, RPool, RRecpN, RRecpNr, NFIX. lia. Qed.

Lemma wrR_low : forall q, In q [RRecpNr] -> (q < NFIX)%nat.
Proof. intros q [<-|[]]. unfold RRecpNr, NFIX. lia. Qed.

Lemma mulR_ok : forall u r a b F s x y,
  InvR s -> (u <= gx_used (st_ctx s))%nat ->
  live r s -> live a s -> live b s -> ndiff r ROne -> rfreeR r ->
  (length (gx_frames (st_ctx s)) + 4 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 9 <= BG_POOL)%nat ->
  RepR x (getbn a s) -> RepR y (getbn b s) ->
  hoare F s (mulR r a b) (fun _ s' => FrR u [r] s s' /\ ctx_keep s s' /\ InvR s' /\ RepR (x * y) (getbn r s')).
Proof.
  intros u r a b F s x y (Hok & Hst & Ht) Hu Lr La Lb Nr [RrN RrNr] Hd Hp (Cx & Nx & Mx & Tx) (Cy & Ny & My & Ty). unfold mulR.
  pose proof Hok as (Nn & Tn & Negn & MagN & Ebits & Hnb & HNb). cbv zeta in Nn, Tn, Negn, MagN.
  assert (HN : 0 < N) by (assert (0 < 2 ^ (nb - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
  pose proof (Z.mod_pos_bound x N HN) as Bx. pose proof (Z.mod_pos_bound y N HN) as By.
  eapply hoare_mono.
  { apply (BN_mod_mul_reciprocal_spec r a b F s N nb Hok Hst). unfold mmr_pre. rewrite Nx, Ny, Mx, My.
    split; [exact Lr|]. split; [exact La|]. split; [exact Lb|]. split; [exact Nr|]. split; [exact RrN|]. split; [exact RrNr|].
    split; [exact Hd|]. split; [exact Hp|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. lia. }
  intros [] s' _ (K & Hok' & Hst' & (C1 & N1 & M1 & T1)). rewrite Ht in T1. destruct K as [[(KL & KU & KF) KS] (K1 & K2 & K3)].
  split; [|split; [split; [exact KL|split; assumption]|split]].
  - unfold FrR. split; [exact KL|]. split; [|auto]. eapply slots_same_weaken; [exact Hu| |exact KS]. intros q Hq _. exact Hq.
  - unfold InvR. split; [exact Hok'|]. split; [exact Hst'|]. rewrite (KS RRecpN); [exact Ht|unfold RRecpN, NFIX; lia|].
    intros [E|[E|[]]]; [unfold RRecpNr, RRecpN in E; lia|apply RrN; exact E].
  - unfold RepR. split; [exact C1|]. split; [exact N1|]. split; [|exact T1]. rewrite M1, Mx, My. apply mod_mod_mul. exact HN.
Qed.

Definition kitR : exp_kit :=
  mkKit mulR InvR RepR rfreeR [RRecpNr] FrR 4 9
        FrR_refl FrR_trans FrR_weaken FrR_slot FrR_len FrR_get InvR_get rfreeR_pool wrR_low mulR_ok.

End Recp.

Section Mont.
Variables (N : Z) (nl : nat).

Definition InvM (s : ST) : Prop := mont_ok s N nl.
Definition RepM (x : Z) (b : BN) : Prop :=
  bn_top b = nl /\ bn_neg b = false /\ 0 <= bn_mag b < N /\ bn_mag b = (x * Bp nl) mod N.
Definition rfreeM (r : bnref) : Prop := ndiff r RMontN /\ ndiff r RMontRR.
Definition mulM (r a b : bnref) : BMu unit := bn_mul_mont_fixed_top ops r a b.

Lemma InvM_get : forall a s s', InvM s -> scal_same s s' -> (forall r, r <> a -> getbn r s' = getbn r s) ->
  (NFIX + gx_used (st_ctx s) <= a)%nat -> InvM s'.
Proof.
  intros a s s' H (S1 & S2 & S3 & S4) E Ha. unfold InvM, mont_ok in *. cbv zeta in *.
  rewrite !E by (unfold RMontN, RMontRR, NFIX in *; lia). rewrite S2. exact H.
Qed.

Lemma rfreeM_pool : forall j, rfreeM (RPool j).
Proof. intros j. unfold rfreeM, ndiff, RPool, RMontN, RMontRR, NFIX. lia. Qed.

Lemma mont_rep_mul : forall x y ma mb z, 0 < N -> Z.odd N = true ->
  ma = (x * Bp nl) mod N -> mb = (y * Bp nl) mod N -> (z * Bp nl) mod N = (ma * mb) mod N -> 0 <= z < N ->
  z = (x * y * Bp nl) mod N.
Proof.
  intros x y ma mb z HN Hodd Ea Eb Ez Hz. rewrite <- (Z.mod_small z N) by lia.
  apply (mont_cancel (Bp nl) N); [lia|rewrite Bp_pow2; apply gcd_pow2_odd; [lia|exact Hodd]|].
  rewrite Ez, Ea, Eb. rewrite mod_mod_mul by lia. f_equal. ring.
Qed.

Lemma mulM_ok : forall u r a b F s x y,
  InvM s -> (u <= gx_used (st_ctx s))%nat ->
  live r s -> live a s -> live b s -> ndiff r ROne -> rfreeM r ->
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 2 <= BG_POOL)%nat ->
  RepM x (getbn a s) -> RepM y (getbn b s) ->
  hoare F s (mulM r a b) (fun _ s' => inner u [r] s s' /\ ctx_keep s s' /\ InvM s' /\ RepM (x * y) (getbn r s')).
Proof.
  intros u r a b F s x y HI Hu Lr La Lb Nr [RrN RrRR] Hd Hp (Tx & Nx & Bx & Mx) (Ty & Ny & By & My). unfold mulM.
  apply hoare_wf. intros Hs. pose proof HI as HI'. unfold InvM, mont_ok in HI'. cbv zeta in HI'.
  destruct HI' as (Etn & Hnl & Enn & EmN & HoddN & HN1 & _).
  assert (VN : (RMontN < length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; unfold RMontN, NFIX; lia).
  pose proof (okv_mag_lt _ (st_wf_okv RMontN s Hs VN)) as HNR. rewrite EmN, Etn in HNR.
  eapply hoare_mono.
  { apply (bn_mul_mont_fixed_top_spec r a b F s N nl HI). unfold mul_mont_pre. rewrite Tx, Ty, Nx, Ny.
    split; [exact Lr|]. split; [exact La|]. split; [exact Lb|]. split; [exact Nr|]. split; [exact RrN|]. split; [exact RrRR|].
    split; [exact Hd|]. split; [exact Hp|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    assert (H1 : bn_mag (getbn a s) * bn_mag (getbn b s) <= bn_mag (getbn a s) * N) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (HN0 : 0 < N) by lia.
    assert (H2 : bn_mag (getbn a s) * N < Bp nl * N) by (apply (proj1 (Z.mul_lt_mono_pos_r N _ _ HN0)); lia). lia. }
  intros [] s' _ (K & HI1 & (T1 & N1 & B1 & V1)).
  split; [eapply inner_of_keeps; [exact K|exact Hu]|]. split; [destruct K as [[CK _] _]; exact CK|]. split; [exact HI1|].
  unfold RepM. split; [exact T1|]. split; [exact N1|]. split; [exact B1|].
  apply (mont_rep_mul x y (bn_mag (getbn a s)) (bn_mag (getbn b s))); try assumption. lia.
Qed.

Definition kitM : exp_kit :=
  mkKit mulM InvM RepM rfreeM [] inner 2 2
        inner_refl inner_trans inner_Fr_weaken inner_Fr_slot inner_Fr_len inner_get InvM_get rfreeM_pool
        (fun q (H : In q []) => match H with end) mulM_ok.

End Mont.

Lemma any_consttime_spec : forall l F s,
  (forall r, In r l -> (r < length (st_bns s))%nat) ->
  hoare F s (any_consttime ops l) (fun b s' => s' = s /\ b = false).
Proof.
  induction l as [|r l IH]; intros F s Hl; cbn [any_consttime fold_right].
  - apply hoare_ret. auto.
  - apply hoare_wf. intros Hs. apply hoare_bind_get.
    eapply hoare_bind; [apply IH; intros q Hq; apply Hl; right; exact Hq|].
    intros x s' _ (-> & ->). apply hoare_ret. rewrite (st_wf_no_flag r s _ Hs) by (try (apply Hl; left; reflexivity); left; reflexivity). auto.
Qed.

Lemma window_bits_range : forall b, 1 <= window_bits b <= 6.
Proof. intros b. unfold window_bits. repeat (destruct (Z.ltb _ _)); lia. Qed.

Lemma window_table_size : forall b, 2 ^ (window_bits b - 1) <= 32.
Proof.
  intros b. unfold window_bits. repeat (destruct (Z.ltb _ _)); cbn; lia.
Qed.

Lemma norm_mag_pos : forall b : BN, bg_okv b -> bn_norm b -> (1 <= bn_top b)%nat -> 0 < bn_mag b.
Proof. intros b Hb Hn Ht. pose proof (okv_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_pos (bn_top b - 1)). lia. Qed.

Lemma norm_mag0_top0 : forall b : BN, bg_okv b -> bn_norm b -> bn_mag b = 0 -> bn_top b = 0%nat.
Proof.
  intros b Hb Hn H0. destruct (Nat.eq_dec (bn_top b) 0) as [E|E]; [exact E|].
  pose proof (okv_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_pos (bn_top b - 1)). lia.
Qed.

Lemma abs_is_word_1 : forall b : BN, bg_okv b -> bn_norm b -> abs_is_word_pure b 1 = (bn_mag b =? 1).
Proof.
  intros b Hb Hn. unfold abs_is_word_pure. cbn [Z.eqb andb orb]. rewrite orb_false_r.
  destruct (Nat.eqb_spec (bn_top b) 1) as [E|E].
  - cbn [andb]. unfold bn_mag. rewrite E. destruct (bn_buf b) as [|x l] eqn:Eb; cbn [firstn nth lval]; [|rewrite Z.mul_0_r, Z.add_0_r]; reflexivity.
  - cbn [andb]. symmetry. apply Z.eqb_neq. intros H1.
    destruct (Nat.eq_dec (bn_top b) 0) as [E0|E0]; [rewrite (bn_mag_top0 b E0) in H1; lia|].
    pose proof (okv_mag_ge b Hb Hn ltac:(lia)) as Hge. rewrite H1 in Hge.
    assert (2 <= bn_top b)%nat by lia. pose proof (Bp_pos (bn_top b - 2)) as Hp.
    replace (bn_top b - 1)%nat with (S (bn_top b - 2)) in Hge by lia. rewrite Bp_S in Hge. unfold BW in Hge. lia.
Qed.

Lemma exp_bits0_spec : forall rr rm F s A,
  live rr s -> (rm < length (st_bns s))%nat -> ndiff rr ROne -> ndiff rr rm -> bn_norm (getbn rm s) -> (1 <= bn_top (getbn rm s))%nat ->
  hoare F s (exp_bits0 ops rr rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\ exp_post A 0 (bn_mag (getbn rm s)) (getbn rr s') /\ (bn_top (getbn rr s') <= 1)%nat).
Proof.
  intros rr rm F s A Lr Vm Nr1 Nrm Nm Tm. apply hoare_wf. intros Hs. unfold exp_bits0. apply hoare_bind_get.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (st_wf_okv rm s Hs Vm) as Okm.
  pose proof (norm_mag_pos _ Okm Nm Tm) as HM.
  rewrite (abs_is_word_1 _ Okm Nm). unfold exp_post. rewrite Z.pow_0_r. destruct (Z.eqb_spec (bn_mag (getbn rm s)) 1) as [E1|E1].
  - eapply hoare_mono; [apply BN_zero_spec; [exact Vr|exact Nr1]|].
    intros [] s' _ (b' & -> & T' & N'). rewrite getbn_setbn_same by exact Vr. split; [apply keeps_setbn|].
    rewrite E1, (bn_mag_top0 b' T'). cbn. split; [|lia]. split; [|split; [exact N'|reflexivity]].
    split; [left; exact T'|intros _; exact N'].
  - eapply hoare_mono; [apply BN_one_spec; [exact Vr|exact Nr1]|].
    intros [] s' _ (b' & -> & M' & C' & N' & T'). rewrite getbn_setbn_same by exact Vr. split; [apply keeps_setbn|].
    rewrite M', Z.mod_1_l by lia. split; [|exact T']. split; [exact C'|]. split; [exact N'|reflexivity].
Qed.

Definition modexp_pre (rr ra rp rm : bnref) (s : ST) (Dn Pn : nat) : Prop :=
  live rr s /\ live ra s /\ live rp s /\ live rm s /\ ndiff rr ROne /\ ndiff rr rm /\ ndiff rr rp /\
  (length (gx_frames (st_ctx s)) + Dn <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + Pn <= BG_POOL)%nat /\
  bn_norm (getbn rm s) /\ (1 <= bn_top (getbn rm s) <= 64)%nat /\
  bn_norm (getbn rp s) /\ (bn_top (getbn rp s) <= 64)%nat /\ (bn_top (getbn ra s) <= 64)%nat.

Lemma BN_mod_exp_simple_spec : forall rr ra rp rm F s,
  modexp_pre rr ra rp rm s 3 38 -> (rm < NFIX)%nat ->
  hoare F s (BN_mod_exp_simple ops rr ra rp rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     exp_post (bn_val (getbn ra s)) (bn_mag (getbn rp s)) (bn_mag (getbn rm s)) (getbn rr s') /\
     (bn_top (getbn rr s') <= bn_top (getbn rm s))%nat).
Proof.
  intros rr ra rp rm F s (Lr & La & Lp & Lm & Nr1 & Nrm & Nrp & Hdepth & Hpool & Nm & Tm & Np & Tp & Ta) Hrm.
  apply hoare_wf. intros Hs. unfold BN_mod_exp_simple. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va. pose proof (live_valid rp s Hs Lp) as Vp. pose proof (live_valid rm s Hs Lm) as Vm.
  unfold live in Lr, La, Lp, Lm. fold u in Lr, La, Lp, Lm.
  set (a := getbn ra s) in *. set (p := getbn rp s) in *. set (m := getbn rm s) in *.
  pose proof (st_wf_okv rm s Hs Vm) as Okm. pose proof (st_wf_okv rp s Hs Vp) as Okp. pose proof (st_wf_okv ra s Hs Va) as Oka. fold a in Oka. fold p in Okp. fold m in Okm.
  pose proof (norm_mag_pos _ Okm Nm ltac:(lia)) as HM. set (M := bn_mag m) in *. set (P := bn_mag p) in *.
  eapply hoare_bind; [apply any_consttime_spec; intros q [<-|[<-|[<-|[]]]]; assumption|]. intros ct s0 _ (-> & ->).
  destruct (Nat.eqb_spec rr rm) as [E|_]; [exfalso; apply Nrm; exact E|].
  eapply hoare_bind; [apply BN_num_bits_spec; exact Vp|]. intros bits s0 _ (-> & ->). fold p.
  pose proof (num_bits_pure_spec p Okp Np) as (B0 & B1 & B2 & B3). fold P in B1, B2.
  pose proof (okv_mag_nonneg p Okp) as HP0. fold P in HP0.
  destruct (Z.eqb_spec (num_bits_pure p) 0) as [Ez|Ez].
  {
    assert (P = 0) as EP by (destruct (Z.eq_dec P 0) as [|Hne]; [assumption|]; specialize (B2 ltac:(lia)); rewrite Ez in B2;
      change (2 ^ (0 - 1)) with 0 in B2; change (2 ^ 0) with 1 in B2; lia).
    rewrite EP. eapply hoare_mono; [apply (exp_bits0_spec rr rm F s (bn_val a)); [unfold live; lia|exact Vm|exact Nr1|exact Nrm|exact Nm|fold m; lia]|].
    intros [] s' _ (K & E & T). split; [exact K|]. split; [exact E|]. lia. }
  set (bits := num_bits_pure p) in *.
  assert (HP1 : 1 <= P) by (destruct (Z.eq_dec P 0) as [E0|]; [exfalso; apply Ez; apply B1; exact E0|lia]).
  specialize (B2 ltac:(lia)).
  pose proof (window_bits_range bits) as Hw. pose proof (window_table_size bits) as Hws. set (window := window_bits bits) in *.

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros d s1 Hs1 (Ed & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Ed, Eu1.
  pose proof (inner_get u d s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Ed; unfold RPool; lia)) as I1.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros v0 s2 Hs2 (Ev0 & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & Tv0 & Nv0). rewrite Eu1 in Ev0, Eu2.
  pose proof (inner_get u v0 s1 s2 Len2 Sc2 Oth2 ltac:(rewrite Ev0; unfold RPool; lia)) as I2.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) as I02. cbn [app] in I02.
  assert (G2 : forall z, (z < NFIX + u)%nat -> getbn z s2 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I02 Hz); intros []).
  assert (L2 : (length (st_bns s) <= length (st_bns s2))%nat) by (destruct I02 as (L & _); exact L).

  eapply hoare_bind.
  { apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite Eu2, Ef2, Ef1, Ef0, !G2, length_app by lia. cbn [length]. fold a m.
    split; [rewrite Ev0; unfold RPool; lia|]. split; [lia|]. split; [lia|]. split; [rewrite Ev0; unfold ndiff, RPool, ROne, NFIX; lia|].
    split; [rewrite Ev0; unfold ndiff, RPool; lia|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|].
    split; [exact Nm|]. split; [lia|]. unfold BG_DMAX. lia. }
  intros [] s3 Hs3 (K3 & X3). rewrite !G2 in X3 by lia. fold a m M in X3. rewrite Eu2 in K3.
  pose proof X3 as (Cx & Nx & Mx & Tx).
  assert (G3 : forall z, (z < NFIX + u)%nat -> getbn z s3 = getbn z s).
  { intros z Hz. rewrite (keeps_get _ _ _ _ z K3); [apply G2; exact Hz|lia|]. rewrite Ev0. unfold RPool. intros [E|[]]. lia. }
  pose proof (keeps_used _ _ _ _ K3) as Eu3. pose proof (keeps_frames _ _ _ _ K3) as Ef3. rewrite Eu2 in Eu3. rewrite Ef2, Ef1, Ef0 in Ef3.
  pose proof (inner_trans _ _ _ _ _ _ I02 (inner_of_keeps u _ _ _ _ K3 ltac:(lia))) as I03. cbn [app] in I03.
  apply hoare_bind_get.

  eapply hoare_bind with (R := fun _ s6 => inner u [v0; rr] s s6 /\ gx_frames (st_ctx s6) = gx_frames (st_ctx s) ++ [u] /\
                                       exp_post (bn_val a) P M (getbn rr s6) /\ (bn_top (getbn rr s6) <= bn_top m)%nat).
  { unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn v0 s3)) 0) as [Z0|Z0].
    -
      assert (Vr3 : (rr < length (st_bns s3))%nat) by (apply live_valid; [exact Hs3|unfold live; rewrite Eu3; lia]).
      eapply hoare_mono; [apply BN_zero_spec; [exact Vr3|exact Nr1]|].
      intros [] s4 _ (b4 & -> & T4 & N4). rewrite getbn_setbn_same, st_ctx_setbn by exact Vr3.
      split; [replace [v0; rr] with ([v0] ++ [rr]) by reflexivity; eapply inner_trans; [exact I03|apply inner_setbn]|].
      split; [exact Ef3|]. split; [|lia]. unfold exp_post. rewrite (bn_mag_top0 b4 T4).
      split; [split; [left; exact T4|intros _; exact N4]|]. split; [exact N4|].
      rewrite <- (pow_mod_base (bn_val a) P M) by lia. rewrite <- Mx, (bn_mag_top0 _ Z0), Z.pow_0_l by lia. reflexivity.
    -
      assert (HM2 : 2 <= M).
      { pose proof (Z.mod_pos_bound (bn_val a) M HM) as Hb. rewrite <- Mx in Hb.
        destruct (Z.eq_dec (bn_mag (getbn v0 s3)) 0) as [E0|E0]; [|lia]. exfalso. apply Z0.
        apply norm_mag0_top0; [|destruct Cx as [Hn _]; exact Hn|exact E0].
        apply (st_wf_okv v0 s3 Hs3). apply live_valid; [exact Hs3|unfold live; rewrite Eu3, Ev0; unfold RPool; lia]. }
      set (a0 := bn_val a mod M).
      assert (Ha0 : 0 <= a0 < M) by (unfold a0; apply Z.mod_pos_bound; exact HM).
      assert (KM : bn_norm m /\ (1 <= bn_top m <= 64)%nat /\ (rm < NFIX)%nat) by (split; [exact Nm|]; split; [exact Tm|exact Hrm]).
      eapply hoare_bind.
      { apply (exp_table_ok (kitS rm m KM HM) window v0 d F s3 a0); cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitS].
        - unfold InvS. apply G3. lia.
        - unfold live. rewrite Eu3, Ev0. unfold RPool. lia.
        - intros [].
        - unfold live. rewrite Eu3, Ed. unfold RPool. lia.
        - rewrite Ed. unfold ndiff, RPool, ROne, NFIX. lia.
        - unfold rfreeS. rewrite Ed. unfold ndiff, RPool. lia.
        - intros [].
        - rewrite Ev0, Ed. unfold RPool. lia.
        - unfold RepS. split; [exact Cx|]. split; [exact Nx|]. split; [|exact Tx]. rewrite Mx. unfold a0. rewrite Z.mod_mod by lia. reflexivity.
        - lia.
        - lia.
        - rewrite Ef3, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - rewrite Eu3. unfold BG_POOL in *. lia. }
      intros vals s4 Hs4 ((new & Evals & Hnew) & Lv & F4 & L4 & U4 & Fm4 & I4 & T4 & V4).
      cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitS] in F4, I4, T4, V4. rewrite Eu3 in U4, F4, Hnew. rewrite Ef3 in Fm4.
      destruct (Nat.eqb_spec rr rp) as [E|_]; [exfalso; apply Nrp; exact E|].
      assert (G4 : forall z, (z < NFIX + u)%nat -> getbn z s4 = getbn z s).
      { intros z Hz. rewrite (inner_get_slot _ _ _ _ z F4); [apply G3; exact Hz|lia|]. rewrite Ed. unfold RPool. intros [E|[]]. lia. }
      assert (Vr4 : (rr < length (st_bns s4))%nat) by (apply live_valid; [exact Hs4|unfold live; rewrite U4; lia]).
      assert (Hvals : forall v, In v vals -> (NFIX + u < v)%nat /\ (v < NFIX + (u + 2 + (Z.to_nat (2 ^ (window - 1)) - 1)))%nat).
      { intros v Hv. rewrite Evals in Hv. destruct Hv as [<-|Hv].
        - rewrite Ev0. unfold RPool. lia.
        - destruct (@In_nth bnref new v 0%nat Hv) as (i & Hi & <-). rewrite (Hnew i Hi). unfold RPool.
          rewrite Evals in Lv. cbn [length] in Lv. lia. }
      eapply hoare_bind; [apply BN_one_spec; [exact Vr4|exact Nr1]|].
      intros [] s5 Hs5 (b5 & -> & M5 & C5 & N5 & T5).
      set (u5 := (u + 2 + (Z.to_nat (2 ^ (window - 1)) - 1))%nat) in *.
      eapply hoare_mono.
      { apply (exp_window_loop_ok (kitS rm m KM HM) (Z.to_nat bits) u5 rp rr vals window (bits - 1) true F (setbn rr b5 s4) a0 P);
          cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitS]; try rewrite st_ctx_setbn; try rewrite length_setbn.
        - unfold InvS. rewrite getbn_setbn_other by exact Nrm. exact I4.
        - rewrite U4. lia.
        - unfold live. rewrite st_ctx_setbn, U4. lia.
        - exact Nr1.
        - exact Nrm.
        - intros [].
        - lia.
        - intros [].
        - intros E. apply Nrp. rewrite E. reflexivity.
        - pose proof I03 as (L03 & _ & _). lia.
        - intros v Hv. destruct (Hvals v Hv) as [H1 H2]. split; [exact H2|]. split; [intros ->; lia|intros []].
        - rewrite Fm4, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - rewrite U4. unfold BG_POOL in *. lia.
        - rewrite getbn_setbn_other by exact Nrp. rewrite G4 by lia. reflexivity.
        - lia.
        - lia.
        - lia.
        - exact Lv.
        - eapply (tab_frame (kitS rm m KM HM)); [exact T4| |cbn [ek_Fr kitS]; apply (inner_setbn u5)].
          cbn [ek_wr kitS]. intros v Hv. destruct (Hvals v Hv) as [H1 H2]. split; [exact H2|]. split; [intros [E|[]]; lia|intros []].
        - rewrite getbn_setbn_same by exact Vr4. replace (bits - 1 + 1) with bits by lia. rewrite (exp_top P bits) by lia.
          rewrite Z.pow_0_r. unfold RepS. split; [exact C5|]. split; [exact N5|]. split; [rewrite M5, Z.mod_1_l by lia; reflexivity|lia].
        - intros _. replace (bits - 1 + 1) with bits by lia. apply exp_top. lia. }
      intros [] s6 _ (F6 & C6 & I6 & R6). cbn [ek_Fr ek_Inv ek_Rep kitS] in F6, I6, R6. destruct C6 as (L6 & U6 & Fm6).
      rewrite st_ctx_setbn in U6, Fm6. destruct R6 as (C6' & N6 & M6 & T6).
      split; [|split; [rewrite Fm6; exact Fm4|split; [|exact T6]]].
      + eapply inner_Fr_weaken; [apply Nat.le_refl| |
          eapply inner_trans; [exact I03|eapply inner_trans; [eapply inner_Fr_weaken; [| |exact F4]; [lia|intros q Hq _; exact Hq]|
            eapply inner_trans; [apply inner_setbn|eapply inner_Fr_weaken; [| |exact F6]; [lia|intros q Hq _; exact Hq]]]]].
        intros q Hq Hlow. cbn [app] in Hq. rewrite Ed in Hq. unfold RPool in Hq.
        destruct Hq as [Hq|[Hq|[Hq|[Hq|[]]]]]; try (rewrite <- Hq in Hlow; lia); subst q; cbn; auto.
      + unfold exp_post. split; [exact C6'|]. split; [exact N6|]. rewrite M6. unfold a0. apply pow_mod_base; lia. }

  intros [] s6 Hs6 (I6 & Ef6 & X6 & T6).
  eapply hoare_mono; [apply (BN_CTX_end_spec F s6 (gx_frames (st_ctx s)) u); exact Ef6|].
  intros [] s7 _ (Eb7 & Sc7 & Eu7 & Ef7).
  assert (G7 : forall z, getbn z s7 = getbn z s6) by (intros z; unfold getbn; rewrite Eb7; reflexivity).
  rewrite G7. split; [|split; [exact X6|exact T6]].
  apply keeps_of_inner; [|rewrite Eu7; reflexivity|rewrite Ef7; reflexivity].
  eapply inner_Fr_weaken; [apply Nat.le_refl| |eapply inner_trans; [exact I6|apply (inner_bns_eq u s6 s7 Eb7 Sc7)]].
  intros q Hq Hlow. cbn [app] in Hq. rewrite Ev0 in Hq. unfold RPool in Hq. destruct Hq as [Hq|[Hq|[]]]; [lia|left; exact Hq].
Qed.

Lemma BN_RECP_CTX_set_spec : forall rd F s,
  live rd s -> ndiff rd RRecpN -> ndiff rd RRecpNr -> bn_norm (getbn rd s) -> bn_neg (getbn rd s) = false ->
  (1 <= bn_top (getbn rd s) <= 64)%nat ->
  hoare F s (BN_RECP_CTX_set ops rd) (fun _ s' =>
     keeps0 (gx_used (st_ctx s)) [RRecpN; RRecpNr] s s' /\ st_ri s' = st_ri s /\ st_n0 s' = st_n0 s /\ st_rshift s' = 0 /\
     recp_ok s' (bn_mag (getbn rd s)) (num_bits_pure (getbn rd s)) /\ recp_st s' (bn_mag (getbn rd s)) (num_bits_pure (getbn rd s)) /\
     bn_top (getbn RRecpN s') = bn_top (getbn rd s)).
Proof.
  intros rd F s Ld N1 N2 Nd Negd Td. apply hoare_wf. intros Hs. unfold BN_RECP_CTX_set. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rd s Hs Ld) as Vd. set (d := getbn rd s) in *.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  pose proof (st_wf_okv rd s Hs Vd) as Okd. fold d in Okd.
  apply hoare_bind_get. fold d. unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top d) 0) as [|_]; [lia|].
  eapply hoare_bind; [apply BN_copy_spec; [unfold RRecpN, NFIX in *; lia|unfold RRecpN, ROne; lia|exact Vd]|].
  intros [] s1 Hs1 (n1 & -> & T1 & Ng1 & P1). fold d in T1, Ng1, P1.
  eapply hoare_bind; [apply BN_zero_spec; [rewrite length_setbn; unfold RRecpNr, NFIX in *; lia|unfold RRecpNr, ROne; lia]|].
  intros [] s2 Hs2 (n2 & -> & T2 & Ng2).
  eapply hoare_bind; [apply BN_num_bits_spec; rewrite !length_setbn; exact Vd|]. intros nb s3 _ (-> & ->).
  rewrite !getbn_setbn_other by (apply ndiff_sym; first [exact N2|exact N1]). fold d.
  apply hoare_setrecp.
  assert (V1 : (RRecpN < length (st_bns s))%nat) by (unfold RRecpN, NFIX in *; lia).
  assert (V2 : (RRecpNr < length (st_bns s))%nat) by (unfold RRecpNr, NFIX in *; lia).
  assert (EN : getbn RRecpN (set_recp (num_bits_pure d) 0 (setbn RRecpNr n2 (setbn RRecpN n1 s))) = n1).
  { unfold getbn, set_recp. cbn [st_bns]. fold (getbn RRecpN (setbn RRecpNr n2 (setbn RRecpN n1 s))).
    rewrite getbn_setbn_other by (unfold RRecpNr, RRecpN; lia). apply getbn_setbn_same. exact V1. }
  assert (ENr : getbn RRecpNr (set_recp (num_bits_pure d) 0 (setbn RRecpNr n2 (setbn RRecpN n1 s))) = n2).
  { unfold getbn, set_recp. cbn [st_bns]. fold (getbn RRecpNr (setbn RRecpNr n2 (setbn RRecpN n1 s))).
    apply getbn_setbn_same. rewrite length_setbn. exact V2. }
  pose proof (mag_of_firstn_eq n1 d T1 P1) as M1. pose proof (norm_of_firstn_eq n1 d T1 P1 Nd) as Nn1.
  pose proof (norm_mag_pos d Okd Nd ltac:(lia)) as HM.
  pose proof (num_bits_pure_spec d Okd Nd) as (B0 & B1 & B2 & B3). specialize (B2 HM).
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [|split; [left; reflexivity|rewrite EN; exact T1]]]]]].
  - split; [split; [cbn; rewrite !list_set_length; lia|split; reflexivity]|].
    intros r Hr Hn. unfold getbn, set_recp. cbn [st_bns]. fold (getbn r (setbn RRecpNr n2 (setbn RRecpN n1 s))).
    rewrite !getbn_setbn_other; [reflexivity| |]; intros E; apply Hn; rewrite <- E; cbn; auto.
  - unfold recp_ok. rewrite EN. cbn [st_rbits set_recp]. rewrite M1, Ng1, Negd. split; [exact Nn1|]. split; [rewrite T1; exact Td|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact B2].
    destruct (Z.le_gt_cases 1 (num_bits_pure d)) as [|Hlt]; [assumption|]. exfalso.
    assert (num_bits_pure d = 0) as E0 by lia. rewrite E0 in B2. change (2 ^ 0) with 1 in B2. lia.
Qed.

Lemma FrR_of_keeps : forall u u' o (s s' : ST), keeps u' o s s' -> (u <= u')%nat -> FrR u o s s'.
Proof.
  intros u u' o s s' [[(L & _ & _) Sl] (S1 & S2 & S3 & S4)] Hu. unfold FrR. split; [exact L|]. split; [|auto].
  intros r Hr Hn. apply Sl; [lia|]. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma FrR_setbn : forall u r b (s : ST), FrR u [r] s (setbn r b s).
Proof.
  intros u r b s. unfold FrR. rewrite length_setbn. split; [lia|]. split; [|repeat split; reflexivity].
  intros q Hq Hn. apply getbn_setbn_other. intros ->. apply Hn. right. left. reflexivity.
Qed.

Lemma InvR_frame : forall N nb tN (s s' : ST), InvR N nb tN s ->
  getbn RRecpN s' = getbn RRecpN s -> getbn RRecpNr s' = getbn RRecpNr s -> st_rbits s' = st_rbits s -> st_rshift s' = st_rshift s ->
  InvR N nb tN s'.
Proof.
  intros N nb tN s s' (A & B & C) E1 E2 E3 E4. unfold InvR, recp_ok, recp_st in *. cbv zeta in *. rewrite E1, E2, E3, E4. auto.
Qed.

Definition refs5 (rr ra rp rm : bnref) : Prop := (rr < 5 /\ ra < 5 /\ rp < 5 /\ rm < 5)%nat.

Lemma BN_mod_exp_recp_spec : forall rr ra rp rm F s,
  modexp_pre rr ra rp rm s 5 42 -> refs5 rr ra rp rm -> recp_pristine s ->
  hoare F s (BN_mod_exp_recp ops rr ra rp rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     exp_post (bn_val (getbn ra s)) (bn_mag (getbn rp s)) (bn_mag (getbn rm s)) (getbn rr s') /\
     (bn_top (getbn rr s') <= bn_top (getbn rm s))%nat /\ recp_pristine s').
Proof.
  intros rr ra rp rm F s (Lr & La & Lp & Lm & Nr1 & Nrm & Nrp & Hdepth & Hpool & Nm & Tm & Np & Tp & Ta) (R1 & R2 & R3 & R4) Hpr.
  apply hoare_wf. intros Hs. unfold BN_mod_exp_recp. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va. pose proof (live_valid rp s Hs Lp) as Vp. pose proof (live_valid rm s Hs Lm) as Vm.
  unfold live in Lr, La, Lp, Lm. fold u in Lr, La, Lp, Lm.
  set (a := getbn ra s) in *. set (p := getbn rp s) in *. set (m := getbn rm s) in *.
  pose proof (st_wf_okv rm s Hs Vm) as Okm. pose proof (st_wf_okv rp s Hs Vp) as Okp. pose proof (st_wf_okv ra s Hs Va) as Oka. fold a in Oka. fold p in Okp. fold m in Okm.
  pose proof (norm_mag_pos _ Okm Nm ltac:(lia)) as HM. set (M := bn_mag m) in *. set (P := bn_mag p) in *.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  pose proof Hpr as (PrN & PrNr & Prb & Prs).
  eapply hoare_bind; [apply any_consttime_spec; intros q [<-|[<-|[<-|[]]]]; assumption|]. intros ct s0 _ (-> & ->).
  eapply hoare_bind; [apply BN_num_bits_spec; exact Vp|]. intros bits s0 _ (-> & ->). fold p.
  pose proof (num_bits_pure_spec p Okp Np) as (B0 & B1 & B2 & B3). fold P in B1, B2.
  pose proof (okv_mag_nonneg p Okp) as HP0. fold P in HP0.
  destruct (Z.eqb_spec (num_bits_pure p) 0) as [Ez|Ez].
  {
    assert (P = 0) as EP by (destruct (Z.eq_dec P 0) as [|Hne]; [assumption|]; specialize (B2 ltac:(lia)); rewrite Ez in B2;
      change (2 ^ (0 - 1)) with 0 in B2; change (2 ^ 0) with 1 in B2; lia).
    rewrite EP. eapply hoare_mono; [apply (exp_bits0_spec rr rm F s (bn_val a)); [unfold live; lia|exact Vm|exact Nr1|exact Nrm|exact Nm|fold m; lia]|].
    intros [] s' _ (K & E & T). split; [exact K|]. split; [exact E|]. split; [lia|].
    unfold recp_pristine. destruct K as [[_ Sl] (_ & _ & S3 & S4)]. rewrite S3, S4.
    rewrite !Sl by (first [unfold RRecpN, RRecpNr, NFIX; lia|intros [E'|[]]; unfold RRecpN, RRecpNr in E'; lia]). exact Hpr. }
  set (bits := num_bits_pure p) in *.
  assert (HP1 : 1 <= P) by (destruct (Z.eq_dec P 0) as [E0|]; [exfalso; apply Ez; apply B1; exact E0|lia]).
  specialize (B2 ltac:(lia)).
  pose proof (window_bits_range bits) as Hw. pose proof (window_table_size bits) as Hws. set (window := window_bits bits) in *.
  eapply hoare_bind; [apply BN_RECP_CTX_init_spec; exact Hpr|]. intros [] s0 _ ->.

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros aa s1 Hs1 (Eaa & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Eaa, Eu1.
  pose proof (inner_get u aa s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Eaa; unfold RPool; lia)) as I1.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros v0 s2 Hs2 (Ev0 & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & Tv0 & Nv0). rewrite Eu1 in Ev0, Eu2.
  pose proof (inner_get u v0 s1 s2 Len2 Sc2 Oth2 ltac:(rewrite Ev0; unfold RPool; lia)) as I2.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) as I02. cbn [app] in I02.
  assert (G2 : forall z, (z < NFIX + u)%nat -> getbn z s2 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I02 Hz); intros []).
  pose proof I02 as (L2 & Sc02 & _).
  assert (Ef2' : gx_frames (st_ctx s2) = gx_frames (st_ctx s) ++ [u]) by (rewrite Ef2, Ef1; exact Ef0).
  assert (V2 : forall z, (z < NFIX + S (S u))%nat -> (z < length (st_bns s2))%nat) by (intros z Hz; apply live_valid; [exact Hs2|unfold live; rewrite Eu2; exact Hz]).
  apply hoare_bind_get. rewrite (G2 rm Lm). fold m.

  eapply hoare_bind with (R := fun _ s4 => exists nb,
     (length (st_bns s) <= length (st_bns s4))%nat /\ slots_same u [RRecpN; RRecpNr] s s4 /\ st_ri s4 = st_ri s /\ st_n0 s4 = st_n0 s /\
     gx_used (st_ctx s4) = S (S u) /\ gx_frames (st_ctx s4) = gx_frames (st_ctx s) ++ [u] /\ InvR M nb (bn_top m) s4).
  { assert (POST : forall s3 rd, st_wf s3 -> (length (st_bns s) <= length (st_bns s3))%nat -> slots_same u [] s s3 -> scal_same s s3 ->
              gx_used (st_ctx s3) = S (S u) -> gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u] ->
              live rd s3 -> ndiff rd RRecpN -> ndiff rd RRecpNr -> bn_norm (getbn rd s3) -> bn_neg (getbn rd s3) = false ->
              bn_top (getbn rd s3) = bn_top m -> bn_mag (getbn rd s3) = M ->
              hoare F s3 (BN_RECP_CTX_set ops rd) (fun _ s4 => exists nb,
                (length (st_bns s) <= length (st_bns s4))%nat /\ slots_same u [RRecpN; RRecpNr] s s4 /\ st_ri s4 = st_ri s /\ st_n0 s4 = st_n0 s /\
                gx_used (st_ctx s4) = S (S u) /\ gx_frames (st_ctx s4) = gx_frames (st_ctx s) ++ [u] /\ InvR M nb (bn_top m) s4)).
    { intros s3 rd Hs3 L3 Sl3 (X1 & X2 & X3 & X4) Eu3 Ef3 Ld D1 D2 Nd Ngd Td Md.
      eapply hoare_mono; [apply BN_RECP_CTX_set_spec; try assumption; rewrite Td; exact Tm|].
      intros [] s4 _ ([(L4 & U4 & F4) Sl4] & Y1 & Y2 & Y3 & Hok & Hst & T4). rewrite Eu3 in Sl4, U4. rewrite Ef3 in F4. rewrite Md, Td in *.
      exists (num_bits_pure (getbn rd s3)). split; [lia|]. split.
      { intros q Hq Hn. rewrite (Sl4 q ltac:(lia) Hn). apply Sl3; [exact Hq|intros []]. }
      rewrite Y1, Y2, X1, X2. split; [reflexivity|]. split; [reflexivity|]. split; [exact U4|]. split; [exact F4|].
      unfold InvR. auto. }
    pose proof I02 as (_ & _ & Sl02).
    destruct (bn_neg m) eqn:Enm.
    -
      eapply hoare_bind; [apply BN_copy_spec; [apply V2; rewrite Eaa; unfold RPool; lia|rewrite Eaa; unfold RPool, ROne, NFIX; lia|apply V2; lia]|].
      intros [] s3 Hs3 (n3 & -> & T3 & Ng3 & P3). rewrite (G2 rm Lm) in T3, Ng3, P3. fold m in T3, Ng3, P3.
      assert (Vaa : (aa < length (st_bns s2))%nat) by (apply V2; rewrite Eaa; unfold RPool; lia).
      apply hoare_bind_update; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Vaa; try reflexivity.
      { exact Vaa. } { rewrite Eaa. unfold RPool, ROne, NFIX. lia. }
      { pose proof (st_wf_ok aa _ Hs3 ltac:(rewrite length_setbn; exact Vaa) ltac:(rewrite Eaa; unfold RPool, ROne, NFIX; lia)) as OK3.
        rewrite getbn_setbn_same in OK3 by exact Vaa. destruct OK3 as (O1 & O2 & O3 & O4).
        unfold bg_ok, bn_dmax in *. cbn [bn_with_neg bn_buf bn_top bn_flags]. auto. }
      rewrite setbn_setbn_same.
      apply (POST (setbn aa (bn_with_neg n3 false) s2) aa); try rewrite length_setbn; try rewrite st_ctx_setbn; try rewrite getbn_setbn_same by exact Vaa;
        cbn [bn_with_neg bn_top bn_neg bn_buf].
      + apply st_wf_setbn; [exact Hs2| |]. { rewrite Eaa. unfold RPool, ROne, NFIX. lia. }
        pose proof (st_wf_ok aa _ Hs3 ltac:(rewrite length_setbn; exact Vaa) ltac:(rewrite Eaa; unfold RPool, ROne, NFIX; lia)) as OK3.
        rewrite getbn_setbn_same in OK3 by exact Vaa. destruct OK3 as (O1 & O2 & O3 & O4).
        unfold bg_ok, bn_dmax in *. cbn [bn_with_neg bn_buf bn_top bn_flags]. auto.
      + exact L2.
      + intros q Hq _. rewrite getbn_setbn_other by (rewrite Eaa; unfold RPool; lia). apply Sl02; [exact Hq|intros []].
      + unfold scal_same in *. cbn. exact Sc02.
      + exact Eu2.
      + exact Ef2'.
      + unfold live. rewrite st_ctx_setbn, Eu2, Eaa. unfold RPool. lia.
      + rewrite Eaa. unfold ndiff, RPool, RRecpN, NFIX. lia.
      + rewrite Eaa. unfold ndiff, RPool, RRecpNr, NFIX. lia.
      + apply (norm_of_firstn_eq (mkBN (bn_d n3) (bn_buf n3) (bn_top n3) false (bn_flags n3)) m); cbn [bn_top bn_buf]; [exact T3|exact P3|exact Nm].
      + reflexivity.
      + exact T3.
      + unfold M. rewrite <- (mag_of_firstn_eq n3 m T3 P3). reflexivity.
    - apply (POST s2 rm Hs2 L2 Sl02 Sc02 Eu2 Ef2'); try reflexivity.
      + unfold live. rewrite Eu2. lia.
      + unfold ndiff, RRecpN. lia.
      + unfold ndiff, RRecpNr. lia.
      + rewrite (G2 rm Lm). exact Nm.
      + rewrite (G2 rm Lm). exact Enm.
      + rewrite (G2 rm Lm). reflexivity.
      + rewrite (G2 rm Lm). reflexivity. }
  intros [] s4 Hs4 (nb & L4 & Sl4 & Ri4 & N04 & Eu4 & Ef4 & I4).
  assert (G4 : forall z, (z < NFIX + u)%nat -> z <> RRecpN -> z <> RRecpNr -> getbn z s4 = getbn z s).
  { intros z Hz Hz1 Hz2. apply Sl4; [exact Hz|]. intros [E|[E|[]]]; [apply Hz1|apply Hz2]; rewrite E; reflexivity. }
  assert (V4 : forall z, (z < NFIX + S (S u))%nat -> (z < length (st_bns s4))%nat) by (intros z Hz; apply live_valid; [exact Hs4|unfold live; rewrite Eu4; exact Hz]).

  eapply hoare_bind.
  { apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite Eu4, Ef4, length_app. cbn [length].
    rewrite !(G4 rm), !(G4 ra) by (first [lia|unfold RRecpN, RRecpNr; lia]). fold a m.
    split; [rewrite Ev0; unfold RPool; lia|]. split; [lia|]. split; [lia|]. split; [rewrite Ev0; unfold ndiff, RPool, ROne, NFIX; lia|].
    split; [rewrite Ev0; unfold ndiff, RPool; lia|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|].
    split; [exact Nm|]. split; [lia|]. unfold BG_DMAX. lia. }
  intros [] s5 Hs5 (K5 & X5). rewrite !(G4 rm), !(G4 ra) in X5 by (first [lia|unfold RRecpN, RRecpNr; lia]). fold a m M in X5. rewrite Eu4 in K5.
  pose proof X5 as (Cx & Nx & Mx & Tx).
  pose proof (keeps_used _ _ _ _ K5) as Eu5. pose proof (keeps_frames _ _ _ _ K5) as Ef5. rewrite Eu4 in Eu5. rewrite Ef4 in Ef5.
  assert (I5 : InvR M nb (bn_top m) s5).
  { destruct K5 as [[_ Sl5] (_ & _ & S3 & S4)]. apply (InvR_frame M nb (bn_top m) s4 s5 I4); try assumption;
      apply Sl5; try (unfold RRecpN, RRecpNr, NFIX; lia); rewrite Ev0; unfold RPool, RRecpN, RRecpNr, NFIX; intros [E|[]]; lia. }
  pose proof (FrR_of_keeps u _ _ _ _ K5 ltac:(lia)) as F45.
  assert (V5 : forall z, (z < NFIX + S (S u))%nat -> (z < length (st_bns s5))%nat) by (intros z Hz; apply live_valid; [exact Hs5|unfold live; rewrite Eu5; exact Hz]).
  apply hoare_bind_get.

  eapply hoare_bind with (R := fun _ s6 => FrR u [rr] s4 s6 /\ gx_frames (st_ctx s6) = gx_frames (st_ctx s) ++ [u] /\
                                       exp_post (bn_val a) P M (getbn rr s6) /\ (bn_top (getbn rr s6) <= bn_top m)%nat).
  { unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn v0 s5)) 0) as [Z0|Z0].
    -
      eapply hoare_mono; [apply BN_zero_spec; [apply V5; lia|exact Nr1]|].
      intros [] s6 _ (b6 & -> & T6 & N6). rewrite getbn_setbn_same, st_ctx_setbn by (apply V5; lia).
      split; [eapply FrR_weaken; [apply Nat.le_refl| |eapply FrR_trans; [exact F45|apply FrR_setbn]]; intros q Hq Hlow; cbn in Hq |- *;
              rewrite Ev0 in Hq; unfold RPool in Hq; destruct Hq as [Hq|[Hq|[]]]; [lia|auto]|].
      split; [exact Ef5|]. split; [|lia]. unfold exp_post. rewrite (bn_mag_top0 b6 T6).
      split; [split; [left; exact T6|intros _; exact N6]|]. split; [exact N6|].
      rewrite <- (pow_mod_base (bn_val a) P M) by lia. rewrite <- Mx, (bn_mag_top0 _ Z0), Z.pow_0_l by lia. reflexivity.
    -
      assert (HM2 : 2 <= M).
      { pose proof (Z.mod_pos_bound (bn_val a) M HM) as Hb. rewrite <- Mx in Hb.
        destruct (Z.eq_dec (bn_mag (getbn v0 s5)) 0) as [E0|E0]; [|lia]. exfalso. apply Z0.
        apply norm_mag0_top0; [|destruct Cx as [Hn _]; exact Hn|exact E0]. apply (st_wf_okv v0 s5 Hs5). apply V5. rewrite Ev0. unfold RPool. lia. }
      set (a0 := bn_val a mod M).
      assert (Ha0 : 0 <= a0 < M) by (unfold a0; apply Z.mod_pos_bound; exact HM).
      eapply hoare_bind.
      { apply (exp_table_ok (kitR M nb (bn_top m)) window v0 aa F s5 a0); cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitR].
        - exact I5.
        - unfold live. rewrite Eu5, Ev0. unfold RPool. lia.
        - rewrite Ev0. unfold RPool, RRecpNr, NFIX. intros [E|[]]. lia.
        - unfold live. rewrite Eu5, Eaa. unfold RPool. lia.
        - rewrite Eaa. unfold ndiff, RPool, ROne, NFIX. lia.
        - unfold rfreeR. rewrite Eaa. unfold ndiff, RPool, RRecpN, RRecpNr, NFIX. lia.
        - rewrite Eaa. unfold RPool, RRecpNr, NFIX. intros [E|[]]. lia.
        - rewrite Ev0, Eaa. unfold RPool. lia.
        - unfold RepR. split; [exact Cx|]. split; [exact Nx|]. split; [|exact Tx]. rewrite Mx. unfold a0. rewrite Z.mod_mod by lia. reflexivity.
        - lia.
        - lia.
        - rewrite Ef5, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - rewrite Eu5. unfold BG_POOL in *. lia. }
      intros vals s6 Hs6 ((new & Evals & Hnew) & Lv & F6 & L6 & U6 & Fm6 & I6 & T6 & W6).
      cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitR] in F6, I6, T6, W6. rewrite Eu5 in U6, F6, Hnew. rewrite Ef5 in Fm6.
      destruct (Nat.eqb_spec rr rp) as [E|_]; [exfalso; apply Nrp; exact E|].
      assert (Vr6 : (rr < length (st_bns s6))%nat) by (apply live_valid; [exact Hs6|unfold live; rewrite U6; lia]).
      assert (Hvals : forall v, In v vals -> (NFIX + u <= v)%nat /\ (v < NFIX + (u + 2 + (Z.to_nat (2 ^ (window - 1)) - 1)))%nat).
      { intros v Hv. rewrite Evals in Hv. destruct Hv as [<-|Hv].
        - rewrite Ev0. unfold RPool. lia.
        - destruct (@In_nth bnref new v 0%nat Hv) as (i & Hi & <-). rewrite (Hnew i Hi). unfold RPool.
          rewrite Evals in Lv. cbn [length] in Lv. lia. }
      eapply hoare_bind; [apply BN_one_spec; [exact Vr6|exact Nr1]|].
      intros [] s7 Hs7 (b7 & -> & M7 & C7 & N7 & T7).
      set (u5 := (u + 2 + (Z.to_nat (2 ^ (window - 1)) - 1))%nat) in *.
      eapply hoare_mono.
      { apply (exp_window_loop_ok (kitR M nb (bn_top m)) (Z.to_nat bits) u5 rp rr vals window (bits - 1) true F (setbn rr b7 s6) a0 P);
          cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitR]; try rewrite st_ctx_setbn; try rewrite length_setbn.
        - apply (InvR_frame M nb (bn_top m) s6 _ I6); try reflexivity; apply getbn_setbn_other; unfold RRecpN, RRecpNr; lia.
        - rewrite U6. lia.
        - unfold live. rewrite st_ctx_setbn, U6. lia.
        - exact Nr1.
        - unfold rfreeR, ndiff, RRecpN, RRecpNr. lia.
        - unfold RRecpNr. intros [E|[]]. lia.
        - lia.
        - unfold RRecpNr. intros [E|[]]. lia.
        - intros E. apply Nrp. rewrite E. reflexivity.
        - pose proof F45 as (L45 & _). lia.
        - intros v Hv. destruct (Hvals v Hv) as [H1 H2]. split; [exact H2|]. split; [intros ->; lia|]. unfold RRecpNr, NFIX in *. intros [E|[]]. lia.
        - rewrite Fm6, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - rewrite U6. unfold BG_POOL in *. lia.
        - rewrite getbn_setbn_other by exact Nrp. rewrite (FrR_slot (S (S u)) [aa] s5 s6 rp F6); [| lia | rewrite Eaa; unfold RPool; intros [E|[]]; lia | unfold RRecpNr; intros [E|[]]; lia].
          rewrite (keeps_get _ _ _ _ rp K5) by (first [lia | rewrite Ev0; unfold RPool; intros [E|[]]; lia]).
          rewrite (G4 rp) by (first [lia | unfold RRecpN, RRecpNr; lia]). reflexivity.
        - lia.
        - lia.
        - lia.
        - exact Lv.
        - eapply (tab_frame (kitR M nb (bn_top m))); [exact T6| |cbn [ek_Fr kitR]; apply (FrR_setbn u5)].
          cbn [ek_wr kitR]. intros v Hv. destruct (Hvals v Hv) as [H1 H2]. split; [exact H2|]. split; [intros [E|[]]; lia|].
          unfold RRecpNr, NFIX in *. intros [E|[]]. lia.
        - rewrite getbn_setbn_same by exact Vr6. replace (bits - 1 + 1) with bits by lia. rewrite (exp_top P bits) by lia.
          rewrite Z.pow_0_r. unfold RepR. split; [exact C7|]. split; [exact N7|]. split; [rewrite M7, Z.mod_1_l by lia; reflexivity|lia].
        - intros _. replace (bits - 1 + 1) with bits by lia. apply exp_top. lia. }
      intros [] s8 _ (F8 & C8 & I8 & R8). cbn [ek_Fr ek_Inv ek_Rep kitR] in F8, I8, R8. destruct C8 as (L8 & U8 & Fm8).
      rewrite st_ctx_setbn in U8, Fm8. destruct R8 as (C8' & N8 & M8 & T8).
      split; [|split; [rewrite Fm8; exact Fm6|split; [|exact T8]]].
      + eapply FrR_weaken; [apply Nat.le_refl| |
          eapply FrR_trans; [exact F45|eapply FrR_trans; [eapply FrR_weaken; [| |exact F6]; [lia|intros q Hq _; exact Hq]|
            eapply FrR_trans; [apply FrR_setbn|eapply FrR_weaken; [| |exact F8]; [lia|intros q Hq _; exact Hq]]]]].
        intros q Hq Hlow. cbn [app] in Hq. rewrite Eaa, Ev0 in Hq. unfold RPool in Hq.
        destruct Hq as [Hq|[Hq|[Hq|[Hq|[]]]]]; try (rewrite <- Hq in Hlow; lia); subst q; cbn; auto.
      + unfold exp_post. split; [exact C8'|]. split; [exact N8|]. rewrite M8. unfold a0. apply pow_mod_base; lia. }

  intros [] s6 Hs6 (F6 & Ef6 & X6 & T6).
  eapply hoare_bind; [apply (BN_CTX_end_spec F s6 (gx_frames (st_ctx s)) u); exact Ef6|].
  intros [] s7 Hs7 (Eb7 & Sc7 & Eu7 & Ef7).
  assert (G7 : forall z, getbn z s7 = getbn z s6) by (intros z; unfold getbn; rewrite Eb7; reflexivity).
  eapply hoare_mono; [apply BN_RECP_CTX_free_spec|]. intros [] s8 _ ->.
  destruct F6 as (L6 & Sl6 & Ri6 & N06 & Rb6). destruct Sc7 as (S1 & S2 & S3 & S4).
  assert (E8 : forall z, z <> RRecpN -> z <> RRecpNr -> getbn z (set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))) = getbn z s6).
  { intros z Hz1 Hz2. unfold getbn at 1. cbn [st_bns set_recp]. fold (getbn z (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))).
    rewrite !getbn_setbn_other by congruence. apply G7. }
  assert (Len7 : length (st_bns s7) = length (st_bns s6)) by (rewrite Eb7; reflexivity).
  split; [|split; [|split]].
  - split; [split; [split|]|].
    + cbn. rewrite !list_set_length. lia.
    + cbn. rewrite Eu7, Ef7. split; reflexivity.
    + intros q Hq Hn. destruct (Nat.eq_dec q RRecpN) as [->|Hq1]; [|destruct (Nat.eq_dec q RRecpNr) as [->|Hq2]].
      * unfold getbn at 1. cbn [st_bns set_recp]. fold (getbn RRecpN (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))).
        rewrite getbn_setbn_other by (unfold RRecpNr, RRecpN; lia). rewrite getbn_setbn_same by (rewrite Len7; unfold RRecpN, NFIX in *; lia). symmetry. exact PrN.
      * unfold getbn at 1. cbn [st_bns set_recp]. fold (getbn RRecpNr (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))).
        rewrite getbn_setbn_same by (rewrite length_setbn, Len7; unfold RRecpNr, NFIX in *; lia). symmetry. exact PrNr.
      * rewrite (E8 q Hq1 Hq2). rewrite (Sl6 q Hq) by (intros [E|[E|[]]]; [apply Hq2; rewrite E; reflexivity|apply Hn; left; exact E]).
        apply G4; assumption.
    + unfold scal_same. cbn. rewrite S1, S2, Ri6, N06, Ri4, N04, Prb, Prs. repeat split; reflexivity.
  - rewrite E8 by (unfold RRecpN, RRecpNr; lia). exact X6.
  - rewrite E8 by (unfold RRecpN, RRecpNr; lia). exact T6.
  - unfold recp_pristine. cbn [st_rbits st_rshift set_recp].
    unfold getbn at 1 2. cbn [st_bns set_recp]. fold (getbn RRecpN (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))).
    fold (getbn RRecpNr (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s7))).
    rewrite getbn_setbn_other by (unfold RRecpNr, RRecpN; lia). rewrite !getbn_setbn_same by (try rewrite length_setbn; rewrite Len7; unfold RRecpN, RRecpNr, NFIX in *; lia).
    repeat split; reflexivity.
Qed.

Lemma hoareG_bind_get : forall {B} F F' r (f : BN -> BMu B) s Q,
  hoareG F F' s (f (getbn r s)) Q -> hoareG F F' s (bbind ops (bget ops r) f) Q.
Proof. intros B F F' r f s Q H. exact H. Qed.

Lemma limb_bit63 : forall x, limb x -> Z.testbit x 63 = true -> 2 ^ 63 <= x.
Proof.
  intros x [H0 H1] Hb. apply Z.testbit_true in Hb; [|lia]. unfold BW in H1.
  assert (x / 2 ^ 63 < 2) by (apply Z.div_lt_upper_bound; [lia|]; change (2 ^ 63 * 2) with (2 ^ 64); exact H1).
  pose proof (Z.div_pos x (2 ^ 63) H0 ltac:(lia)).
  destruct (Z.eq_dec (x / 2 ^ 63) 0) as [E|E]; [rewrite E in Hb; discriminate|].
  pose proof (Z.mul_div_le x (2 ^ 63) ltac:(lia)). lia.
Qed.

Lemma top_limb_bit63 : forall b : BN, bg_okv b -> (1 <= bn_top b)%nat ->
  Z.testbit (nth (bn_top b - 1) (bn_buf b) 0) 63 = true -> Bp (bn_top b) <= 2 * bn_mag b.
Proof.
  intros b [Hl Ht] H1 Hb. unfold bn_mag.
  unfold bn_dmax in Ht.
  replace (bn_top b) with (S (bn_top b - 1)) at 1 2 by lia. rewrite firstn_S_nth by lia. rewrite lval_app, Bp_S. cbn [lval].
  rewrite firstn_length_le by lia. rewrite Z.mul_0_r, Z.add_0_r.
  pose proof (limb_bit63 _ (limbs_nth _ (bn_top b - 1)%nat Hl) Hb) as Hx.
  pose proof (lval_nonneg (firstn (bn_top b - 1) (bn_buf b)) (limbs_firstn _ _ Hl)) as L0.
  pose proof (Bp_pos (bn_top b - 1)) as HB.
  assert (Bp (bn_top b - 1) * 2 ^ 63 <= Bp (bn_top b - 1) * nth (bn_top b - 1) (bn_buf b) 0) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold BW. change (2 ^ 64) with (2 * 2 ^ 63). lia.
Qed.

Lemma neg_limbs_value : forall (m : BN) nl, bg_okv m -> bn_top m = nl -> (1 <= nl)%nat -> Z.odd (bn_mag m) = true ->
  let L := neg_limbs (firstn nl (bn_buf m)) in limbs L /\ length L = nl /\ lval L = Bp nl - bn_mag m.
Proof.
  intros m nl [Hl Ht] Et Hnl Hodd. cbv zeta. change (neg_limbs (firstn nl (bn_buf m))) with (neg_limbs_pure (firstn nl (bn_buf m))).
  unfold bn_dmax in Ht. assert (Hlen : length (firstn nl (bn_buf m)) = nl) by (apply firstn_length_le; lia).
  destruct (neg_limbs_spec (firstn nl (bn_buf m)) (limbs_firstn _ _ Hl)) as (A & B & C).
  - rewrite nth_firstn. destruct (Nat.ltb_spec 0 nl); [|lia]. intros E0.
    rewrite <- (is_odd_pure_spec m (conj Hl Ht)) in Hodd. unfold is_odd_pure in Hodd. rewrite E0 in Hodd. rewrite andb_false_r in Hodd. discriminate.
  - rewrite Hlen in B, C. split; [exact A|]. split; [exact B|]. rewrite C. unfold bn_mag. rewrite Et. reflexivity.
Qed.

Lemma BN_mod_exp_mont_spec : forall rr ra rp rm F s,
  modexp_pre rr ra rp rm s 4 36 -> refs5 rr ra rp rm -> mont_pristine s -> getbn RTmod s = bn_nil 0 ->
  Z.odd (bn_mag (getbn rm s)) = true -> bn_norm (getbn ra s) -> (length F < BG_NF)%nat ->
  hoare F s (BN_mod_exp_mont ops rr ra rp rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     exp_post (bn_val (getbn ra s)) (bn_mag (getbn rp s)) (bn_mag (getbn rm s)) (getbn rr s') /\
     (bn_top (getbn rr s') <= bn_top (getbn rm s))%nat /\ mont_pristine s' /\ getbn RTmod s' = bn_nil 0).
Proof.
  intros rr ra rp rm F s (Lr & La & Lp & Lm & Nr1 & Nrm & Nrp & Hdepth & Hpool & Nm & Tm & Np & Tp & Ta) (R1 & R2 & R3 & R4) Hpr ET Hodd Na HF.
  apply hoare_wf. intros Hs. unfold BN_mod_exp_mont. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va. pose proof (live_valid rp s Hs Lp) as Vp. pose proof (live_valid rm s Hs Lm) as Vm.
  unfold live in Lr, La, Lp, Lm. fold u in Lr, La, Lp, Lm.
  set (a := getbn ra s) in *. set (p := getbn rp s) in *. set (m := getbn rm s) in *.
  pose proof (st_wf_okv rm s Hs Vm) as Okm. pose proof (st_wf_okv rp s Hs Vp) as Okp. pose proof (st_wf_okv ra s Hs Va) as Oka. fold a in Oka. fold p in Okp. fold m in Okm.
  pose proof (norm_mag_pos _ Okm Nm ltac:(lia)) as HM. set (M := bn_mag m) in *. set (P := bn_mag p) in *. set (nl := bn_top m) in *.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  assert (HMR : M < Bp nl) by (apply okv_mag_lt; exact Okm).
  pose proof Hpr as (PrRR & PrN & PrNi & Pri & Pn0).
  apply hoare_bind_get. fold m. rewrite (is_odd_pure_spec m Okm). fold M. rewrite Hodd. cbn [negb].
  eapply hoare_bind; [apply any_consttime_spec; intros q [<-|[<-|[<-|[]]]]; assumption|]. intros ct s0 _ (-> & ->).
  eapply hoare_bind; [apply BN_num_bits_spec; exact Vp|]. intros bits s0 _ (-> & ->). fold p.
  pose proof (num_bits_pure_spec p Okp Np) as (B0 & B1 & B2 & B3). fold P in B1, B2.
  pose proof (okv_mag_nonneg p Okp) as HP0. fold P in HP0.
  destruct (Z.eqb_spec (num_bits_pure p) 0) as [Ez|Ez].
  {
    assert (P = 0) as EP by (destruct (Z.eq_dec P 0) as [|Hne]; [assumption|]; specialize (B2 ltac:(lia)); rewrite Ez in B2;
      change (2 ^ (0 - 1)) with 0 in B2; change (2 ^ 0) with 1 in B2; lia).
    rewrite EP. eapply hoare_mono; [apply (exp_bits0_spec rr rm F s (bn_val a)); [unfold live; lia|exact Vm|exact Nr1|exact Nrm|exact Nm|fold m; lia]|].
    intros [] s' _ (K & E & T). split; [exact K|]. split; [exact E|]. split; [lia|].
    unfold mont_pristine. destruct K as [[_ Sl] (S1 & S2 & S3 & S4)]. rewrite S1, S2.
    rewrite !Sl by (first [unfold RMontRR, RMontN, RMontNi, RTmod, NFIX; lia|intros [E'|[]]; unfold RMontRR, RMontN, RMontNi, RTmod in E'; lia]).
    split; [exact Hpr|exact ET]. }
  set (bits := num_bits_pure p) in *.
  assert (HP1 : 1 <= P) by (destruct (Z.eq_dec P 0) as [E0|]; [exfalso; apply Ez; apply B1; exact E0|lia]).
  specialize (B2 ltac:(lia)).
  pose proof (window_bits_range bits) as Hw. pose proof (window_table_size bits) as Hws. set (window := window_bits bits) in *.

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros d s1 Hs1 (Ed & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Ed, Eu1.
  pose proof (inner_get u d s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Ed; unfold RPool; lia)) as I1.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros r s2 Hs2 (Er & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & Tr2 & Nr2). rewrite Eu1 in Er, Eu2.
  pose proof (inner_get u r s1 s2 Len2 Sc2 Oth2 ltac:(rewrite Er; unfold RPool; lia)) as I2.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu2; unfold BG_POOL in *; lia|].
  intros v0 s3 Hs3 (Ev0 & Eu3 & Ef3 & Sc3 & Len3 & Oth3 & Tv0 & Nv0). rewrite Eu2 in Ev0, Eu3.
  pose proof (inner_get u v0 s2 s3 Len3 Sc3 Oth3 ltac:(rewrite Ev0; unfold RPool; lia)) as I3.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) I3) as I03. cbn [app] in I03.
  assert (G3 : forall z, (z < NFIX + u)%nat -> getbn z s3 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I03 Hz); intros []).
  pose proof I03 as (L3 & Sc03 & _).
  assert (Ef3' : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]) by (rewrite Ef3, Ef2, Ef1; exact Ef0).
  assert (Tr3 : bn_top (getbn r s3) = 0%nat /\ bn_neg (getbn r s3) = false) by (rewrite Oth3 by (rewrite Er, Ev0; unfold RPool; lia); split; assumption).
  assert (V3 : forall z, (z < NFIX + S (S (S u)))%nat -> (z < length (st_bns s3))%nat) by (intros z Hz; apply live_valid; [exact Hs3|unfold live; rewrite Eu3; exact Hz]).

  eapply hoareG_bind.
  { apply BN_MONT_CTX_new_spec; [exact HF|]. unfold mont_pristine. rewrite !G3 by (unfold RMontRR, RMontN, RMontNi, NFIX; lia).
    destruct Sc03 as (S1 & S2 & _). rewrite S1, S2. exact Hpr. }
  intros pm s3' _ ->. cbv beta.

  eapply hoareG_bind.
  { apply BN_MONT_CTX_set_spec. unfold montset_pre, live. rewrite Eu3, Ef3', length_app, !G3 by (unfold RTmod, NFIX; lia). cbn [length]. fold m M nl.
    split; [lia|]. split; [unfold ndiff, RMontN; lia|]. split; [unfold ndiff, RMontRR; lia|]. split; [unfold ndiff, RTmod; lia|].
    split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact ET|]. cbv zeta. split; [exact Nm|]. split; [lia|exact Hodd]. }
  intros [] s4 Hs4 (KM4 & Ri4 & MO4). rewrite (G3 rm Lm) in Ri4, MO4. fold m M nl in Ri4, MO4. rewrite Eu3 in KM4.
  destruct KM4 as [[(L4 & U4 & F4) Sl4] [Rb4 Rs4]]. rewrite Eu3 in U4. rewrite Ef3' in F4.
  assert (G4 : forall z, (z < NFIX + S (S (S u)))%nat -> z <> RMontN -> z <> RMontRR -> getbn z s4 = getbn z s3).
  { intros z Hz Hz1 Hz2. apply Sl4; [exact Hz|]. intros [E|[E|[]]]; [apply Hz1|apply Hz2]; rewrite E; reflexivity. }
  assert (G4s : forall z, (z < NFIX + u)%nat -> z <> RMontN -> z <> RMontRR -> getbn z s4 = getbn z s).
  { intros z Hz Hz1 Hz2. rewrite G4 by (lia || assumption). apply G3. exact Hz. }
  assert (V4 : forall z, (z < NFIX + S (S (S u)))%nat -> (z < length (st_bns s4))%nat) by (intros z Hz; apply live_valid; [exact Hs4|unfold live; rewrite U4; exact Hz]).
  apply hoareG_bind_get. rewrite (G4s ra) by (first [lia|unfold RMontN, RMontRR; lia]). fold a.
  eapply hoareG_bind; [apply BN_ucmp_spec; apply V4; lia|]. intros c s4' _ (-> & ->).
  rewrite (G4s ra), (G4s rm) by (first [lia|unfold RMontN, RMontRR; lia]). fold a m.
  set (a0 := bn_val a mod M).
  assert (Ha0 : 0 <= a0 < M) by (unfold a0; apply Z.mod_pos_bound; exact HM).

  eapply hoareG_bind with (R := fun aa s5 => keeps (S (S (S u))) [v0] s4 s5 /\ (aa = v0 \/ aa = ra) /\
      bn_neg (getbn aa s5) = false /\ bn_mag (getbn aa s5) = a0 /\ (bn_top (getbn aa s5) <= nl)%nat).
  { destruct (bn_neg a || (0 <=? ucmp_pure a m)) eqn:Ec.
    - eapply hoare_bind.
      { apply BN_nnmod_spec. unfold nnmod_pre, live. rewrite U4, F4, length_app. cbn [length].
        rewrite (G4s ra), (G4s rm) by (first [lia|unfold RMontN, RMontRR; lia]). fold a m.
        split; [rewrite Ev0; unfold RPool; lia|]. split; [lia|]. split; [lia|]. split; [rewrite Ev0; unfold ndiff, RPool, ROne, NFIX; lia|].
        split; [rewrite Ev0; unfold ndiff, RPool; lia|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|].
        split; [exact Nm|]. split; [lia|]. unfold BG_DMAX. lia. }
      intros [] s5 Hs5 (K5 & X5). rewrite (G4s ra), (G4s rm) in X5 by (first [lia|unfold RMontN, RMontRR; lia]). fold a m M nl in X5.
      destruct X5 as (Cx & Nx & Mx & Tx). rewrite U4 in K5.
      apply hoare_ret. split; [exact K5|]. split; [left; reflexivity|]. split; [exact Nx|]. split; [exact Mx|exact Tx].
    - apply Bool.orb_false_elim in Ec. destruct Ec as [Ena Ec]. destruct (Z.leb_spec 0 (ucmp_pure a m)) as [|Hlt]; [discriminate|].
      destruct (ucmp_okv_spec a m Oka Okm Na Nm) as (_ & U2 & _). specialize (U2 Hlt). fold M in U2.
      pose proof (okv_mag_nonneg a Oka) as Ha00.
      apply hoare_ret. split; [apply keeps_refl|]. split; [right; reflexivity|].
      rewrite (G4s ra) by (first [lia|unfold RMontN, RMontRR; lia]). fold a.
      split; [exact Ena|]. split; [unfold a0, bn_val; rewrite Ena, Z.mod_small by lia; reflexivity|].
      apply (norm_top_le m a Okm Oka Na). lia. }
  intros aa s5 Hs5 (K5 & Haa & Nx & Mx & Tx).
  pose proof (keeps_used _ _ _ _ K5) as U5. pose proof (keeps_frames _ _ _ _ K5) as F5. rewrite U4 in U5. rewrite F4 in F5.
  assert (MO5 : mont_ok s5 M nl).
  { apply (mont_ok_keeps _ _ _ _ M nl K5); [| |exact MO4]; rewrite Ev0; unfold RPool, RMontN, RMontRR, NFIX; intros [E|[]]; lia. }
  assert (G5 : forall z, (z < NFIX + S (S (S u)))%nat -> z <> v0 -> getbn z s5 = getbn z s4).
  { intros z Hz Hz1. apply (keeps_get _ _ _ _ z K5); [exact Hz|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }
  assert (V5 : forall z, (z < NFIX + S (S (S u)))%nat -> (z < length (st_bns s5))%nat) by (intros z Hz; apply live_valid; [exact Hs5|unfold live; rewrite U5; exact Hz]).
  assert (Laa : (aa < NFIX + S (S (S u)))%nat) by (destruct Haa as [-> | ->]; [rewrite Ev0; unfold RPool; lia|lia]).

  unfold bn_to_mont_fixed_top at 1.
  eapply hoareG_bind.
  { apply (bn_mul_mont_fixed_top_spec v0 aa RMontRR _ s5 M nl MO5). apply (to_mont_pre_ok v0 aa s5 M nl MO5); try assumption.
    - unfold live. rewrite U5, Ev0. unfold RPool. lia.
    - unfold live. rewrite U5. exact Laa.
    - rewrite Ev0. unfold ndiff, RPool, ROne, NFIX. lia.
    - rewrite Ev0. unfold ndiff, RPool, RMontN, NFIX. lia.
    - rewrite Ev0. unfold ndiff, RPool, RMontRR, NFIX. lia.
    - rewrite F5, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
    - rewrite U5. unfold BG_POOL in *. lia.
    - lia.
    - lia. }
  intros [] s6 Hs6 (K6 & MO6 & MR6). rewrite U5 in K6. rewrite Mx in MR6.
  assert (RR5 : bn_mag (getbn RMontRR s5) = (Bp nl * Bp nl) mod M).
  { unfold mont_ok in MO5. cbv zeta in MO5. destruct MO5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E). exact E. }
  rewrite RR5 in MR6. destruct MR6 as (T6 & N6 & B6 & V6).
  assert (R6 : RepM M nl a0 (getbn v0 s6)).
  { unfold RepM. split; [exact T6|]. split; [exact N6|]. split; [exact B6|].
    rewrite <- (Z.mod_small _ M B6). apply (bn_to_mont_value M nl a0); [lia|exact Hodd|exact V6]. }
  pose proof (keeps_used _ _ _ _ K6) as U6. pose proof (keeps_frames _ _ _ _ K6) as F6. rewrite U5 in U6. rewrite F5 in F6.
  assert (G6 : forall z, (z < NFIX + S (S (S u)))%nat -> z <> v0 -> getbn z s6 = getbn z s5).
  { intros z Hz Hz1. apply (keeps_get _ _ _ _ z K6); [exact Hz|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }

  eapply hoareG_bind.
  { apply (exp_table_ok (kitM M nl) window v0 d _ s6 a0); cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitM].
    - exact MO6.
    - unfold live. rewrite U6, Ev0. unfold RPool. lia.
    - intros [].
    - unfold live. rewrite U6, Ed. unfold RPool. lia.
    - rewrite Ed. unfold ndiff, RPool, ROne, NFIX. lia.
    - unfold rfreeM. rewrite Ed. unfold ndiff, RPool, RMontN, RMontRR, NFIX. lia.
    - intros [].
    - rewrite Ev0, Ed. unfold RPool. lia.
    - exact R6.
    - lia.
    - lia.
    - rewrite F6, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
    - rewrite U6. unfold BG_POOL in *. lia. }
  intros vals s7 Hs7 ((new & Evals & Hnew) & Lv & F7 & L7 & U7 & Fm7 & I7 & T7 & W7).
  cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitM] in F7, I7, T7, W7. rewrite U6 in U7, F7, Hnew. rewrite F6 in Fm7.
  assert (G7 : forall z, (z < NFIX + S (S (S u)))%nat -> z <> d -> getbn z s7 = getbn z s6).
  { intros z Hz Hz1. apply (inner_get_slot _ _ _ _ z F7); [exact Hz|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }

  assert (G7s : forall z, (z < NFIX + u)%nat -> z <> RMontN -> z <> RMontRR -> getbn z s7 = getbn z s).
  { intros z Hz Hz1 Hz2. rewrite G7, G6, G5 by (first [lia | rewrite Ed; unfold RPool; lia | rewrite Ev0; unfold RPool; lia]).
    apply G4s; assumption. }
  assert (V7 : forall z, (z < NFIX + S (S (S u)))%nat -> (z < length (st_bns s7))%nat) by (intros z Hz; apply live_valid; [exact Hs7|unfold live; rewrite U7; lia]).
  assert (Hvals : forall v, In v vals -> (NFIX + S (S u) <= v)%nat /\ v <> RPool (S u) /\ (v < NFIX + (u + 3 + (Z.to_nat (2 ^ (window - 1)) - 1)))%nat).
  { intros v Hv. rewrite Evals in Hv. destruct Hv as [<-|Hv].
    - rewrite Ev0. unfold RPool. repeat split; lia.
    - destruct (@In_nth bnref new v 0%nat Hv) as (i & Hi & <-). rewrite (Hnew i Hi). unfold RPool.
      rewrite Evals in Lv. cbn [length] in Lv. repeat split; lia. }
  set (u7 := (u + 3 + (Z.to_nat (2 ^ (window - 1)) - 1))%nat) in *.

  assert (Er7 : bn_top (getbn r s7) = 0%nat /\ bn_neg (getbn r s7) = false).
  { rewrite G7, G6, G5, G4 by (first [rewrite Er; unfold RPool, RMontN, RMontRR, NFIX; lia | rewrite Er, Ed; unfold RPool; lia | rewrite Er, Ev0; unfold RPool; lia]).
    exact Tr3. }
  apply hoareG_bind_get. rewrite (G7s rm) by (first [lia|unfold RMontN, RMontRR; lia]). fold m nl.
  replace (nl =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).

  eapply hoareG_bind with (R := fun _ s8 => inner u7 [r] s7 s8 /\ ctx_keep s7 s8 /\ mont_ok s8 M nl /\ RepM M nl 1 (getbn r s8)).
  { assert (Vr7 : (r < length (st_bns s7))%nat) by (apply V7; rewrite Er; unfold RPool; lia).
    assert (NrOne : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
    destruct (Z.testbit (nth (nl - 1) (bn_buf m) 0) 63) eqn:Etb.
    -
      pose proof (top_limb_bit63 m Okm ltac:(lia) Etb) as HmR. fold nl M in HmR.
      destruct (neg_limbs_value m nl Okm eq_refl ltac:(lia) Hodd) as (NL1 & NL2 & NL3). fold M in NL3.
      set (L := neg_limbs (firstn nl (bn_buf m))) in *.
      replace (r =? rm)%nat with false by (symmetry; apply Nat.eqb_neq; rewrite Er; unfold RPool; lia).
      eapply hoare_bind; [apply bn_wexpand_spec; [exact Vr7|exact NrOne|unfold BG_DMAX; lia]|].
      intros [] s8 Hs8 (r1 & -> & Hex). destruct Hex as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). destruct Er7 as [Tr7 Nr7].
      rewrite Tr7 in E1. rewrite Nr7 in E2. pose proof Hok1 as (O1 & O2 & O3 & O4). unfold bn_dmax in Hd1, O2, O3.
      apply hoare_bind_get. rewrite getbn_setbn_same by exact Vr7. apply hoare_bind_get.
      rewrite (getbn_setbn_other r rm) by (rewrite Er; unfold RPool; lia). rewrite (G7s rm) by (first [lia|unfold RMontN, RMontRR; lia]). fold m nl L.
      assert (Lsp : length (splice (bn_buf r1) 0 L) = length (bn_buf r1)) by (apply splice_length; rewrite NL2; lia).
      eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Vr7; try assumption; try reflexivity.
      + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lsp. split; [apply splice_limbs; [exact O1|exact NL1]|].
        split; [lia|]. split; [exact O3|exact O4].
      + rewrite setbn_setbn_same. set (rG := mkBN (bn_d r1) (splice (bn_buf r1) 0 L) nl (bn_neg r1) (bn_flags r1)).
        split; [apply inner_setbn|]. split; [unfold ctx_keep; rewrite length_setbn, st_ctx_setbn; auto|]. split.
        * apply (mont_ok_keeps u7 [r] s7 _ M nl); [apply keeps_setbn| | |exact I7]; rewrite Er; unfold RPool, RMontN, RMontRR, NFIX; intros [E|[]]; lia.
        * rewrite getbn_setbn_same by exact Vr7. unfold RepM, bn_mag. cbn [rG bn_top bn_neg bn_buf].
          rewrite firstn_splice_0 by (rewrite ?NL2; lia). rewrite NL3, E2.
          assert (HBM : Bp nl <> 2 * M).
          { intros EBM. pose proof Hodd as Hodd'. apply Z.odd_spec in Hodd'. destruct Hodd' as [k Hk]. rewrite Bp_pow2 in EBM.
            assert (E' : 2 ^ (64 * Z.of_nat nl) = 2 * (2 * 2 ^ (64 * Z.of_nat nl - 2))).
            { rewrite <- !Z.pow_succ_r by (try apply Z.mul_nonneg_nonneg; lia). f_equal. lia. }
            lia. }
          split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
          rewrite Z.mul_1_l. apply (Z.mod_unique_pos (Bp nl) M 1 (Bp nl - M)); lia.
    -
      unfold bn_to_mont_fixed_top.
      assert (MOne : getbn ROne s7 = bn_const_one) by (destruct Hs7 as (_ & _ & E & _); exact E).
      eapply hoare_mono.
      { apply (bn_mul_mont_fixed_top_spec r ROne RMontRR _ s7 M nl I7). apply (to_mont_pre_ok r ROne s7 M nl I7); try rewrite MOne.
        - unfold live. rewrite U7, Er. unfold RPool. lia.
        - unfold live, ROne, NFIX. lia.
        - exact NrOne.
        - rewrite Er. unfold ndiff, RPool, RMontN, NFIX. lia.
        - rewrite Er. unfold ndiff, RPool, RMontRR, NFIX. lia.
        - rewrite Fm7, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
        - rewrite U7. unfold BG_POOL in *. lia.
        - cbn. lia.
        - reflexivity.
        - rewrite bn_mag_const_one. pose proof (Bp_pos (nl - 1)). replace nl with (S (nl - 1)) by lia. rewrite Bp_S. unfold BW. lia.
        - rewrite bn_mag_const_one. lia. }
      intros [] s8 _ (K8 & MO8 & MR8). rewrite MOne, bn_mag_const_one in MR8.
      assert (RR7 : bn_mag (getbn RMontRR s7) = (Bp nl * Bp nl) mod M).
      { unfold mont_ok in I7. cbv zeta in I7. destruct I7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E). exact E. }
      rewrite RR7 in MR8. destruct MR8 as (T8 & N8 & B8 & V8). rewrite U7 in K8.
      split; [eapply inner_of_keeps; [exact K8|unfold u7; lia]|]. split; [destruct K8 as [[C _] _]; exact C|]. split; [exact MO8|].
      unfold RepM. split; [exact T8|]. split; [exact N8|]. split; [exact B8|].
      rewrite <- (Z.mod_small _ M B8). apply (bn_to_mont_value M nl 1); [lia|exact Hodd|exact V8]. }
  intros [] s8 Hs8 (I8 & C8 & MO8 & R8). destruct C8 as (L8 & U8 & Fm8). rewrite U7 in U8. rewrite Fm7 in Fm8.
  assert (G8 : forall z, (z < NFIX + u7)%nat -> z <> r -> getbn z s8 = getbn z s7).
  { intros z Hz Hz1. apply (inner_get_slot _ _ _ _ z I8); [exact Hz|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }

  eapply hoareG_bind.
  { apply (exp_window_loop_ok (kitM M nl) (Z.to_nat bits) u7 rp r vals window (bits - 1) true _ s8 a0 P);
      cbn [ek_Inv ek_wr ek_rfree ek_Rep ek_D ek_P ek_Fr kitM].
    - exact MO8.
    - rewrite U8. unfold u7. lia.
    - unfold live. rewrite U8, Er. unfold RPool. lia.
    - rewrite Er. unfold ndiff, RPool, ROne, NFIX. lia.
    - unfold rfreeM. rewrite Er. unfold ndiff, RPool, RMontN, RMontRR, NFIX. lia.
    - intros [].
    - unfold u7. lia.
    - intros [].
    - rewrite Er. unfold RPool. lia.
    - pose proof (V7 rp ltac:(lia)). lia.
    - intros v Hv. destruct (Hvals v Hv) as (H1 & H2 & H3). split; [exact H3|]. split; [rewrite Er; exact H2|intros []].
    - rewrite Fm8, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
    - rewrite U8. unfold u7, BG_POOL in *. lia.
    - rewrite G8, (G7s rp) by (first [unfold u7; lia | unfold RMontN, RMontRR; lia | rewrite Er; unfold RPool; lia]). reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Lv.
    - eapply (tab_frame (kitM M nl)); [exact T7| |cbn [ek_Fr kitM]; exact I8].
      cbn [ek_wr kitM]. intros v Hv. destruct (Hvals v Hv) as (H1 & H2 & H3). split; [exact H3|]. split; [rewrite Er; intros [E|[]]; apply H2; rewrite E; reflexivity|intros []].
    - replace (bits - 1 + 1) with bits by lia. rewrite (exp_top P bits) by lia. rewrite Z.pow_0_r. exact R8.
    - intros _. replace (bits - 1 + 1) with bits by lia. apply exp_top. lia. }
  intros [] s9 Hs9 (F9 & C9 & I9 & R9). cbn [ek_Fr ek_Inv ek_Rep kitM] in F9, I9, R9. destruct C9 as (L9 & U9 & Fm9). rewrite U8 in U9. rewrite Fm8 in Fm9.
  destruct R9 as (T9 & N9 & B9 & M9).
  assert (G9 : forall z, (z < NFIX + u7)%nat -> z <> r -> getbn z s9 = getbn z s8).
  { intros z Hz Hz1. apply (inner_get_slot _ _ _ _ z F9); [exact Hz|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }

  eapply hoareG_bind.
  { apply (BN_from_montgomery_spec rr r _ s9 M nl I9). unfold from_mont_top_pre, live. rewrite U9, Fm9, length_app, T9, N9. cbn [length].
    split; [unfold u7; lia|]. split; [rewrite Er; unfold RPool, u7; lia|]. split; [exact Nr1|]. split; [unfold ndiff, RMontN; lia|]. split; [unfold ndiff, RMontRR; lia|].
    split; [unfold BG_DEPTH in *; lia|]. split; [unfold u7, BG_POOL in *; lia|]. split; [lia|]. split; [reflexivity|].
    pose proof (Bp_pos nl). assert (M * 1 <= M * Bp nl) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  intros [] s10 Hs10 (K10 & MO10 & MC10). rewrite U9 in K10. destruct MC10 as (C10 & T10 & N10 & B10 & V10). rewrite M9 in V10.
  assert (X10 : exp_post (bn_val a) P M (getbn rr s10)).
  { unfold exp_post. split; [exact C10|]. split; [exact N10|]. rewrite <- (Z.mod_small _ M B10).
    rewrite <- (pow_mod_base (bn_val a) P M) by lia. fold a0.
    apply (mont_cancel (Bp nl) M); [lia|rewrite Bp_pow2; apply gcd_pow2_odd; [lia|exact Hodd]|]. rewrite V10. apply Z.mod_mod. lia. }
  pose proof (keeps_used _ _ _ _ K10) as U10. pose proof (keeps_frames _ _ _ _ K10) as Fm10. rewrite U9 in U10. rewrite Fm9 in Fm10.
  assert (G10 : forall z, (z < NFIX + u7)%nat -> z <> rr -> getbn z s10 = getbn z s9).
  { intros z Hz Hz1. apply (keeps_get _ _ _ _ z K10); [unfold u7 in Hz; lia|]. intros [E|[]]. apply Hz1. rewrite E. reflexivity. }

  assert (G10s : forall z, (z < NFIX + u)%nat -> z <> rr -> z <> RMontN -> z <> RMontRR -> getbn z s10 = getbn z s).
  { intros z Hz Hz0 Hz1 Hz2. rewrite G10, G9, G8 by (first [unfold u7; lia | assumption | rewrite Er; unfold RPool; lia]). apply G7s; assumption. }
  assert (Ltot : (length (st_bns s) <= length (st_bns s10))%nat).
  { destruct K5 as [[(L5' & _) _] _]. destruct K6 as [[(L6' & _) _] _]. destruct K10 as [[(L10' & _) _] _]. lia. }

  eapply hoareG_bind.
  { apply BN_MONT_CTX_free_spec. rewrite (G10s RMontNi) by (unfold RMontNi, RMontN, RMontRR, NFIX; lia). exact PrNi. }
  intros [] s11 _ ->.

  eapply hoare_mono; [apply (BN_CTX_end_spec F _ (gx_frames (st_ctx s)) u); cbn; exact Fm10|].
  intros [] s12 _ (Eb12 & Sc12 & Eu12 & Ef12).
  assert (E12 : forall z, getbn z s12 = getbn z (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) s10))).
  { intros z. unfold getbn at 1. rewrite Eb12. reflexivity. }
  destruct Sc12 as (S1 & S2 & S3 & S4). cbn in S1, S2, S3, S4.
  destruct K10 as [_ (Y1 & Y2 & Y3 & Y4)]. destruct I8 as (_ & (Z1 & Z2 & Z3 & Z4) & _). destruct F9 as (_ & (W1 & W2 & W3 & W4) & _).
  destruct F7 as (_ & (X1 & X2 & X3 & X4) & _). destruct K6 as [_ (Q1 & Q2 & Q3 & Q4)]. destruct K5 as [_ (P1' & P2' & P3' & P4')].
  assert (VN10 : (RMontN < length (st_bns s10))%nat) by (apply live_valid; [exact Hs10|unfold live, RMontN, NFIX; lia]).
  assert (VRR10 : (RMontRR < length (st_bns s10))%nat) by (apply live_valid; [exact Hs10|unfold live, RMontRR, NFIX; lia]).
  split; [|split; [|split; [|split]]].
  - split; [split; [split|]|].
    + rewrite Eb12. cbn. rewrite !list_set_length. exact Ltot.
    + rewrite Eu12, Ef12. split; reflexivity.
    + intros q Hq Hn. rewrite E12. destruct (Nat.eq_dec q RMontN) as [->|Hq1]; [|destruct (Nat.eq_dec q RMontRR) as [->|Hq2]].
      * rewrite getbn_setbn_same by (rewrite length_setbn; exact VN10). symmetry. exact PrN.
      * rewrite getbn_setbn_other by (unfold RMontN, RMontRR; lia). rewrite getbn_setbn_same by exact VRR10. symmetry. exact PrRR.
      * rewrite !getbn_setbn_other by (first [exact (not_eq_sym Hq1) | exact (not_eq_sym Hq2) | congruence]).
        apply G10s; [exact Hq|intros ->; apply Hn; left; reflexivity|exact Hq1|exact Hq2].
    + unfold scal_same. rewrite S1, S2, S3, S4. cbn. rewrite Y3, Y4, W3, W4, Z3, Z4, X3, X4, Q3, Q4, P3', P4', Rb4, Rs4.
      destruct Sc03 as (_ & _ & S03a & S03b). rewrite S03a, S03b, Pri, Pn0. repeat split; reflexivity.
  - rewrite E12, !getbn_setbn_other by (unfold RMontN, RMontRR; lia). exact X10.
  - rewrite E12, !getbn_setbn_other by (unfold RMontN, RMontRR; lia). fold nl in T10. exact T10.
  - unfold mont_pristine. rewrite !E12. cbn [st_ri st_n0 set_mont].
    rewrite getbn_setbn_other by (unfold RMontN, RMontRR; lia). rewrite getbn_setbn_same by exact VRR10.
    rewrite getbn_setbn_same by (rewrite length_setbn; exact VN10).
    rewrite !getbn_setbn_other by (unfold RMontN, RMontRR, RMontNi; lia). rewrite (G10s RMontNi) by (unfold RMontNi, RMontN, RMontRR, NFIX; lia).
    rewrite S1, S2. cbn. repeat split; try reflexivity. exact PrNi.
  - rewrite E12, !getbn_setbn_other by (unfold RMontN, RMontRR, RTmod; lia).
    rewrite G10, G9, G8, G7, G6, G5 by (first [unfold u7, RTmod, NFIX; lia | rewrite ?Er, ?Ed, ?Ev0; unfold RPool, RTmod, NFIX; lia]).
    rewrite (Sl4 RTmod) by (first [unfold RTmod, NFIX; lia | unfold RTmod, RMontN, RMontRR; intros [E|[E|[]]]; lia]).
    rewrite G3 by (unfold RTmod, NFIX; lia). exact ET.
Qed.

End ExpSpec.
