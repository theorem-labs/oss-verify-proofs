(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgNumTheory.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RecpSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma norm_top_lt : forall (b : BN) k, bg_okv b -> bn_norm b -> bn_mag b < Bp k -> (bn_top b <= k)%nat.
Proof.
  intros b k Hb Hn Hlt. destruct (Nat.le_gt_cases (bn_top b) k) as [|Hgt]; [assumption|exfalso].
  pose proof (okv_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_mono k (bn_top b - 1) ltac:(lia)). lia.
Qed.

Definition reciprocal_pre (rr rm : bnref) (len : Z) (s : ST) : Prop :=
  live rr s /\ live rm s /\ ndiff rr ROne /\ ndiff rr rm /\
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 5 <= BG_POOL)%nat /\
  bn_norm (getbn rm s) /\ (1 <= bn_top (getbn rm s))%nat /\ bn_neg (getbn rm s) = false /\
  0 <= len /\ len / 64 + 4 <= BG_DMAX /\ Z.of_nat (bn_top (getbn rm s)) + 2 <= BG_DMAX.

Lemma BN_reciprocal_spec : forall rr rm len F s,
  reciprocal_pre rr rm len s ->
  hoare F s (BN_reciprocal ops rr rm len) (fun res s' =>
     res = len /\ keeps (gx_used (st_ctx s)) [rr] s s' /\
     let r := getbn rr s' in bn_canon r /\ bn_neg r = false /\ bn_mag r = 2 ^ len / bn_mag (getbn rm s)).
Proof.
  intros rr rm len F s (Lr & Lm & Nr1 & Nrm & Hdepth & Hpool & Hnm & Htm & Hnegm & Hlen & Hsz & Hszm).
  unfold BN_reciprocal. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, Lm. fold u in Lr, Lm.
  set (m := getbn rm s) in *.
  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros t s1 Hs1 (Et & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & Tt1 & Nt1'). rewrite Eu0 in Et, Eu1.
  pose proof (inner_get u t s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Et; unfold RPool; lia)) as I1.
  pose proof (inner_trans _ _ _ _ _ _ I0 I1) as I01. cbn [app] in I01.
  assert (G1 : forall x, (x < NFIX + u)%nat -> getbn x s1 = getbn x s) by (intros x Hx; apply (inner_get_slot _ _ _ _ x I01 Hx); intros []).
  assert (Vt : (t < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|]; unfold live; rewrite Eu1, Et; unfold RPool; lia).
  assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).
  eapply hoare_bind; [apply BN_set_bit_zero_spec; try assumption; unfold BG_DMAX in *; lia|].
  intros [] s2 Hs2 (t2 & -> & M2 & No2 & T2 & N2). rewrite Nt1' in N2.
  set (s2 := setbn t t2 s1) in *.
  pose proof (inner_setbn u t t2 s1) as I2. fold s2 in I2.
  assert (G2 : forall x, (x < NFIX + u)%nat -> getbn x s2 = getbn x s).
  { intros x Hx. unfold s2. rewrite getbn_setbn_other by (rewrite Et; unfold RPool; lia). apply G1. exact Hx. }
  assert (Eg2 : getbn t s2 = t2) by (unfold s2; apply getbn_setbn_same; exact Vt).
  eapply hoare_bind.
  { apply (BN_div_spec (Some rr) None t rm). unfold div_pre, live. change (gx_used (st_ctx s2)) with (gx_used (st_ctx s1)).
    change (gx_frames (st_ctx s2)) with (gx_frames (st_ctx s1)). rewrite Eu1, Ef1, Ef0, length_app, Eg2, (G2 rm Lm). cbn [length]. fold m.
    split; [rewrite Et; unfold RPool; lia|]. split; [lia|]. split.
    - intros d Ed. injection Ed as <-. split; [lia|]. split; [exact Nr1|exact Nrm].
    - split; [intros r Er; discriminate|]. split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|].
      split; [exact Hnm|]. split; [exact Htm|]. split; [rewrite T2; rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia); lia|exact Hszm]. }
  intros [] s3 Hs3 (K3 & Q3 & _). change (gx_used (st_ctx s2)) with (gx_used (st_ctx s1)) in K3. rewrite Eu1 in K3. cbn [opt_refs app] in K3.
  rewrite Eg2, (G2 rm Lm) in Q3. fold m in Q3. pose proof (Q3 rr eq_refl) as Q3'. cbv zeta in Q3'. destruct Q3' as (C3 & M3 & N3 & _). clear Q3.
  pose proof (inner_of_keeps u _ _ _ _ K3 ltac:(lia)) as I3.
  assert (Ef3 : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]).
  { rewrite (keeps_frames _ _ _ _ K3). change (gx_frames (st_ctx s2)) with (gx_frames (st_ctx s1)). rewrite Ef1. exact Ef0. }
  eapply hoare_bind; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3|].
  intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4). apply hoare_ret.
  pose proof (inner_bns_eq u s3 s4 Eb4 Sc4) as I4.
  split; [reflexivity|]. split.
  - apply keeps_of_inner; [|exact Eu4|exact Ef4].
    eapply inner_weaken; [|eapply inner_trans; [eapply inner_trans; [eapply inner_trans; [exact I01|exact I2]|exact I3]|exact I4]].
    intros r Hin Hr. cbn [app] in Hin. destruct Hin as [E|[E|[]]]; [rewrite <- E, Et in Hr; unfold RPool in Hr; lia|left; exact E].
  - cbv zeta. assert (Eg : getbn rr s4 = getbn rr s3) by (unfold getbn; rewrite Eb4; reflexivity). rewrite Eg.
    split; [exact C3|]. split; [rewrite N3, N2, Hnegm; reflexivity|]. rewrite M3, M2. reflexivity.
Qed.

Definition recp_ok (s : ST) (N nb : Z) : Prop :=
  let n := getbn RRecpN s in
  bn_norm n /\ (1 <= bn_top n <= 64)%nat /\ bn_neg n = false /\ bn_mag n = N /\ st_rbits s = nb /\ 1 <= nb /\ 2 ^ (nb - 1) <= N < 2 ^ nb.

Definition fix_inv (r d : bnref) (m dq N j : Z) (s : ST) : Prop :=
  let x := getbn r s in let y := getbn d s in
  bn_norm x /\ bn_neg x = false /\ bn_mag x = m - (dq + j) * N /\
  bn_norm y /\ bn_neg y = false /\ bn_mag y = dq + j.

Lemma recp_fix_loop_spec : forall fuel r d m dq N nb j F s,
  recp_ok s N nb -> (r < length (st_bns s))%nat -> (d < length (st_bns s))%nat -> ndiff r ROne -> ndiff d ROne -> ndiff r d ->
  ndiff r RRecpN -> ndiff d RRecpN ->
  0 <= j <= 3 -> 0 <= dq -> (dq + 4) * N > m -> m < N * N -> fix_inv r d m dq N j s -> (4 - j < Z.of_nat fuel) ->
  hoare F s (recp_fix_loop ops fuel r d j) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [r; d] s s' /\
     let x := getbn r s' in bn_norm x /\ bn_neg x = false /\ bn_mag x = m mod N /\ (bn_top x <= bn_top (getbn r s))%nat).
Proof.
  induction fuel as [|f IH]; intros r d m dq N nb j F s Hok Vr Vd Nr1 Nd1 Nrd NrN NdN Hj Hdq Hest HmNN Hinv Hfuel; [lia|].
  apply hoare_wf. intros Hs. cbn [recp_fix_loop].
  pose proof Hok as (Nn & Tn & Negn & MagN & _ & Hnb & HNb). cbv zeta in Nn, Tn, Negn, MagN.
  assert (VN : (RRecpN < length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; unfold RRecpN, NFIX; lia).
  pose proof (st_wf_okv RRecpN s Hs VN) as HNv. pose proof (st_wf_okv r s Hs Vr) as Hrv. pose proof (st_wf_okv d s Hs Vd) as Hdv.
  destruct Hinv as (X1 & X2 & X3 & Y1 & Y2 & Y3). cbv zeta in X1, X2, X3, Y1, Y2, Y3.
  assert (HNpos : 0 < N) by (assert (0 < 2 ^ (nb - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
  eapply hoare_bind; [apply BN_ucmp_spec; assumption|]. intros c s1 _ [-> ->].
  destruct (ucmp_okv_spec (getbn r s) (getbn RRecpN s) Hrv HNv X1 Nn) as (U1 & U2 & U3). rewrite MagN in U1, U2, U3.
  destruct (Z.ltb_spec (ucmp_pure (getbn r s) (getbn RRecpN s)) 0) as [Hc|Hc].
  - apply hoare_ret. split; [apply keeps_refl|]. cbv zeta. split; [exact X1|]. split; [exact X2|]. split; [|lia].
    specialize (U2 Hc). rewrite X3 in *. pose proof (okv_mag_nonneg (getbn r s) Hrv) as H0. rewrite X3 in H0.
    apply (Z.mod_unique m N (dq + j)); lia.
  - assert (Hge : N <= bn_mag (getbn r s)).
    { destruct (Z.eq_dec (ucmp_pure (getbn r s) (getbn RRecpN s)) 0) as [E|E]; [rewrite (U3 E); lia|]. assert (0 < ucmp_pure (getbn r s) (getbn RRecpN s)) by lia. specialize (U1 H). lia. }
    assert (Hj2 : j <= 2) by (rewrite X3 in Hge; nia).
    destruct (Z.ltb_spec 2 j); [lia|].
    eapply hoare_bind; [apply BN_usub_spec; try assumption; rewrite MagN; exact Hge|].
    intros [] s2 Hs2 (r2 & -> & (P1 & P2 & P3 & P4)). rewrite MagN in P2.
    set (s2 := setbn r r2 s) in *.
    assert (L2 : length (st_bns s2) = length (st_bns s)) by (unfold s2; apply length_setbn).
    assert (Ed2 : getbn d s2 = getbn d s) by (unfold s2; apply getbn_setbn_other; exact Nrd).
    pose proof (st_wf_okv d s2 Hs2 ltac:(rewrite L2; exact Vd)) as Hdv2. rewrite Ed2 in Hdv2.
    assert (Htopd : (bn_top (getbn d s) <= 64)%nat).
    { apply (Nat.le_trans _ (bn_top (getbn RRecpN s))); [|lia]. apply (norm_top_le _ _ HNv Hdv Y1). rewrite MagN, Y3. nia. }
    eapply hoare_bind; [apply BN_add_word_spec; try rewrite L2; try rewrite Ed2; try assumption; try (unfold BW; lia); unfold BG_DMAX; lia|].
    intros [] s3 Hs3 (d3 & -> & (Q1 & Q2 & Q3 & Q4)). rewrite Ed2 in Q1.
    set (s3 := setbn d d3 s2) in *.
    assert (L3 : length (st_bns s3) = length (st_bns s)) by (unfold s3; rewrite length_setbn; exact L2).
    assert (Er3 : getbn r s3 = r2) by (unfold s3, s2; rewrite getbn_setbn_other by (apply ndiff_sym; exact Nrd); apply getbn_setbn_same; exact Vr).
    assert (Ed3 : getbn d s3 = d3) by (unfold s3; apply getbn_setbn_same; rewrite L2; exact Vd).
    assert (EN3 : getbn RRecpN s3 = getbn RRecpN s).
    { unfold s3, s2. rewrite getbn_setbn_other by exact NdN. apply getbn_setbn_other. exact NrN. }
    eapply hoare_mono.
    { apply (IH r d m dq N nb (j + 1)); try rewrite L3; try assumption; try lia.
      - unfold recp_ok. cbv zeta. rewrite EN3. exact Hok.
      - unfold fix_inv. cbv zeta. rewrite Er3, Ed3. repeat split; try assumption; lia. }
    intros [] s4 _ (K4 & X4). cbv zeta in X4. rewrite Er3 in X4. change (gx_used (st_ctx s3)) with (gx_used (st_ctx s)) in K4. split.
    + eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [eapply keeps_trans; [apply (keeps_setbn _ r r2 s)|apply (keeps_setbn _ d d3 s2)]|exact K4]].
      intros x Hin _. cbn [app] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; subst x; cbn; auto.
    + cbv zeta. destruct X4 as (A1 & A2 & A3 & A4). repeat split; try assumption. lia.
Qed.

Definition recp_st (s : ST) (N nb : Z) : Prop :=
  st_rshift s = 0 \/
  (st_rshift s = 2 * nb /\ let x := getbn RRecpNr s in bn_canon x /\ bn_neg x = false /\ bn_mag x = 2 ^ (2 * nb) / N).

Definition keepsR (u : nat) (outs : list bnref) (s s' : ST) : Prop :=
  keeps0 u (RRecpNr :: outs) s s' /\ st_ri s' = st_ri s /\ st_n0 s' = st_n0 s /\ st_rbits s' = st_rbits s.

Definition div_recp_pre (r rm : bnref) (s : ST) (N : Z) : Prop :=
  live r s /\ live rm s /\ ndiff r ROne /\ ndiff r rm /\ ndiff r RRecpN /\ ndiff r RRecpNr /\ ndiff rm RRecpNr /\
  (length (gx_frames (st_ctx s)) + 3 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 8 <= BG_POOL)%nat /\
  bn_canon (getbn rm s) /\ bn_neg (getbn rm s) = false /\ bn_mag (getbn rm s) < N * N.

Lemma pow2_bits_le : forall N nb t, 1 <= nb -> 2 ^ (nb - 1) <= N -> N < Bp t -> nb <= 64 * Z.of_nat t.
Proof.
  intros N nb t Hnb H1 H2. rewrite Bp_pow2 in H2. destruct (Z.le_gt_cases nb (64 * Z.of_nat t)) as [|Hgt]; [assumption|exfalso].
  assert (2 ^ (64 * Z.of_nat t) <= 2 ^ (nb - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma BN_div_recp_spec : forall r rm F s N nb,
  recp_ok s N nb -> recp_st s N nb -> div_recp_pre r rm s N ->
  hoare F s (BN_div_recp ops None (Some r) rm) (fun _ s' =>
     keepsR (gx_used (st_ctx s)) [r] s s' /\ recp_ok s' N nb /\ recp_st s' N nb /\
     nnmod_post (bn_mag (getbn rm s)) N (bn_top (getbn RRecpN s)) (getbn r s')).
Proof.
  intros r rm F s N nb Hok Hst (Lr & Lm & Nr1 & Nrm & NrN & NrNr & NmNr & Hdepth & Hpool & Cm & Negm & HmNN).
  unfold BN_div_recp. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, Lm. fold u in Lr, Lm.
  set (m := getbn rm s) in *. set (n := getbn RRecpN s) in *.
  pose proof Hok as (Nn & Tn & Negn & MagN & Ebits & Hnb & HNb). cbv zeta in Nn, Tn, Negn, MagN. fold n in Nn, Tn, Negn, MagN.
  assert (HNpos : 0 < N) by (assert (0 < 2 ^ (nb - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros d s1 Hs1 (Ed & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Ed, Eu1.
  pose proof (inner_get u d s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Ed; unfold RPool; lia)) as I1.
  apply hoare_bind_ret.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros a s2 Hs2 (Ea & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & _). rewrite Eu1 in Ea, Eu2.
  pose proof (inner_get u a s1 s2 Len2 Sc2 Oth2 ltac:(rewrite Ea; unfold RPool; lia)) as I2.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu2; unfold BG_POOL in *; lia|].
  intros b s3 Hs3 (Eb & Eu3 & Ef3 & Sc3 & Len3 & Oth3 & _). rewrite Eu2 in Eb, Eu3.
  pose proof (inner_get u b s2 s3 Len3 Sc3 Oth3 ltac:(rewrite Eb; unfold RPool; lia)) as I3.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) I3) as I03. cbn [app] in I03.
  assert (G3 : forall x, (x < NFIX + u)%nat -> getbn x s3 = getbn x s) by (intros x Hx; apply (inner_get_slot _ _ _ _ x I03 Hx); intros []).
  assert (Ef3' : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]) by (rewrite Ef3, Ef2, Ef1; exact Ef0).
  assert (Hlive3 : forall x, (x < NFIX + S (S (S u)))%nat -> (x < length (st_bns s3))%nat).
  { intros x Hx. apply live_valid; [exact Hs3|]. unfold live. rewrite Eu3. exact Hx. }
  assert (HfixN : (RRecpN < NFIX + u)%nat) by (unfold RRecpN, NFIX; lia).
  assert (HfixNr : (RRecpNr < NFIX + u)%nat) by (unfold RRecpNr, NFIX; lia).
  assert (Sc03 : scal_same s s3) by (destruct I03 as (_ & H & _); exact H).
  pose proof (st_wf_okv rm s3 Hs3 (Hlive3 rm ltac:(lia))) as Hmv. rewrite (G3 rm Lm) in Hmv. fold m in Hmv.
  pose proof (st_wf_okv RRecpN s3 Hs3 (Hlive3 RRecpN ltac:(lia))) as HNv. rewrite (G3 _ HfixN) in HNv. fold n in HNv.
  destruct Cm as [Nm Zm].
  eapply hoare_bind; [apply BN_ucmp_spec; apply Hlive3; lia|]. intros c s3' _ [-> ->]. rewrite (G3 rm Lm), (G3 _ HfixN). fold m n.
  destruct (ucmp_okv_spec m n Hmv HNv Nm Nn) as (U1 & U2 & U3). rewrite MagN in U1, U2, U3.
  assert (Hfinal : forall s6, st_wf s6 -> gx_frames (st_ctx s6) = gx_frames (st_ctx s) ++ [u] ->
            (length (st_bns s) <= length (st_bns s6))%nat -> slots_same u [RRecpNr; r; d; a; b] s s6 ->
            st_ri s6 = st_ri s -> st_n0 s6 = st_n0 s -> st_rbits s6 = st_rbits s ->
            recp_st s6 N nb -> nnmod_post (bn_mag m) N (bn_top n) (getbn r s6) ->
            hoare F s6 (BN_CTX_end ops) (fun _ s' => keepsR u [r] s s' /\ recp_ok s' N nb /\ recp_st s' N nb /\
                                                     nnmod_post (bn_mag m) N (bn_top n) (getbn r s'))).
  { intros s6 Hs6 Ef6 CL6 Sl6 Eri6 En06 Erb6 Hst6 Hpost6.
    eapply hoare_mono; [apply (BN_CTX_end_spec F s6 (gx_frames (st_ctx s)) u); exact Ef6|].
    intros [] s7 Hs7 (Eb7 & Sc7 & Eu7 & Ef7).
    assert (G7 : forall x, getbn x s7 = getbn x s6) by (intros x; unfold getbn; rewrite Eb7; reflexivity).
    destruct Sc7 as (S1 & S2 & S3 & S4).
    assert (Sl7 : slots_same u [RRecpNr; r] s s7).
    { intros x Hx Hnin. rewrite G7. apply Sl6; [exact Hx|]. intros Hin. cbn [In] in Hin, Hnin.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; try (apply Hnin; auto; fail); subst x; rewrite ?Ed, ?Ea, ?Eb in Hx; unfold RPool in Hx; lia. }
    split; [|split; [|split]].
    - split; [split; [|exact Sl7]|repeat split; congruence]. unfold ctx_keep. rewrite Eb7. split; [exact CL6|]. split; assumption.
    - unfold recp_ok. cbv zeta. rewrite (Sl7 RRecpN HfixN) by (intros [E|[E|[]]]; [discriminate|apply NrN; exact E]).
      rewrite S3, Erb6. exact Hok.
    - unfold recp_st in *. cbv zeta in *. rewrite G7, S4. exact Hst6.
    - rewrite G7. exact Hpost6. }
  assert (Ld : (d < length (st_bns s3))%nat) by (apply Hlive3; rewrite Ed; unfold RPool; lia).
  assert (Nd1 : ndiff d ROne) by (rewrite Ed; unfold ndiff, RPool, NFIX, ROne; lia).
  destruct (Z.ltb_spec (ucmp_pure m n) 0) as [Hc|Hc].
  -
    specialize (U2 Hc).
    eapply hoare_bind; [apply BN_zero_spec; [exact Ld|exact Nd1]|].
    intros [] s4 Hs4 (d4 & -> & _).
    eapply hoare_bind; [apply BN_copy_spec; try rewrite length_setbn; try (apply Hlive3; lia); exact Nr1|].
    intros [] s5 Hs5 (r5 & -> & T5 & N5 & B5).
    rewrite (getbn_setbn_other d rm) in T5, N5, B5 by (rewrite Ed; unfold RPool; lia). rewrite (G3 rm Lm) in T5, N5, B5. fold m in T5, N5, B5.
    assert (Vr4 : (r < length (st_bns (setbn d d4 s3)))%nat) by (rewrite length_setbn; apply Hlive3; lia).
    apply Hfinal; try assumption.
    + rewrite !length_setbn. destruct I03 as (L & _). exact L.
    + intros x Hx Hnin. rewrite getbn_setbn_other by (intros ->; apply Hnin; cbn; auto).
      rewrite getbn_setbn_other by (intros ->; apply Hnin; cbn; auto). apply G3. exact Hx.
    + destruct Sc03 as (S1 & _). exact S1.
    + destruct Sc03 as (_ & S2 & _). exact S2.
    + destruct Sc03 as (_ & _ & S3 & _). exact S3.
    + unfold recp_st in *. cbv zeta in *. destruct Sc03 as (_ & _ & _ & S4). cbn [setbn set_bns st_rshift]. rewrite S4.
      rewrite (getbn_setbn_other r RRecpNr) by exact NrNr. rewrite (getbn_setbn_other d RRecpNr) by (rewrite Ed; unfold RPool, RRecpNr, NFIX; lia).
      rewrite (G3 _ HfixNr). exact Hst.
    + rewrite getbn_setbn_same by exact Vr4. unfold nnmod_post.
      pose proof (st_wf_okv r _ Hs5 ltac:(rewrite length_setbn; exact Vr4)) as Hr5. rewrite getbn_setbn_same in Hr5 by exact Vr4.
      assert (Em5 : bn_mag r5 = bn_mag m) by (apply mag_of_firstn_eq; assumption).
      assert (Nn5 : bn_norm r5) by (eapply norm_of_firstn_eq; eassumption).
      split; [split; [exact Nn5|intros _; rewrite N5; exact Negm]|]. split; [rewrite N5; exact Negm|]. split.
      * rewrite Em5. symmetry. apply Z.mod_small. split; [apply okv_mag_nonneg; exact Hmv|exact U2].
      * apply (norm_top_le n r5 HNv Hr5 Nn5). rewrite Em5, MagN. lia.
  -
    assert (HgeN : N <= bn_mag m).
    { destruct (Z.eq_dec (ucmp_pure m n) 0) as [E|E]; [rewrite (U3 E); lia|]. assert (H : 0 < ucmp_pure m n) by lia. specialize (U1 H). lia. }
    eapply hoare_bind; [apply BN_num_bits_spec; apply Hlive3; lia|]. intros i0 s3' _ [-> ->]. rewrite (G3 rm Lm). fold m.
    apply hoare_bind_getst.
    destruct Sc03 as (Sri & Sn0 & Srb & Srs).
    assert (Hnbt0 : nb <= 64 * Z.of_nat (bn_top n)) by (apply (pow2_bits_le N nb (bn_top n) Hnb); [lia| rewrite <- MagN; apply okv_mag_lt; exact HNv]).
    assert (RNGnb : forall sh, sh = 0 \/ sh = 2 * nb ->
              ((0 <=? nb) && (nb <? 16777216) && (-2147483648 <=? sh) && (sh <? 2147483648)) = true).
    { intros sh Hsh. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. clear - Hnb Hnbt0 Tn Hsh. lia. }
    unfold recp_rng at 1. rewrite Srb, Srs, Ebits.
    rewrite (RNGnb (st_rshift s)) by (destruct Hst as [E0|[E2 _]]; [left; exact E0| right; exact E2]). cbn [negb].
    destruct (num_bits_pure_spec m Hmv Nm) as (B0 & _ & B2 & _). specialize (B2 ltac:(lia)).
    assert (EN2 : 2 ^ (2 * nb) = 2 ^ nb * 2 ^ nb) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hi0 : num_bits_pure m <= 2 * nb).
    { destruct (Z.le_gt_cases (num_bits_pure m) (2 * nb)) as [|Hgt]; [assumption|exfalso].
      assert (2 ^ (2 * nb) <= 2 ^ (num_bits_pure m - 1)) by (apply Z.pow_le_mono_r; lia). nia. }
    set (i := if num_bits_pure m <? 2 * nb then 2 * nb else num_bits_pure m).
    assert (Ei : i = 2 * nb) by (unfold i; destruct (Z.ltb_spec (num_bits_pure m) (2 * nb)); lia).
    rewrite Ei. clear i Ei.
    pose proof (pow2_bits_le N nb (bn_top n) Hnb ltac:(lia) ltac:(rewrite <- MagN; apply okv_mag_lt; exact HNv)) as Hnbt.

    eapply hoare_bind with (R := fun _ sR => gx_frames (st_ctx sR) = gx_frames (st_ctx s) ++ [u] /\ gx_used (st_ctx sR) = S (S (S u)) /\
          (length (st_bns s) <= length (st_bns sR))%nat /\ slots_same u [RRecpNr] s sR /\
          st_ri sR = st_ri s /\ st_n0 sR = st_n0 s /\ st_rbits sR = nb /\ st_rshift sR = 2 * nb /\
          (let x := getbn RRecpNr sR in bn_canon x /\ bn_neg x = false /\ bn_mag x = 2 ^ (2 * nb) / N)).
    { destruct (Z.eqb_spec (2 * nb) (st_rshift s)) as [Esh|Nsh].
      - apply hoare_ret. destruct Hst as [E0|[_ HNr]]; [lia|]. cbv zeta in HNr. rewrite (G3 _ HfixNr).
        split; [exact Ef3'|]. split; [exact Eu3|]. destruct I03 as (L & _ & Sl). split; [exact L|]. split; [intros x Hx _; apply G3; exact Hx|].
        split; [exact Sri|]. split; [exact Sn0|]. split; [rewrite Srb; exact Ebits|]. split; [rewrite Srs; lia|exact HNr].
      - eapply hoare_bind.
        { apply (BN_reciprocal_spec RRecpNr RRecpN (2 * nb)). unfold reciprocal_pre, live. rewrite Eu3, Ef3', length_app, (G3 _ HfixN). cbn [length]. fold n.
          split; [lia|]. split; [lia|]. split; [unfold ndiff, RRecpNr, ROne; lia|]. split; [unfold ndiff, RRecpNr, RRecpN; lia|].
          split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact Nn|]. split; [lia|]. split; [exact Negn|].
          split; [lia|]. split; [|unfold BG_DMAX; lia].
          assert (2 * nb / 64 <= 2 * Z.of_nat (bn_top n)) by (apply Z.div_le_upper_bound; lia). unfold BG_DMAX. lia. }
        intros sh s4 Hs4 (-> & K4 & C4). rewrite Eu3 in K4. rewrite (G3 _ HfixN) in C4. fold n in C4. rewrite MagN in C4.
        apply hoare_bind_getst. eapply hoare_mono; [apply hoare_setrecp with (Q := fun _ s' => s' = set_recp (st_rbits s4) (2 * nb) s4); reflexivity|].
        intros [] s5 _ ->. destruct K4 as [[(L4 & U4 & F4) Sl4] (R1 & R2 & R3 & R4)].
        cbn [set_recp st_ctx st_bns st_ri st_n0 st_rbits st_rshift]. rewrite F4, U4. split; [exact Ef3'|]. split; [exact Eu3|].
        destruct I03 as (L & _ & _). split; [lia|]. split.
        + intros x Hx Hnin. change (getbn x (set_recp (st_rbits s4) (2 * nb) s4)) with (getbn x s4). rewrite Sl4 by (try lia; exact Hnin). apply G3. exact Hx.
        + split; [congruence|]. split; [congruence|]. split; [rewrite R3, Srb; exact Ebits|]. split; [reflexivity|exact C4]. }
    intros [] sR HsR (EfR & EuR & LenR & SlR & EriR & En0R & ErbR & ErsR & HNr). cbv zeta in HNr. destruct HNr as (CNr & NegNr & MagNr).
    apply hoare_bind_getst. unfold recp_rng at 1. rewrite ErsR, ErbR. rewrite (RNGnb (2 * nb)) by (right; reflexivity). cbn [negb].
    destruct (Z.eqb_spec (2 * nb) (-1)) as [|_]; [lia|].
    assert (HliveR : forall x, (x < NFIX + S (S (S u)))%nat -> (x < length (st_bns sR))%nat).
    { intros x Hx. apply live_valid; [exact HsR|]. unfold live. rewrite EuR. exact Hx. }
    assert (GR : forall x, (x < NFIX + u)%nat -> x <> RRecpNr -> getbn x sR = getbn x s) by (intros x Hx Hn; apply SlR; [exact Hx|intros [E|[]]; apply Hn; symmetry; exact E]).

    set (Acc := fun sX : ST => gx_frames (st_ctx sX) = gx_frames (st_ctx s) ++ [u] /\ gx_used (st_ctx sX) = S (S (S u)) /\
          (length (st_bns s) <= length (st_bns sX))%nat /\ slots_same u [RRecpNr; r; d; a; b] s sX /\
          st_ri sX = st_ri s /\ st_n0 sX = st_n0 s /\ st_rbits sX = nb /\ st_rshift sX = 2 * nb /\
          getbn RRecpNr sX = getbn RRecpNr sR /\ getbn rm sX = m /\ getbn RRecpN sX = n).
    assert (Hda : ndiff d a /\ ndiff d b /\ ndiff a b) by (rewrite Ed, Ea, Eb; unfold ndiff, RPool; lia).
    destruct Hda as (Nda & Ndb & Nab).
    assert (Htmp : forall x, x = d \/ x = a \/ x = b -> (NFIX + u <= x)%nat) by (intros x [E|[E|E]]; subst x; rewrite ?Ed, ?Ea, ?Eb; unfold RPool; lia).
    assert (Hwr : forall x, x = r \/ x = d \/ x = a \/ x = b -> ndiff x rm /\ ndiff x RRecpNr /\ ndiff x RRecpN).
    { intros x [E|E]; [subst x; auto|]. pose proof (Htmp x E) as Hge. clear - Hge Lm. unfold ndiff, RRecpNr, RRecpN, NFIX in *. lia. }
    assert (AccR : Acc sR).
    { unfold Acc. split; [exact EfR|]. split; [exact EuR|]. split; [exact LenR|]. split.
      - intros x Hx Hnin. apply SlR; [exact Hx|]. intros [E|[]]. apply Hnin. left. exact E.
      - split; [exact EriR|]. split; [exact En0R|]. split; [exact ErbR|]. split; [exact ErsR|]. split; [reflexivity|].
        split; [apply GR; [exact Lm|unfold ndiff in NmNr; exact NmNr]|apply GR; [exact HfixN|unfold RRecpN, RRecpNr; lia]]. }
    assert (Acc_set : forall x bx sX, x = r \/ x = d \/ x = a \/ x = b -> Acc sX -> Acc (setbn x bx sX)).
    { intros x bx sX Hx (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). destruct (Hwr x Hx) as (W1 & W2 & W3).
      unfold Acc. rewrite length_setbn. cbn [setbn set_bns st_ctx st_ri st_n0 st_rbits st_rshift].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
      - intros y Hy Hnin. fold (setbn x bx sX). rewrite getbn_setbn_other; [apply A4; assumption|].
        intros ->. apply Hnin. cbn. destruct Hx as [E|[E|[E|E]]]; rewrite E; auto 10.
      - fold (setbn x bx sX). rewrite !getbn_setbn_other by assumption. repeat split; assumption. }
    assert (Acc_keeps : forall x sX sY, x = r \/ x = d \/ x = a \/ x = b -> Acc sX -> keeps (S (S (S u))) [x] sX sY -> Acc sY).
    { intros x sX sY Hx (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) [[(K1 & K2 & K3) K4] (K5 & K6 & K7 & K8)].
      destruct (Hwr x Hx) as (W1 & W2 & W3).
      unfold Acc. split; [congruence|]. split; [congruence|]. split; [lia|]. split.
      - intros y Hy Hnin. rewrite K4; [apply A4; assumption|lia|]. intros [E|[]]. apply Hnin. subst y. cbn. destruct Hx as [E|[E|[E|E]]]; rewrite E; auto 10.
      - split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
        assert (E1 : getbn RRecpNr sY = getbn RRecpNr sX) by (apply K4; [unfold RRecpNr, NFIX; lia|intros [E|[]]; apply W2; exact E]).
        assert (E2 : getbn rm sY = getbn rm sX) by (apply K4; [lia|intros [E|[]]; apply W1; exact E]).
        assert (E3 : getbn RRecpN sY = getbn RRecpN sX) by (apply K4; [unfold RRecpN, NFIX; lia|intros [E|[]]; apply W3; exact E]).
        rewrite E1, E2, E3. repeat split; assumption. }
    assert (Acc_live : forall sX x, Acc sX -> st_wf sX -> (x < NFIX + S (S (S u)))%nat -> (x < length (st_bns sX))%nat).
    { intros sX x (_ & A2 & _) HsX Hx. apply live_valid; [exact HsX|]. unfold live. rewrite A2. exact Hx. }
    assert (Va_lt : (a < NFIX + S (S (S u)))%nat) by (rewrite Ea; unfold RPool; lia).
    assert (Vb_lt : (b < NFIX + S (S (S u)))%nat) by (rewrite Eb; unfold RPool; lia).
    assert (Vd_lt : (d < NFIX + S (S (S u)))%nat) by (rewrite Ed; unfold RPool; lia).
    assert (Na1 : ndiff a ROne) by (rewrite Ea; unfold ndiff, RPool, NFIX, ROne; lia).
    assert (Nb1 : ndiff b ROne) by (rewrite Eb; unfold ndiff, RPool, NFIX, ROne; lia).
    pose proof (okv_mag_nonneg m Hmv) as Hm0.
    assert (Hpnb : 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
    assert (HBn : 2 ^ nb <= Bp (bn_top n)) by (rewrite Bp_pow2; apply Z.pow_le_mono_r; lia).

    pose proof AccR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EmR & EnR).
    eapply hoare_bind; [apply BN_rshift_spec; [apply (Acc_live sR a AccR HsR Va_lt)|exact Na1|apply (Acc_live sR rm AccR HsR); lia|lia]|].
    intros [] s5 Hs5 (a5 & -> & Ca5 & Ma5 & Na5 & Ta5). rewrite EmR in Ma5, Na5, Ta5. specialize (Na5 Negm).
    pose proof (Acc_set a a5 sR ltac:(auto) AccR) as Acc5. set (s5 := setbn a a5 sR) in *.
    pose proof Acc5 as (Ef5 & Eu5 & _ & _ & _ & _ & _ & _ & ENr5 & Em5 & En5).
    assert (Ega5 : getbn a s5 = a5) by (unfold s5; apply getbn_setbn_same; apply (Acc_live sR a AccR HsR Va_lt)).
    pose proof (st_wf_okv a s5 Hs5 (Acc_live s5 a Acc5 Hs5 Va_lt)) as Hav5. rewrite Ega5 in Hav5.
    assert (Ha5lt : bn_mag a5 < 2 ^ nb) by (rewrite Ma5; apply Z.div_lt_upper_bound; [lia|nia]).
    assert (Ta5' : (bn_top a5 <= bn_top n)%nat) by (apply (norm_top_lt a5 _ Hav5 (proj1 Ca5)); lia).
    pose proof (st_wf_okv RRecpNr s5 Hs5 (Acc_live s5 RRecpNr Acc5 Hs5 ltac:(unfold RRecpNr, NFIX; lia))) as HNrv. rewrite ENr5 in HNrv.
    assert (HNrle : bn_mag (getbn RRecpNr sR) <= 2 * 2 ^ nb).
    { rewrite MagNr, EN2. apply Z.div_le_upper_bound; [lia|]. assert (E2 : 2 ^ nb = 2 * 2 ^ (nb - 1)) by (replace nb with (Z.succ (nb - 1)) at 1 by lia; apply Z.pow_succ_r; lia). nia. }
    assert (TNr : (bn_top (getbn RRecpNr sR) <= bn_top n + 1)%nat).
    { apply (norm_top_lt _ _ HNrv (proj1 CNr)). replace (bn_top n + 1)%nat with (S (bn_top n)) by lia. rewrite Bp_S. unfold BW. lia. }

    eapply hoare_bind.
    { apply (BN_mul_spec b a RRecpNr). unfold mul_pre, live. rewrite Eu5, Ef5, length_app, Ega5, ENr5. cbn [length].
      split; [exact Vb_lt|]. split; [exact Va_lt|]. split; [unfold RRecpNr, NFIX; lia|]. split; [exact Nb1|].
      split; [unfold ndiff; apply ndiff_sym; exact Nab|]. split; [rewrite Eb; unfold ndiff, RPool, RRecpNr, NFIX; lia|].
      split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; lia. }
    intros [] s6 Hs6 (K6 & Cb6 & Mb6 & Nb6 & _). rewrite Eu5 in K6. rewrite Ega5, ENr5 in Mb6, Nb6. rewrite Na5, NegNr in Nb6. cbn [xorb andb] in Nb6.
    pose proof (Acc_keeps b s5 s6 ltac:(auto) Acc5 K6) as Acc6.

    apply hoare_bind_getst. unfold recp_rng at 1.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Acc6))))))), (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Acc6)))))))).
    rewrite (RNGnb (2 * nb)) by (right; reflexivity). cbn [negb].
    replace (2 * nb - nb) with nb by lia.
    eapply hoare_bind; [apply BN_rshift_spec; [apply (Acc_live s6 d Acc6 Hs6 Vd_lt)|exact Nd1|apply (Acc_live s6 b Acc6 Hs6 Vb_lt)|lia]|].
    intros [] s7 Hs7 (d7 & -> & Cd7 & Md7 & Nd7 & _). rewrite Mb6 in Md7. specialize (Nd7 Nb6).
    pose proof (Acc_set d d7 s6 ltac:(auto) Acc6) as Acc7. set (s7 := setbn d d7 s6) in *.
    assert (Vd7 : (d < length (st_bns s7))%nat) by (apply (Acc_live s7 d Acc7 Hs7 Vd_lt)).
    assert (Egd7 : getbn d s7 = d7) by (unfold s7; apply getbn_setbn_same; apply (Acc_live s6 d Acc6 Hs6 Vd_lt)).
    pose proof (st_wf_ok d s7 Hs7 Vd7 Nd1) as Hd7ok. rewrite Egd7 in Hd7ok.
    apply (hoare_bind_update d (fun x => bn_with_neg x false)); try rewrite Egd7; try assumption; try reflexivity.
    pose proof (Acc_set d (bn_with_neg d7 false) s7 ltac:(auto) Acc7) as Acc8. set (s8 := setbn d (bn_with_neg d7 false) s7) in *.
    pose proof Acc8 as (Ef8 & Eu8 & _ & _ & _ & _ & _ & _ & ENr8 & Em8 & En8).
    assert (Egd8 : getbn d s8 = bn_with_neg d7 false) by (unfold s8; apply getbn_setbn_same; exact Vd7).

    set (dq := bn_mag d7) in *.
    pose proof (recp_estimate (bn_mag m) N nb (2 * nb) Hnb HNb ltac:(split; [lia|rewrite EN2; nia]) ltac:(lia)) as Hest. cbv zeta in Hest.
    replace (2 * nb - nb) with nb in Hest by lia. rewrite <- MagNr, <- Ma5 in Hest. rewrite <- Md7 in Hest. fold dq in Hest.
    destruct Hest as (Hdq0 & Hlo & Hhi).
    assert (Hdqlt : dq < N) by nia.
    eapply hoare_wf. intros Hs8.
    pose proof (st_wf_okv d s8 Hs8 ltac:(unfold s8; rewrite length_setbn; exact Vd7)) as Hdv8. rewrite Egd8 in Hdv8.
    assert (Td8 : (bn_top d7 <= bn_top n)%nat).
    { apply (norm_top_le n (bn_with_neg d7 false) HNv Hdv8 (proj1 Cd7)). rewrite MagN. change (bn_mag (bn_with_neg d7 false)) with dq. lia. }

    eapply hoare_bind.
    { apply (BN_mul_spec b RRecpN d). unfold mul_pre, live. rewrite Eu8, Ef8, length_app, Egd8, En8. cbn [length bn_with_neg bn_top].
      split; [exact Vb_lt|]. split; [unfold RRecpN, NFIX; lia|]. split; [exact Vd_lt|]. split; [exact Nb1|].
      split; [rewrite Eb; unfold ndiff, RPool, RRecpN, NFIX; lia|]. split; [unfold ndiff; apply ndiff_sym; exact Ndb|].
      split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; lia. }
    intros [] s9 Hs9 (K9 & Cb9 & Mb9 & _ & _). rewrite Eu8 in K9. rewrite Egd8, En8, MagN in Mb9. change (bn_mag (bn_with_neg d7 false)) with dq in Mb9.
    pose proof (Acc_keeps b s8 s9 ltac:(auto) Acc8 K9) as Acc9.
    pose proof Acc9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Em9 & En9).

    assert (Vr9 : (r < length (st_bns s9))%nat) by (apply (Acc_live s9 r Acc9 Hs9); lia).
    eapply hoare_bind; [apply BN_usub_spec; [exact Vr9|exact Nr1|apply (Acc_live s9 rm Acc9 Hs9); lia|apply (Acc_live s9 b Acc9 Hs9 Vb_lt)|exact (proj1 Cb9)|rewrite Em9, Mb9; lia]|].
    intros [] s10 Hs10 (r10 & -> & (Pn & Pm & Pg & Pt)). rewrite Em9, Mb9 in Pm.
    pose proof (Acc_set r r10 s9 ltac:(auto) Acc9) as Acc10. set (s10 := setbn r r10 s9) in *.
    assert (Vr10 : (r < length (st_bns s10))%nat) by (apply (Acc_live s10 r Acc10 Hs10); lia).
    assert (Egr10 : getbn r s10 = r10) by (unfold s10; apply getbn_setbn_same; exact Vr9).
    pose proof (st_wf_ok r s10 Hs10 Vr10 Nr1) as Hr10ok. rewrite Egr10 in Hr10ok.
    apply (hoare_bind_update r (fun x => bn_with_neg x false)); try rewrite Egr10; try assumption; try reflexivity.
    pose proof (Acc_set r (bn_with_neg r10 false) s10 ltac:(auto) Acc10) as Acc11. set (s11 := setbn r (bn_with_neg r10 false) s10) in *.
    pose proof Acc11 as (_ & Eu11 & _ & _ & _ & _ & Erb11 & _ & _ & _ & En11).
    assert (Egr11 : getbn r s11 = bn_with_neg r10 false) by (unfold s11; apply getbn_setbn_same; exact Vr10).
    assert (Egd11 : getbn d s11 = bn_with_neg d7 false).
    { unfold s11, s10. rewrite !getbn_setbn_other by (unfold ndiff; first [exact Nrd'|idtac]; rewrite ?Ed; unfold RPool; lia).
      rewrite (keeps_get _ _ _ _ d K9) by (try lia; intros [E|[]]; apply Ndb; symmetry; exact E). exact Egd8. }

    eapply hoare_wf. intros Hs11.
    eapply hoare_bind.
    { apply (recp_fix_loop_spec 5 r d (bn_mag m) dq N nb 0 F s11); try lia.
      - unfold recp_ok. cbv zeta. rewrite En11, Erb11. split; [exact Nn|]. split; [exact Tn|]. split; [exact Negn|]. split; [exact MagN|]. split; [reflexivity|]. split; [exact Hnb|exact HNb].
      - unfold s11. rewrite length_setbn. exact Vr10.
      - apply (Acc_live s11 d Acc11 Hs11 Vd_lt).
      - exact Nr1.
      - exact Nd1.
      - rewrite Ed. unfold ndiff, RPool. lia.
      - exact NrN.
      - rewrite Ed. unfold ndiff, RPool, RRecpN, NFIX. lia.
      - unfold fix_inv. cbv zeta. rewrite Egr11, Egd11. cbn [bn_with_neg bn_neg].
        change (bn_norm (bn_with_neg r10 false)) with (bn_norm r10). change (bn_norm (bn_with_neg d7 false)) with (bn_norm d7).
        change (bn_mag (bn_with_neg r10 false)) with (bn_mag r10). change (bn_mag (bn_with_neg d7 false)) with dq.
        split; [exact Pn|]. split; [reflexivity|]. split; [rewrite Pm; lia|]. split; [exact (proj1 Cd7)|]. split; [reflexivity|lia]. }
    intros [] s12 Hs12 (K12 & X12). rewrite Eu11 in K12. cbv zeta in X12. destruct X12 as (Xn & Xg & Xm & _).
    assert (Acc12 : Acc s12).
    { destruct Acc11 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). destruct K12 as [[(K1 & K2 & K3) K4] (K5 & K6' & K7 & K8)].
      unfold Acc. split; [congruence|]. split; [congruence|]. split; [lia|]. split.
      - intros y Hy Hnin. rewrite K4; [apply A4; assumption|lia|]. intros [E|[E|[]]]; apply Hnin; subst y; cbn; auto 10.
      - split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
        destruct (Hwr r ltac:(auto)) as (W1 & W2 & W3). destruct (Hwr d ltac:(auto)) as (V1 & V2 & V3).
        assert (E1 : getbn RRecpNr s12 = getbn RRecpNr s11) by (apply K4; [unfold RRecpNr, NFIX; lia|intros [E|[E|[]]]; [apply W2|apply V2]; exact E]).
        assert (E2 : getbn rm s12 = getbn rm s11) by (apply K4; [lia|intros [E|[E|[]]]; [apply W1|apply V1]; exact E]).
        assert (E3 : getbn RRecpN s12 = getbn RRecpN s11) by (apply K4; [unfold RRecpN, NFIX; lia|intros [E|[E|[]]]; [apply W3|apply V3]; exact E]).
        rewrite E1, E2, E3. repeat split; assumption. }

    assert (Vr12 : (r < length (st_bns s12))%nat) by (apply (Acc_live s12 r Acc12 Hs12); lia).
    pose proof (st_wf_ok r s12 Hs12 Vr12 Nr1) as Hr12ok.
    pose proof Acc12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Em12 & _).
    set (r13 := bn_with_neg (getbn r s12) (if is_zero_pure (getbn r s12) then false else false)).
    eapply hoare_bind with (R := fun _ sY => sY = setbn r r13 s12).
    { apply hoare_bind_get. apply hoare_bind_get. rewrite Em12, Negm.
      eapply hoare_set; try assumption; try reflexivity; try (unfold r13; destruct (is_zero_pure (getbn r s12)); exact Hr12ok). }
    intros [] s13 Hs13 ->. pose proof (Acc_set r r13 s12 ltac:(auto) Acc12) as Acc13. set (s13 := setbn r r13 s12) in *.
    assert (Vd13 : (d < length (st_bns s13))%nat) by (apply (Acc_live s13 d Acc13 Hs13 Vd_lt)).
    pose proof (st_wf_ok d s13 Hs13 Vd13 Nd1) as Hd13ok.
    set (d14 := bn_with_neg (getbn d s13) (xorb (bn_neg (getbn rm s13)) (bn_neg (getbn RRecpN s13)))).
    eapply hoare_bind with (R := fun _ sY => sY = setbn d d14 s13).
    { apply hoare_bind_get. apply hoare_bind_get. apply hoare_bind_get. eapply hoare_set; try assumption; try reflexivity. }
    intros [] s14 Hs14 ->. pose proof (Acc_set d d14 s13 ltac:(auto) Acc13) as Acc14.
    destruct Acc14 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    apply Hfinal; try assumption.
    + rewrite A7. symmetry. exact Ebits.
    + right. split; [exact A8|]. cbv zeta. rewrite A9. repeat split; assumption || apply CNr.
    + rewrite getbn_setbn_other by (rewrite Ed; unfold RPool; unfold live in *; lia). unfold s13. rewrite getbn_setbn_same by exact Vr12.
      pose proof (st_wf_okv r s13 Hs13 ltac:(unfold s13; rewrite length_setbn; exact Vr12)) as Hrv13. unfold s13 in Hrv13. rewrite getbn_setbn_same in Hrv13 by exact Vr12.
      assert (Er13 : bn_norm r13 /\ bn_neg r13 = false /\ bn_mag r13 = bn_mag m mod N).
      { unfold r13. destruct (is_zero_pure (getbn r s12)); cbn [bn_with_neg bn_neg]; (split; [exact Xn|split; [reflexivity|exact Xm]]). }
      destruct Er13 as (E1 & E2 & E3). unfold nnmod_post. split; [split; [exact E1|intros _; exact E2]|]. split; [exact E2|]. split; [exact E3|].
      apply (norm_top_le n r13 HNv Hrv13 E1). rewrite E3, MagN. pose proof (Z.mod_pos_bound (bn_mag m) N HNpos). lia.
Qed.

Definition mmr_pre (rr rx ry : bnref) (s : ST) (N : Z) : Prop :=
  live rr s /\ live rx s /\ live ry s /\ ndiff rr ROne /\ ndiff rr RRecpN /\ ndiff rr RRecpNr /\
  (length (gx_frames (st_ctx s)) + 4 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 9 <= BG_POOL)%nat /\
  (bn_top (getbn rx s) <= 127)%nat /\ (bn_top (getbn ry s) <= 127)%nat /\
  bn_neg (getbn rx s) = false /\ bn_neg (getbn ry s) = false /\
  0 <= bn_mag (getbn rx s) < N /\ 0 <= bn_mag (getbn ry s) < N.

Lemma keepsR_inner : forall u o s s', keepsR u o s s' -> (length (st_bns s) <= length (st_bns s'))%nat /\ slots_same u (RRecpNr :: o) s s'.
Proof. intros u o s s' [[(L & _) Sl] _]. split; assumption. Qed.

Lemma BN_mod_mul_reciprocal_spec : forall rr rx ry F s N nb,
  recp_ok s N nb -> recp_st s N nb -> mmr_pre rr rx ry s N ->
  hoare F s (BN_mod_mul_reciprocal ops rr rx ry) (fun _ s' =>
     keepsR (gx_used (st_ctx s)) [rr] s s' /\ recp_ok s' N nb /\ recp_st s' N nb /\
     nnmod_post (bn_mag (getbn rx s) * bn_mag (getbn ry s)) N (bn_top (getbn RRecpN s)) (getbn rr s')).
Proof.
  intros rr rx ry F s N nb Hok Hst (Lr & Lx & Ly & Nr1 & NrN & NrNr & Hdepth & Hpool & Htx & Hty & Hnx & Hny & Hx & Hy).
  unfold BN_mod_mul_reciprocal. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, Lx, Ly. fold u in Lr, Lx, Ly.
  set (x := getbn rx s) in *. set (y := getbn ry s) in *.
  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros t s1 Hs1 (Et & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Et, Eu1.
  pose proof (inner_get u t s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Et; unfold RPool; lia)) as I1.
  pose proof (inner_trans _ _ _ _ _ _ I0 I1) as I01. cbn [app] in I01.
  assert (G1 : forall z, (z < NFIX + u)%nat -> getbn z s1 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I01 Hz); intros []).
  assert (Lt1 : live t s1) by (unfold live; rewrite Eu1, Et; unfold RPool; lia).
  assert (Hl1 : forall z, (z < NFIX + u)%nat -> live z s1) by (intros z Hz; unfold live; rewrite Eu1; lia).
  assert (Ntx : forall z, (z < NFIX + u)%nat -> ndiff t z) by (intros z Hz; rewrite Et; unfold ndiff, RPool; lia).
  assert (Nt1 : ndiff t ROne) by (rewrite Et; unfold ndiff, RPool, NFIX, ROne; lia).
  eapply hoare_bind with (R := fun _ s2 => keeps (S u) [t] s1 s2 /\ bn_canon (getbn t s2) /\ bn_neg (getbn t s2) = false /\
        bn_mag (getbn t s2) = bn_mag x * bn_mag y).
  { destruct (Nat.eqb_spec rx ry) as [Exy|Nxy].
    - eapply hoare_mono; [apply BN_sqr_spec; unfold sqr_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 rx Lx); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact Lx|]. split; [exact Nt1|]. split; [apply Ntx; exact Lx|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|exact Htx].
      + intros [] s2 _ (K2 & C2 & M2 & N2 & T2). rewrite Eu1 in K2. rewrite (G1 rx Lx) in M2. fold x in M2.
        split; [exact K2|]. split; [exact C2|]. split; [exact N2|]. rewrite M2. unfold y. rewrite <- Exy. reflexivity.
    - eapply hoare_mono; [apply BN_mul_spec; unfold mul_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 rx Lx), (G1 ry Ly); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact Lx|]. split; [apply Hl1; exact Ly|]. split; [exact Nt1|].
        split; [apply Ntx; exact Lx|]. split; [apply Ntx; exact Ly|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; assumption.
      + intros [] s2 _ (K2 & C2 & M2 & N2 & T2). rewrite Eu1 in K2. rewrite (G1 rx Lx), (G1 ry Ly) in M2, N2. fold x y in M2, N2.
        split; [exact K2|]. split; [exact C2|]. split; [rewrite N2, Hnx, Hny; reflexivity|exact M2]. }
  intros [] s2 Hs2 (K2 & C2 & N2 & M2).
  pose proof (inner_of_keeps u _ _ _ _ K2 ltac:(lia)) as I2.
  pose proof (inner_trans _ _ _ _ _ _ I01 I2) as I02. cbn [app] in I02.
  assert (G2 : forall z, (z < NFIX + u)%nat -> getbn z s2 = getbn z s).
  { intros z Hz. apply (inner_get_slot _ _ _ _ z I02 Hz). intros [E|[]]. rewrite <- E, Et in Hz. unfold RPool in Hz. lia. }
  assert (Hok2 : recp_ok s2 N nb).
  { unfold recp_ok in *. cbv zeta in *. rewrite (G2 RRecpN) by (unfold RRecpN, NFIX; lia). destruct I02 as (_ & (_ & _ & E & _) & _). rewrite E. exact Hok. }
  assert (Hst2 : recp_st s2 N nb).
  { unfold recp_st in *. cbv zeta in *. rewrite (G2 RRecpNr) by (unfold RRecpNr, NFIX; lia). destruct I02 as (_ & (_ & _ & _ & E) & _). rewrite E. exact Hst. }
  eapply hoare_bind.
  { apply (BN_div_recp_spec rr t F s2 N nb Hok2 Hst2). unfold div_recp_pre, live.
    rewrite (keeps_used _ _ _ _ K2), (keeps_frames _ _ _ _ K2), Eu1, Ef1, Ef0, length_app, M2, N2. cbn [length].
    split; [lia|]. split; [rewrite Et; unfold RPool; lia|]. split; [exact Nr1|]. split; [unfold ndiff; apply ndiff_sym, Ntx; exact Lr|].
    split; [exact NrN|]. split; [exact NrNr|]. split; [apply Ntx; unfold RRecpNr, NFIX; lia|].
    split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact C2|]. split; [reflexivity|nia]. }
  intros [] s3 Hs3 (K3 & Hok3 & Hst3 & P3). rewrite (keeps_used _ _ _ _ K2), Eu1 in K3. rewrite M2, (G2 RRecpN) in P3 by (unfold RRecpN, NFIX; lia).
  destruct (keepsR_inner _ _ _ _ K3) as [Len3 Sl3]. destruct K3 as [[(_ & Eu3 & Ef3) _] (Eri3 & En03 & Erb3)].
  assert (Ef3' : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]).
  { rewrite Ef3, (keeps_frames _ _ _ _ K2), Ef1. exact Ef0. }
  eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3'|].
  intros [] s4 Hs4 (Eb4 & (S1 & S2 & S3 & S4) & Eu4 & Ef4).
  assert (G4 : forall z, getbn z s4 = getbn z s3) by (intros z; unfold getbn; rewrite Eb4; reflexivity).
  assert (Sl4 : slots_same u [RRecpNr; rr] s s4).
  { intros z Hz Hnin. rewrite G4. rewrite Sl3; [apply G2; exact Hz|lia|]. intros [E|[E|[]]]; apply Hnin; subst z; cbn; auto. }
  destruct I02 as (Len02 & (R1 & R2 & R3 & R4) & _).
  split; [|split; [|split]].
  - split; [split; [|exact Sl4]|repeat split; congruence]. unfold ctx_keep. rewrite Eb4. split; [lia|]. split; assumption.
  - unfold recp_ok in *. cbv zeta in *. rewrite G4, S3. exact Hok3.
  - unfold recp_st in *. cbv zeta in *. rewrite G4, S4. exact Hst3.
  - rewrite G4. exact P3.
Qed.

End RecpSpec.
