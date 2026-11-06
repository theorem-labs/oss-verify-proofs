(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ModSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma canon_val_nonneg : forall b : BN, bg_okv b -> bn_canon b -> 0 <= bn_val b -> bn_neg b = false /\ bn_mag b = bn_val b.
Proof.
  intros b Hb [Hn Hz] Hv. unfold bn_val in *. pose proof (okv_mag_nonneg b Hb). destruct (bn_neg b) eqn:En; [|split; reflexivity].
  assert (Hm0 : bn_mag b = 0) by lia. pose proof (Hz (proj2 (norm_zero_iff b Hb Hn) Hm0)) as Ef. congruence.
Qed.

Definition nnmod_pre (rr ra rm : bnref) (s : ST) : Prop :=
  live rr s /\ live ra s /\ live rm s /\ ndiff rr ROne /\ ndiff rr rm /\
  (length (gx_frames (st_ctx s)) < BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 4 <= BG_POOL)%nat /\
  bn_norm (getbn rm s) /\ (1 <= bn_top (getbn rm s))%nat /\
  Z.of_nat (bn_top (getbn ra s)) + 2 <= BG_DMAX /\ Z.of_nat (bn_top (getbn rm s)) + 2 <= BG_DMAX.

Definition nnmod_post (v m : Z) (top_m : nat) (r : BN) : Prop :=
  bn_canon r /\ bn_neg r = false /\ bn_mag r = v mod m /\ (bn_top r <= top_m)%nat.

Lemma BN_nnmod_spec : forall rr ra rm F s,
  nnmod_pre rr ra rm s ->
  hoare F s (BN_nnmod ops rr ra rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     nnmod_post (bn_val (getbn ra s)) (bn_mag (getbn rm s)) (bn_top (getbn rm s)) (getbn rr s')).
Proof.
  intros rr ra rm F s (Lr & La & Lm & Nr1 & Nrm & Hdepth & Hpool & Hnm & Htm & Hsa & Hsm).
  apply hoare_wf. intros Hs. unfold BN_nnmod, BN_mod. set (u := gx_used (st_ctx s)) in *.
  destruct (Nat.eqb_spec rr rm) as [E|_]; [exfalso; exact (Nrm E)|].
  set (a := getbn ra s) in *. set (m := getbn rm s) in *.
  pose proof (st_wf_okv ra s Hs (live_valid ra s Hs La)) as Ha. fold a in Ha.
  pose proof (st_wf_okv rm s Hs (live_valid rm s Hs Lm)) as Hm. fold m in Hm.
  assert (Mpos : 0 < bn_mag m) by (pose proof (okv_mag_ge m Hm Hnm ltac:(lia)); pose proof (Bp_pos (bn_top m - 1)); lia).
  pose proof (okv_mag_nonneg a Ha) as Ma.
  eapply hoare_bind.
  { apply (BN_div_spec None (Some rr) ra rm). unfold div_pre. fold u a m.
    split; [exact La|]. split; [exact Lm|]. split; [intros d Ed; discriminate|]. split.
    - intros r Er. injection Er as <-. split; [exact Lr|]. split; [exact Nr1|]. split; [exact Nrm|discriminate].
    - repeat split; assumption. }
  intros [] s1 Hs1 (K1 & _ & R1). fold u a m in K1, R1. cbn [opt_refs app] in K1.
  pose proof (R1 rr eq_refl) as R1'. cbv zeta in R1'. destruct R1' as (C1 & M1 & N1 & T1). clear R1.
  assert (Vr1 : (rr < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|eapply keeps_live; eassumption]).
  assert (Lm1 : live rm s1) by (eapply keeps_live; eassumption).
  assert (Em1 : getbn rm s1 = m) by (apply (keeps_get _ _ _ _ rm K1); [exact Lm|intros [E|[]]; apply Nrm; exact E]).
  pose proof (st_wf_okv rr s1 Hs1 Vr1) as Hr1.
  apply hoare_bind_get. set (r1 := getbn rr s1) in *.
  pose proof (Z.mod_pos_bound (bn_mag a) (bn_mag m) Mpos) as Hmb.
  destruct (bn_neg r1) eqn:Eneg; cbn [negb].
  -
    assert (Haneg : bn_neg a = true) by (destruct (bn_neg a); [reflexivity|discriminate]).
    assert (Hnz : bn_mag r1 <> 0).
    { intros Ez. destruct C1 as [Cn Cz]. rewrite (Cz (proj2 (norm_zero_iff r1 Hr1 Cn) Ez)) in Eneg. discriminate. }
    assert (Hcm : bn_canon (getbn rm s1)) by (rewrite Em1; split; [exact Hnm|intros E; lia]).
    assert (Hsz : Z.of_nat (Nat.max (bn_top (getbn rr s1)) (bn_top (getbn rm s1))) + 1 <= BG_DMAX) by (rewrite Em1; fold r1; lia).
    apply hoare_bind_get. rewrite Em1.
    assert (Hfin : forall s2, st_wf s2 -> upd1 rr s1 (signed_post (bn_mag m - bn_mag r1) (Nat.max (bn_top r1) (bn_top m))) tt s2 ->
              keeps u [rr] s s2 /\ nnmod_post (bn_val a) (bn_mag m) (bn_top m) (getbn rr s2)).
    { intros s2 Hs2 (r2 & -> & (C2 & V2 & T2)). split.
      - eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
        intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; exact Hin.
      - rewrite getbn_setbn_same by exact Vr1.
        pose proof (st_wf_okv rr _ Hs2 ltac:(rewrite length_setbn; exact Vr1)) as Hr2. rewrite getbn_setbn_same in Hr2 by exact Vr1.
        destruct (canon_val_nonneg r2 Hr2 C2 ltac:(lia)) as [N2 M2].
        unfold nnmod_post. split; [exact C2|]. split; [exact N2|]. split.
        + rewrite M2, V2. unfold bn_val. rewrite Haneg. rewrite Z.mod_opp_l_nz by lia. lia.
        + apply (norm_top_le m r2 Hm Hr2 (proj1 C2)). rewrite M2, V2. lia. }
    destruct (bn_neg m) eqn:Emneg.
    + eapply hoare_mono; [apply BN_sub_spec; try assumption; try (apply live_valid; assumption)|].
      intros [] s2 Hs2 Hu. apply Hfin; [exact Hs2|]. rewrite Em1 in Hu. fold r1 in Hu.
      replace (bn_mag m - bn_mag r1) with (bn_val r1 - bn_val m); [exact Hu|]. unfold bn_val. rewrite Eneg, Emneg. lia.
    + eapply hoare_mono; [apply BN_add_spec; try assumption; try (apply live_valid; assumption)|].
      intros [] s2 Hs2 Hu. apply Hfin; [exact Hs2|]. rewrite Em1 in Hu. fold r1 in Hu.
      replace (bn_mag m - bn_mag r1) with (bn_val r1 + bn_val m); [exact Hu|]. unfold bn_val. rewrite Eneg, Emneg. lia.
  - apply hoare_ret. split; [exact K1|]. fold r1. unfold nnmod_post. split; [exact C1|]. split; [exact Eneg|]. split; [|exact T1].
    rewrite M1. unfold bn_val. destruct (bn_neg a) eqn:Ea; [|reflexivity].

    cbn [andb] in N1. symmetry in N1. apply negb_false_iff, Nat.eqb_eq in N1.
    pose proof (bn_mag_top0 r1 N1) as E0. rewrite M1 in E0. rewrite E0. symmetry. apply Z.mod_opp_l_z; lia.
Qed.

Definition mod_mul_pre (rr ra rb rm : bnref) (s : ST) : Prop :=
  live rr s /\ live ra s /\ live rb s /\ live rm s /\ ndiff rr ROne /\ ndiff rr rm /\
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 5 <= BG_POOL)%nat /\
  bn_norm (getbn rm s) /\ (1 <= bn_top (getbn rm s))%nat /\ Z.of_nat (bn_top (getbn rm s)) + 2 <= BG_DMAX /\
  (bn_top (getbn ra s) <= 127)%nat /\ (bn_top (getbn rb s) <= 127)%nat /\
  bn_neg (getbn ra s) = false /\ bn_neg (getbn rb s) = false.

Lemma BN_mod_mul_spec : forall rr ra rb rm F s,
  mod_mul_pre rr ra rb rm s ->
  hoare F s (BN_mod_mul ops rr ra rb rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     nnmod_post (bn_mag (getbn ra s) * bn_mag (getbn rb s)) (bn_mag (getbn rm s)) (bn_top (getbn rm s)) (getbn rr s')).
Proof.
  intros rr ra rb rm F s (Lr & La & Lb & Lm & Nr1 & Nrm & Hdepth & Hpool & Hnm & Htm & Hsm & Hal & Hbl & Hna & Hnb).
  unfold BN_mod_mul. set (u := gx_used (st_ctx s)) in *. unfold live in Lr, La, Lb, Lm. fold u in Lr, La, Lb, Lm.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *. set (m := getbn rm s) in *.
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

  eapply hoare_bind with (R := fun _ s2 => keeps (S u) [t] s1 s2 /\ bn_canon (getbn t s2) /\ bn_neg (getbn t s2) = false /\
        bn_mag (getbn t s2) = bn_mag a * bn_mag b /\ (bn_top (getbn t s2) <= 254)%nat).
  { destruct (Nat.eqb_spec ra rb) as [Eab|Nab].
    - eapply hoare_mono; [apply BN_sqr_spec; unfold sqr_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 ra La); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact La|]. split; [exact Nt1|]. split; [apply Ntx; exact La|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|exact Hal].
      + intros [] s2 _ (K2 & C2 & M2 & N2 & T2). rewrite Eu1 in K2. rewrite (G1 ra La) in M2, T2. fold a in M2, T2.
        split; [exact K2|]. split; [exact C2|]. split; [exact N2|]. split; [rewrite M2; unfold b; rewrite <- Eab; reflexivity|lia].
    - eapply hoare_mono; [apply BN_mul_spec; unfold mul_pre; rewrite Eu1, Ef1, Ef0, length_app, (G1 ra La), (G1 rb Lb); cbn [length]|].
      + split; [exact Lt1|]. split; [apply Hl1; exact La|]. split; [apply Hl1; exact Lb|]. split; [exact Nt1|].
        split; [apply Ntx; exact La|]. split; [apply Ntx; exact Lb|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; assumption.
      + intros [] s2 _ (K2 & C2 & M2 & N2 & T2). rewrite Eu1 in K2. rewrite (G1 ra La), (G1 rb Lb) in M2, N2, T2. fold a b in M2, N2, T2.
        split; [exact K2|]. split; [exact C2|]. split; [rewrite N2, Hna, Hnb; reflexivity|]. split; [exact M2|lia]. }
  intros [] s2 Hs2 (K2 & C2 & N2 & M2 & T2).
  pose proof (inner_of_keeps u _ _ _ _ K2 ltac:(lia)) as I2.
  assert (G2 : forall x, (x < NFIX + u)%nat -> getbn x s2 = getbn x s).
  { intros x Hx. rewrite (inner_get_slot _ _ _ _ x I2 Hx) by (intros [E|[]]; rewrite Et in E; unfold RPool in E; lia). apply G1. exact Hx. }

  eapply hoare_bind.
  { apply (BN_nnmod_spec rr t rm). unfold nnmod_pre, live. rewrite (keeps_used _ _ _ _ K2), (keeps_frames _ _ _ _ K2), Eu1, Ef1, Ef0, length_app, (G2 rm Lm). cbn [length].
    fold m. split; [lia|]. split; [rewrite Et; unfold RPool; lia|]. split; [lia|]. split; [exact Nr1|]. split; [exact Nrm|].
    split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact Hnm|]. split; [exact Htm|].
    split; [unfold BG_DMAX; lia|exact Hsm]. }
  intros [] s3 Hs3 (K3 & P3). rewrite (keeps_used _ _ _ _ K2), Eu1 in K3. rewrite (G2 rm Lm) in P3. fold m in P3.
  pose proof (inner_of_keeps u _ _ _ _ K3 ltac:(lia)) as I3.
  assert (Ef3 : gx_frames (st_ctx s3) = gx_frames (st_ctx s) ++ [u]).
  { rewrite (keeps_frames _ _ _ _ K3), (keeps_frames _ _ _ _ K2), Ef1. exact Ef0. }
  eapply hoare_mono; [apply (BN_CTX_end_spec F s3 (gx_frames (st_ctx s)) u); exact Ef3|].
  intros [] s4 Hs4 (Eb4 & Sc4 & Eu4 & Ef4).
  pose proof (inner_bns_eq u s3 s4 Eb4 Sc4) as I4.
  split.
  - apply keeps_of_inner; [|exact Eu4|exact Ef4].
    eapply inner_weaken; [|eapply inner_trans; [eapply inner_trans; [eapply inner_trans; [exact I01|exact I2]|exact I3]|exact I4]].
    intros r Hin Hr. cbn [app] in Hin. destruct Hin as [E|[E|[]]]; [rewrite <- E, Et in Hr; unfold RPool in Hr; lia|left; exact E].
  - assert (Eg : getbn rr s4 = getbn rr s3) by (unfold getbn; rewrite Eb4; reflexivity). rewrite Eg.
    unfold bn_val in P3. rewrite N2, M2 in P3. exact P3.
Qed.

End ModSpec.
