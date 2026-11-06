(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim ScanInt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Txt.
  Variables (txt : list Z) (p : Z).
  Hypothesis Hp : 0 <= p < zlength txt.
  Hypothesis Hnul : znth txt p = 0.
  Hypothesis Hpre : forall i, 0 <= i < p -> znth txt i <> 0.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.

  #[using="BYT"] Lemma txt_rng : forall i, 0 <= i < zlength txt -> 0 <= znth txt i < 256.
  Proof. intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply znth_In. exact Hi. Qed.

  Definition U (k c : Z) (f : shfile) : Prop :=
    sh_buf f = txt /\ 0 <= sh_cnt0 f <= sh_rpos f /\ -1 <= c < 256 /\
    (sh_shlim_neg f = false -> sh_cnt0 f + k <= sh_rpos f) /\
    (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p /\ c = -1)) /\
    (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0 -> sh_rpos f <= p) /\ c <> -1).

  Definition pot (c : Z) (f : shfile) : Z :=
    if sh_stdio f then (if sh_shlim_neg f then 0 else p + 1 - sh_rpos f)
    else (if c =? 0 then 0 else p + 1 - sh_rpos f).

  #[using="Hp"] Lemma pot_range : forall k c f, U k c f -> 0 <= pot c f <= p + 1.
  Proof.
    intros k c f (B & C0 & Rc & K & ST & NS). unfold pot. destruct (sh_stdio f) eqn:S.
    - destruct (ST eq_refl) as (N1 & N2 & N3). destruct (sh_shlim_neg f); lia.
    - destruct (NS eq_refl) as (N1 & N2 & N3 & N4). destruct (Z.eqb_spec c 0); [lia|]. apply N3 in n. lia.
  Qed.

  Ltac U_open H := destruct H as (?B & ?C0 & ?Rc & ?K & ?ST & ?NS).

  #[using="Hp Hnul Hpre BYT"] Lemma U_getc : forall k c f, U k c f -> (sh_stdio f = true -> sh_shlim_neg f = false) -> (sh_stdio f = false -> c <> 0) ->
    let '(c1, f1) := sh_getc f in
    U (k + 1) c1 f1 /\ sh_stdio f1 = sh_stdio f /\ sh_cnt0 f1 = sh_cnt0 f /\ sh_n f1 = sh_n f /\ 0 <= pot c1 f1 < pot c f /\
    sh_rpos f <= sh_rpos f1 <= sh_rpos f + 1 /\ sh_rpos f <= p /\
    (c1 <> -1 -> sh_rpos f1 = sh_rpos f + 1 /\ c1 = znth txt (sh_rpos f) /\ sh_shlim_neg f1 = false /\
                 (c1 = 0 <-> (sh_stdio f = false /\ sh_rpos f = p))) /\
    (c1 = -1 -> sh_stdio f = true /\ sh_rpos f = p /\ sh_rpos f1 = p /\ sh_shlim_neg f1 = true).
  Proof.
    intros k c f HU CR1 CR2. U_open HU. unfold pot.
    unfold sh_getc. destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf.
    destruct st; cbn.
    - destruct (ST eq_refl) as (Hn & Hr & L1). subst n. specialize (CR1 eq_refl). subst sn. cbn.
      specialize (K eq_refl).
      destruct (Z.eqb_spec rpos p) as [E|NE]; cbn.
      + unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence.
      + pose proof (txt_rng rpos ltac:(lia)) as R. pose proof (Hpre rpos ltac:(lia)) as NZ.
        unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence.
        all: match goal with H : _ /\ _ |- _ => destruct H; congruence | _ => idtac end.
    - destruct (NS eq_refl) as (N1 & N2 & N3 & N4). subst sn. specialize (K eq_refl). specialize (CR2 eq_refl).
      assert (Hr : rpos <= p) by (apply N3; exact CR2).
      pose proof (txt_rng rpos ltac:(lia)) as R.
      assert (SZ : (znth txt rpos =? 0) = (rpos =? p)).
      { destruct (Z.eqb_spec rpos p) as [E|NE].
        - subst rpos. rewrite Hnul. reflexivity.
        - pose proof (Hpre rpos ltac:(lia)). apply Z.eqb_neq. lia. }
      rewrite SZ. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact CR2).
      assert (G1 : znth txt rpos <> 0 -> rpos + 1 <= p).
      { intros Hz. destruct (Z.eq_dec rpos p) as [E|NE]; [subst rpos; exfalso; exact (Hz Hnul) | lia]. }
      assert (G2 : 0 <= (if rpos =? p then 0 else p + 1 - (rpos + 1)) < p + 1 - rpos) by (destruct (Z.eqb_spec rpos p); lia).
      assert (G3 : znth txt rpos = 0 <-> false = false /\ rpos = p).
      { split. - intros E. split; [reflexivity|]. destruct (Z.eq_dec rpos p); [lia|]. exfalso. exact (Hpre rpos ltac:(lia) E). - intros [_ ->]. exact Hnul. }
      unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence; try tauto.
  Qed.

  #[using="Type"] Lemma U_unget : forall k c f, U k c f -> 1 <= k -> U (k - 1) c (sh_unget f) /\ sh_stdio (sh_unget f) = sh_stdio f /\
    sh_cnt0 (sh_unget f) = sh_cnt0 f /\ sh_n (sh_unget f) = sh_n f /\ sh_shlim_neg (sh_unget f) = sh_shlim_neg f /\
    sh_cnt0 f <= sh_rpos (sh_unget f) <= p /\ sh_rpos (sh_unget f) <= sh_rpos f /\
    (sh_shlim_neg f = false -> sh_rpos (sh_unget f) = sh_rpos f - 1).
  Proof.
    intros k c f HU Hk. U_open HU. unfold sh_unget. destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf.
    destruct sn; cbn.
    - destruct st; [|destruct (NS eq_refl); congruence]. destruct (ST eq_refl) as (Hn & Hr & L1). destruct (L1 eq_refl) as [E1 E2].
      unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence. all: try (apply ST; reflexivity).
    - specialize (K eq_refl). destruct st.
      + destruct (ST eq_refl) as (Hn & Hr & L1).
        unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence.
      + destruct (NS eq_refl) as (N1 & N2 & N3 & N4).
        unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence.
  Qed.

  #[using="Type"] Lemma U_lim0 : forall k c f, U k c f -> U 0 c (sh_lim0 f) /\ sh_stdio (sh_lim0 f) = sh_stdio f /\
    sh_cnt0 (sh_lim0 f) = sh_rpos f /\ sh_rpos (sh_lim0 f) = sh_rpos f /\ sh_n (sh_lim0 f) = sh_n f /\ sh_shlim_neg (sh_lim0 f) = false.
  Proof.
    intros k c f HU. U_open HU. unfold sh_lim0. destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf.
    destruct st.
    - destruct (ST eq_refl) as (Hn & Hr & L1). unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence.
    - destruct (NS eq_refl) as (N1 & N2 & N3 & N4). unfold U; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence. all: apply N3; assumption.
  Qed.

  #[using="Type"] Lemma isspace_rng : forall c, -1 <= c < 256 -> m_isspace c = true -> c = 32 \/ 9 <= c <= 13.
  Proof. intros c Hc H. apply (proj1 (m_isspace_iff c ltac:(lia))). exact H. Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma ws_loop_U : forall n k c f, U k c f -> (sh_stdio f = true -> sh_shlim_neg f = false) -> (sh_stdio f = false -> c <> 0) ->
    pot c f < Z.of_nat n ->
    exists c1 f1 k1, is_ws_loop n f = Some (c1, f1) /\ U k1 c1 f1 /\ k + 1 <= k1 /\ m_isspace c1 = false /\
      sh_stdio f1 = sh_stdio f /\ sh_cnt0 f1 = sh_cnt0 f /\ sh_n f1 = sh_n f /\ sh_rpos f + 1 <= sh_rpos f1 + (if sh_shlim_neg f1 then 1 else 0).
  Proof.
    induction n as [|n IH]; intros k c f HU CR1 CR2 HP.
    { exfalso. pose proof (pot_range k c f HU). cbn in HP. lia. }
    cbn [is_ws_loop]. pose proof (U_getc k c f HU CR1 CR2) as G. destruct (sh_getc f) as [c1 f1].
    destruct G as (U1 & S1 & C1 & N1 & P1 & R1 & Rp & NE1 & E1).
    destruct (m_isspace c1) eqn:SP.
    - assert (Rc1 : -1 <= c1 < 256) by (destruct U1 as (_ & _ & R & _); exact R).
      pose proof (isspace_rng c1 Rc1 SP) as SR.
      destruct (NE1 ltac:(lia)) as (Q1 & Q3 & Q4 & Q5).
      destruct (IH (k + 1) c1 f1 U1 ltac:(intros; exact Q4) ltac:(intros; lia) ltac:(rewrite Nat2Z.inj_succ in HP; lia))
        as (c2 & f2 & k2 & HL & U2 & K2 & SP2 & S2 & C2 & N2 & R2).
      exists c2, f2, k2. rewrite HL. split; [reflexivity|]. split; [exact U2|]. repeat split; try assumption; try lia; try congruence.
    - exists c1, f1, (k + 1). split; [reflexivity|]. split; [exact U1|]. repeat split; try assumption; try lia; try reflexivity.
      destruct (Z.eq_dec c1 (-1)) as [E|NE].
      + destruct (E1 E) as (_ & _ & X3 & X4). rewrite X4. lia.
      + destruct (NE1 NE) as (Q1 & _ & Q4 & _). rewrite Q4. lia.
  Qed.

  #[using="Type"] Lemma digval_stop : forall c, c = 0 \/ c = -1 -> forall base, base <= 36 -> (digval c <? base) = false.
  Proof. intros c Hc base Hb. rewrite (digval_nondigit_stop c Hc). apply Z.ltb_ge. lia. Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma dig_loop_U : forall n base k c f, U k c f -> 2 <= base <= 36 -> pot c f < Z.of_nat n ->
    exists c1 f1 k1, is_dig_loop n base c f = Some (c1, f1) /\ U k1 c1 f1 /\ k <= k1 /\ base <= digval c1 /\
      sh_stdio f1 = sh_stdio f /\ sh_cnt0 f1 = sh_cnt0 f /\ sh_n f1 = sh_n f /\
      ((c1 = c /\ f1 = f /\ k1 = k) \/ (k + 1 <= k1 /\ sh_rpos f + 1 <= sh_rpos f1 + (if sh_shlim_neg f1 then 1 else 0))).
  Proof.
    induction n as [|n IH]; intros base k c f HU Hb HP.
    { exfalso. pose proof (pot_range k c f HU). cbn in HP. lia. }
    cbn [is_dig_loop]. destruct (Z.ltb_spec0 (digval c) base) as [LT|GE].
    - assert (Hc : c <> 0 /\ c <> -1).
      { split; intros E; rewrite (digval_nondigit_stop c ltac:(lia)) in LT; lia. }
      destruct Hc as [Hc0 Hc1].
      assert (CR1 : sh_stdio f = true -> sh_shlim_neg f = false).
      { intros S. destruct HU as (_ & _ & _ & _ & ST & _). destruct (ST S) as (_ & _ & L1). destruct (sh_shlim_neg f); [|reflexivity]. destruct (L1 eq_refl). congruence. }
      pose proof (U_getc k c f HU CR1 ltac:(intros; exact Hc0)) as G. destruct (sh_getc f) as [c1 f1].
      destruct G as (U1 & S1 & C1 & N1 & P1 & R1 & Rp & NE1 & E1).
      destruct (IH base (k + 1) c1 f1 U1 Hb ltac:(rewrite Nat2Z.inj_succ in HP; lia)) as (c2 & f2 & k2 & HL & U2 & K2 & D2 & S2 & C2 & N2 & ALT).
      exists c2, f2, k2. rewrite HL. split; [reflexivity|]. split; [exact U2|]. repeat split; try assumption; try lia; try congruence.
      right. split; [lia|].
      destruct ALT as [(-> & -> & ->) | [K3 R3]].
      + destruct (Z.eq_dec c1 (-1)) as [E|NE].
        * destruct (E1 E) as (_ & _ & X3 & X4). rewrite X4. lia.
        * destruct (NE1 NE) as (Q1 & _ & Q4 & _). rewrite Q4. lia.
      + lia.
    - exists c, f, k. split; [reflexivity|]. split; [exact HU|]. repeat split; try assumption; try lia. left. repeat split; reflexivity.
  Qed.

  Definition Rpost (f fR : shfile) : Prop :=
    sh_buf fR = txt /\ sh_stdio fR = sh_stdio f /\ sh_n fR = sh_n f /\
    0 <= sh_cnt0 fR <= sh_rpos fR /\ sh_rpos fR <= p /\ (sh_cnt0 fR = sh_cnt0 f \/ sh_cnt0 fR = sh_rpos fR) /\
    (exists k' c', U k' c' fR).

  #[using="Type"] Lemma Rpost_intro : forall ff fR k' c', U k' c' fR -> sh_stdio fR = sh_stdio ff -> sh_n fR = sh_n ff -> sh_rpos fR <= p ->
    (sh_cnt0 fR = sh_cnt0 ff \/ sh_cnt0 fR = sh_rpos fR) -> Rpost ff fR.
  Proof.
    intros ff fR k' c' HU S N R C. pose proof HU as HU'. destruct HU' as (B & C0 & _).
    unfold Rpost. repeat split; try assumption; try lia. exists k', c'. exact HU.
  Qed.

  #[using="Hp"] Lemma len_pot : forall k c f, U k c f -> pot c f < Z.of_nat (S (length txt)).
  Proof. intros k c f HU. pose proof (pot_range k c f HU). unfold zlength in Hp. rewrite Nat2Z.inj_succ. lia. Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma digits_U : forall base k c f, U k c f -> 1 <= k -> 2 <= base <= 36 ->
    exists fR, is_digits (S (length txt)) base c f = Some fR /\ Rpost f fR.
  Proof.
    intros base k c f HU Hk Hb. unfold is_digits.
    destruct (dig_loop_U (S (length txt)) base k c f HU Hb (len_pot k c f HU)) as (c1 & f1 & k1 & HL & U1 & K1 & D1 & S1 & C1 & N1 & ALT).
    rewrite HL. eexists. split; [reflexivity|].
    assert (Hk1 : 1 <= k1) by lia.
    destruct (U_unget k1 c1 f1 U1 Hk1) as (Uu & Su & Cu & Nu & SNu & Ru & Ru2 & Ru3).
    pose proof Uu as Uu'. destruct Uu' as (X1 & X2 & _). pose proof HU as HU'. destruct HU' as (Y1 & Y2 & _).
    unfold Rpost. rewrite Su, Cu, Nu, S1, C1, N1. rewrite Cu, C1 in X2.
    split; [exact X1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
    exists (k1 - 1), c1. exact Uu.
  Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma intscan_U : forall base pok k c f, U k c f -> (0 <= k) -> (base = 10 \/ base = 16) ->
    (sh_stdio f = true -> sh_shlim_neg f = false) -> (sh_stdio f = false -> c <> 0) ->
    exists fR, intscan (S (length txt)) base pok f = Some fR /\ Rpost f fR.
  Proof.
    intros base pok k c f HU Hk0 Hb CR1 CR2. unfold intscan.
    destruct (ws_loop_U (S (length txt)) k c f HU CR1 CR2 (len_pot k c f HU)) as (c1 & f1 & k1 & HL & U1 & K1 & SP1 & S1 & C1 & N1 & R1).
    rewrite HL.

    assert (SG : exists c2 f2 k2, (if (c1 =? 43) || (c1 =? 45) then sh_getc f1 else (c1, f1)) = (c2, f2) /\ U k2 c2 f2 /\ 1 <= k2 /\
                 sh_stdio f2 = sh_stdio f /\ sh_cnt0 f2 = sh_cnt0 f /\ sh_n f2 = sh_n f).
    { destruct ((c1 =? 43) || (c1 =? 45)) eqn:E.
      - assert (H4345 : c1 = 43 \/ c1 = 45) by (apply Bool.orb_true_iff in E; destruct E as [E|E]; apply Z.eqb_eq in E; lia).
        assert (CR1' : sh_stdio f1 = true -> sh_shlim_neg f1 = false).
        { intros S. destruct U1 as (_ & _ & _ & _ & ST & _). destruct (ST S) as (_ & _ & L1). destruct (sh_shlim_neg f1); [|reflexivity]. destruct (L1 eq_refl). lia. }
        pose proof (U_getc k1 c1 f1 U1 CR1' ltac:(intros; lia)) as G. destruct (sh_getc f1) as [c2 f2].
        destruct G as (U2 & S2 & C2 & N2 & _). exists c2, f2, (k1 + 1). split; [reflexivity|]. split; [exact U2|]. repeat split; [lia | congruence | congruence | congruence].
      - exists c1, f1, k1. split; [reflexivity|]. split; [exact U1|]. repeat split; [lia | congruence | congruence | congruence]. }
    destruct SG as (c2 & f2 & k2 & -> & U2 & K2 & S2 & C2 & N2).
    assert (CR1' : forall kk cc ff, U kk cc ff -> cc <> -1 -> sh_stdio ff = true -> sh_shlim_neg ff = false).
    { intros kk cc ff UU NE S. destruct UU as (_ & _ & _ & _ & ST & _). destruct (ST S) as (_ & _ & L1). destruct (sh_shlim_neg ff); [|reflexivity]. destruct (L1 eq_refl). lia. }
    assert (RP : forall ff fR, Rpost ff fR -> sh_stdio ff = sh_stdio f -> sh_cnt0 ff = sh_cnt0 f -> sh_n ff = sh_n f -> Rpost f fR).
    { intros ff fR (A1 & A2 & A3 & A4 & A5 & A6 & A7) E1 E2 E3. unfold Rpost. rewrite <- E1, <- E2, <- E3. repeat split; try assumption; lia. }
    destruct ((base =? 16) && (c2 =? 48)) eqn:E16.
    - apply andb_prop in E16. destruct E16 as [Eb Ec]. apply Z.eqb_eq in Eb. apply Z.eqb_eq in Ec.
      pose proof (U_getc k2 c2 f2 U2 (CR1' _ _ _ U2 ltac:(lia)) ltac:(intros; lia)) as G. destruct (sh_getc f2) as [c3 f3].
      destruct G as (U3 & S3 & C3 & N3 & _).
      destruct (Z.lor c3 32 =? 120) eqn:EX.
      + apply Z.eqb_eq in EX. assert (c3 <> 0 /\ c3 <> -1) as [X0 X1] by (split; intros E; rewrite E in EX; discriminate EX).
        pose proof (U_getc (k2 + 1) c3 f3 U3 (CR1' _ _ _ U3 X1) ltac:(intros; exact X0)) as G. destruct (sh_getc f3) as [c4 f4].
        destruct G as (U4 & S4 & C4 & N4 & _).
        destruct (16 <=? digval c4).
        * eexists. split; [reflexivity|].
          destruct (U_unget (k2 + 1 + 1) c4 f4 U4 ltac:(lia)) as (Uu & Su & Cu & Nu & SNu & Ru & Ru2 & Ru3).
          unfold nz. destruct (Z.eqb_spec pok 0); cbn [negb].
          -- destruct (U_lim0 _ _ _ Uu) as (Ul & Sl & Cl & Rl & Nl & SNl).
             eapply Rpost_intro; [exact Ul | congruence | congruence | lia | right; congruence].
          -- destruct (U_unget _ c4 _ Uu ltac:(lia)) as (Uuu & Suu & Cuu & Nuu & SNuu & Ruu & Ruu2 & Ruu3).
             eapply Rpost_intro; [exact Uuu | congruence | congruence | lia | left; congruence].
        * destruct (digits_U 16 (k2 + 1 + 1) c4 f4 U4 ltac:(lia) ltac:(lia)) as (fR & HD & RR). rewrite HD. eexists. split; [reflexivity|].
          apply (RP f4 fR RR); congruence.
      + destruct (digits_U 16 (k2 + 1) c3 f3 U3 ltac:(lia) ltac:(lia)) as (fR & HD & RR). rewrite HD. eexists. split; [reflexivity|].
        apply (RP f3 fR RR); congruence.
    - destruct (base <=? digval c2).
      + eexists. split; [reflexivity|].
        destruct (U_unget k2 c2 f2 U2 ltac:(lia)) as (Uu & Su & Cu & Nu & SNu & Ru & Ru2 & Ru3).
        destruct (U_lim0 _ _ _ Uu) as (Ul & Sl & Cl & Rl & Nl & SNl).
        eapply Rpost_intro; [exact Ul | congruence | congruence | lia | right; congruence].
      + destruct (digits_U base k2 c2 f2 U2 ltac:(lia) ltac:(lia)) as (fR & HD & RR). rewrite HD. eexists. split; [reflexivity|].
        apply (RP f2 fR RR); congruence.
  Qed.
End Txt.

Fixpoint first_nul (l : list Z) : nat :=
  match l with [] => 0%nat | c :: l' => if c =? 0 then 0%nat else S (first_nul l') end.
Lemma first_nul_spec : forall l, In 0 l ->
  (first_nul l < length l)%nat /\ znth l (Z.of_nat (first_nul l)) = 0 /\ forall i, 0 <= i < Z.of_nat (first_nul l) -> znth l i <> 0.
Proof.
  induction l as [|c l IH]; intros Hin; [destruct Hin|]. cbn [first_nul].
  destruct (Z.eqb_spec c 0) as [E|NE].
  - subst c. cbn. split; [lia|]. split; [reflexivity|]. intros; lia.
  - destruct Hin as [E|Hin]; [lia|]. destruct (IH Hin) as (L & Z0 & NZ).
    split; [cbn; lia|]. split.
    + unfold znth in *. destruct (Z.ltb_spec0 (Z.of_nat (first_nul l)) 0); [lia|].
      destruct (Z.ltb_spec0 (Z.of_nat (S (first_nul l))) 0); [lia|].
      rewrite Nat2Z.id in *. cbn. exact Z0.
    + intros i Hi. unfold znth in *. destruct (Z.ltb_spec0 i 0); [lia|].
      destruct (Z.to_nat i) as [|j] eqn:Ej; cbn; [exact NE|].
      specialize (NZ (Z.of_nat j) ltac:(lia)). destruct (Z.ltb_spec0 (Z.of_nat j) 0); [lia|]. rewrite Nat2Z.id in NZ. exact NZ.
Qed.
Lemma first_nul_app : forall pre post, Forall (fun c => 0 < c < 256) pre -> first_nul (pre ++ 0 :: post) = length pre.
Proof.
  induction pre as [|c pre IH]; intros post HF; cbn; [reflexivity|].
  inversion HF; subst. destruct (Z.eqb_spec c 0); [lia|]. rewrite IH by assumption. reflexivity.
Qed.

Lemma intscan_strtol : forall txt base, In 0 txt -> Forall (fun c => 0 <= c < 256) txt -> (base = 10 \/ base = 16) ->
  exists fR, intscan (S (length txt)) base 1 (stf0 txt) = Some fR /\ sh_buf fR = txt /\ sh_stdio fR = false /\
    0 <= sh_cnt0 fR <= sh_rpos fR /\ sh_rpos fR <= Z.of_nat (first_nul txt).
Proof.
  intros txt base Hin BYT Hb.
  destruct (first_nul_spec txt Hin) as (L & Z0 & NZ).
  assert (HU : U txt (Z.of_nat (first_nul txt)) 0 1 (stf0 txt)).
  { unfold U, stf0; cbn. repeat split; try lia; try discriminate; intros; try lia; try congruence. }
  destruct (intscan_U txt (Z.of_nat (first_nul txt)) ltac:(unfold zlength; lia) Z0 NZ BYT base 1 0 1 (stf0 txt) HU ltac:(lia) Hb
              ltac:(intros X; discriminate X) ltac:(intros; lia)) as (fR & HI & (B1 & B2 & B3 & B4 & B5 & B6 & B7)).
  exists fR. cbn in B2, B3. repeat split; try assumption; lia.
Qed.
