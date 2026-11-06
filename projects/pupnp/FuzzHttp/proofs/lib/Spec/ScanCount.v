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
  Variables (txt pre post : list Z).
  Hypothesis Htxt : txt = pre ++ 0 :: post.
  Hypothesis NZ : Forall (fun c => 0 < c < 256) pre.
  Let p : Z := zlength pre.

  Definition rem (rp : Z) : list Z := skipn (Z.to_nat rp) pre.

  #[using="Type"] Lemma rem_p : forall rp, p <= rp -> rem rp = [].
  Proof. intros rp H. unfold rem, p, zlength in *. apply skipn_all2. lia. Qed.

  #[using="Type"] Lemma skipn_nth_cons : forall (l : list Z) n d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
  Proof.
    clear. intros l. induction l as [|a l IH]; intros n d H; cbn in H; [lia|].
    destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
  Qed.

  #[using="post Htxt"] Lemma rem_cons : forall rp, 0 <= rp < p -> rem rp = znth txt rp :: rem (rp + 1).
  Proof.
    intros rp H. unfold rem, p, zlength in *. rewrite Htxt. rewrite znth_app_l by (unfold zlength; lia).
    unfold znth. destruct (Z.ltb_spec0 rp 0); [lia|].
    replace (Z.to_nat (rp + 1)) with (S (Z.to_nat rp)) by lia. apply skipn_nth_cons. lia.
  Qed.

  #[using="post Htxt NZ"] Lemma pre_char : forall rp, 0 <= rp < p -> 0 < znth txt rp < 256.
  Proof.
    intros rp H. rewrite Htxt. rewrite znth_app_l by (unfold p in H; lia).
    apply (proj1 (Forall_forall _ _) NZ). apply znth_In. unfold p in H; lia.
  Qed.

  Definition SF (f : shfile) : Prop :=
    sh_buf f = txt /\ sh_stdio f = true /\ sh_n f = p /\ 0 <= sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p).

  #[using="pre p"] Lemma isspace_eq : forall c, (0 <= c < 256 \/ c = -1) -> m_isspace c = is_space c.
  Proof.
    intros c Hc. destruct (m_isspace c) eqn:E.
    - apply (proj1 (m_isspace_iff c ltac:(lia))) in E. unfold is_space. symmetry. destruct E as [->|E]; [reflexivity|].
      apply Bool.orb_true_iff. right. apply andb_true_intro; split; apply Z.leb_le; lia.
    - symmetry. unfold is_space. destruct (Z.eqb_spec c 32); [subst; discriminate E|]. cbn [orb].
      destruct (Z.leb_spec0 9 c); destruct (Z.leb_spec0 c 13); cbn; try reflexivity.
      exfalso. assert (m_isspace c = true) by (apply (proj2 (m_isspace_iff c ltac:(lia))); lia). congruence.
  Qed.

  #[using="pre p"] Lemma isdigit_eq : forall c, (digval c <? 10) = is_digit c.
  Proof.
    intros c. unfold is_digit. destruct (Z.ltb_spec0 (digval c) 10) as [L|L].
    - apply (proj1 (digval_lt10 c)) in L. symmetry. apply andb_true_intro; split; apply Z.leb_le; lia.
    - symmetry. destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn; try reflexivity.
      exfalso. apply L. apply (proj2 (digval_lt10 c)). lia.
  Qed.

  #[using="post Htxt NZ"] Lemma getc_SF : forall f, SF f ->
    let '(c, f1) := sh_getc f in
    SF f1 /\ sh_cnt0 f1 = sh_cnt0 f /\
    ((sh_rpos f < p /\ c = znth txt (sh_rpos f) /\ 0 < c < 256 /\ sh_rpos f1 = sh_rpos f + 1 /\ sh_shlim_neg f1 = false /\ sh_shlim_neg f = false)
     \/ (sh_rpos f = p /\ c = -1 /\ sh_rpos f1 = p /\ sh_shlim_neg f1 = true)).
  Proof.
    intros f (B & ST & N & R & L). destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf st n.
    unfold sh_getc; cbn. destruct (Z.eqb_spec rpos p) as [E|E]; cbn.
    - split; [unfold SF; cbn; repeat split; try lia; reflexivity|]. split; [reflexivity|]. right. repeat split; lia.
    - pose proof (pre_char rpos ltac:(lia)) as PC.
      assert (sn = false) as -> by (destruct sn; [|reflexivity]; exfalso; specialize (L eq_refl); lia).
      split; [unfold SF; cbn; repeat split; try lia; intros X; discriminate X|]. split; [reflexivity|]. left. repeat split; lia.
  Qed.

  #[using="Type"] Lemma unget_SF : forall f, SF f -> (sh_shlim_neg f = false -> 1 <= sh_rpos f) ->
    SF (sh_unget f) /\ sh_cnt0 (sh_unget f) = sh_cnt0 f /\ sh_shlim_neg (sh_unget f) = sh_shlim_neg f /\
    sh_rpos (sh_unget f) = (if sh_shlim_neg f then sh_rpos f else sh_rpos f - 1).
  Proof.
    intros f (B & ST & N & R & L) H1. destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf st n.
    unfold sh_unget; cbn. destruct sn; cbn.
    - split; [unfold SF; cbn; repeat split; try lia; exact L|]. repeat split; reflexivity.
    - specialize (H1 eq_refl). split; [unfold SF; cbn; repeat split; try lia; intros X; discriminate X|]. repeat split; reflexivity.
  Qed.

  #[using="Type"] Lemma lim0_SF : forall f, SF f -> SF (sh_lim0 f) /\ sh_rpos (sh_lim0 f) = sh_rpos f /\ sh_cnt0 (sh_lim0 f) = sh_rpos f /\ sh_shlim_neg (sh_lim0 f) = false.
  Proof.
    intros f (B & ST & N & R & L). destruct f as [buf rpos cnt0 n st sn]; cbn in *. subst buf st n.
    unfold sh_lim0; cbn. split; [unfold SF; cbn; repeat split; try lia; intros X; discriminate X|]. repeat split; reflexivity.
  Qed.

  #[using="Type"] Lemma rem_length : forall rp, 0 <= rp <= p -> zlength (rem rp) = p - rp.
  Proof. intros rp H. unfold rem, zlength, p, zlength in *. rewrite length_skipn. lia. Qed.

  #[using="post Htxt NZ"] Lemma ws_loop_SF : forall n f, SF f -> sh_shlim_neg f = false -> p - sh_rpos f < Z.of_nat n ->
    exists c f1 rp', is_ws_loop n f = Some (c, f1) /\ SF f1 /\ sh_cnt0 f1 = sh_cnt0 f /\ sh_rpos f <= rp' <= p /\
      rem rp' = drop_while is_space (rem (sh_rpos f)) /\
      ((rem rp' = [] /\ c = -1 /\ sh_rpos f1 = p /\ sh_shlim_neg f1 = true /\ rp' = p)
       \/ (exists l, rem rp' = c :: l /\ is_space c = false /\ 0 < c < 256 /\ sh_rpos f1 = rp' + 1 /\ sh_shlim_neg f1 = false)).
  Proof.
    induction n as [|n IH]; intros f HS NL HP; [destruct HS as (_ & _ & _ & R & _); cbn in HP; lia|].
    cbn [is_ws_loop]. pose proof (getc_SF f HS) as G. destruct (sh_getc f) as [c f1]. destruct G as (S1 & C1 & [(LT & Ec & Rc & R1 & NL1 & _) | (EQ & Ec & R1 & L1)]).
    - rewrite (isspace_eq c) by lia. pose proof (rem_cons (sh_rpos f) ltac:(destruct HS as (_ & _ & _ & R & _); lia)) as RC. rewrite <- Ec in RC.
      destruct (is_space c) eqn:SP.
      + destruct (IH f1 S1 NL1 ltac:(lia)) as (c2 & f2 & rp2 & HL & S2 & C2 & R2 & RM & ALT).
        exists c2, f2, rp2. split; [exact HL|]. split; [exact S2|]. split; [congruence|]. split; [lia|].
        split; [rewrite RC; cbn [drop_while]; rewrite SP; rewrite <- R1; exact RM|]. exact ALT.
      + exists c, f1, (sh_rpos f). split; [reflexivity|]. split; [exact S1|]. split; [exact C1|]. split; [destruct HS as (_ & _ & _ & R & _); lia|].
        split; [rewrite RC; cbn [drop_while]; rewrite SP; reflexivity|].
        right. exists (rem (sh_rpos f + 1)). repeat split; try assumption; lia.
    - rewrite Ec. cbn. exists (-1), f1, p. split; [reflexivity|]. split; [exact S1|]. split; [exact C1|]. split; [destruct HS as (_ & _ & _ & R & _); lia|].
      rewrite EQ, (rem_p p) by lia. cbn. split; [reflexivity|]. left. repeat split; try assumption; reflexivity.
  Qed.

  #[using="post Htxt"] Lemma p_lt : p < Z.of_nat (length txt).
  Proof. unfold p, zlength. rewrite Htxt, length_app. cbn. lia. Qed.

  #[using="post Htxt NZ"] Lemma vfW_SF : forall f, SF f -> exists f2, vf_W (S (length txt)) f = VOk f2 /\ SF f2 /\ rem (sh_rpos f2) = drop_while is_space (rem (sh_rpos f)).
  Proof.
    intros f HS. unfold vf_W. destruct (lim0_SF f HS) as (Sl & Rl & Cl & Nl).
    pose proof p_lt as PL.
    destruct (ws_loop_SF (S (length txt)) (sh_lim0 f) Sl Nl ltac:(destruct Sl as (_ & _ & _ & R & _); lia)) as (c & f1 & rp' & HL & S1 & C1 & R1 & RM & ALT).
    rewrite HL. eexists. split; [reflexivity|].
    destruct ALT as [(E0 & Ec & Rf & Lf & Ep) | (l & E0 & SP & Rc & Rf & Lf)].
    - destruct (unget_SF f1 S1 ltac:(intros X; congruence)) as (Su & Cu & Lu & Ru). rewrite Lf in Ru.
      split; [exact Su|]. rewrite Ru, Rf, <- Ep, <- Rl. exact RM.
    - destruct (unget_SF f1 S1 ltac:(intros _; destruct Sl as (_ & _ & _ & R & _); lia)) as (Su & Cu & Lu & Ru). rewrite Lf in Ru.
      split; [exact Su|]. rewrite Ru, Rf, <- Rl. replace (rp' + 1 - 1) with rp' by lia. exact RM.
  Qed.

  Definition CUR (K : Z) (c : Z) (g : shfile) (i : list Z) : Prop :=
    SF g /\ sh_cnt0 g = K /\
    ((1 <= sh_rpos g /\ sh_shlim_neg g = false /\ rem (sh_rpos g - 1) = i /\ (exists l, i = c :: l) /\ 0 < c < 256)
     \/ (i = [] /\ c = -1 /\ sh_shlim_neg g = true /\ sh_rpos g = p)).

  #[using="post Htxt NZ"] Lemma read_CUR : forall g, SF g -> sh_shlim_neg g = false ->
    let '(c1, g1) := sh_getc g in CUR (sh_cnt0 g) c1 g1 (rem (sh_rpos g)).
  Proof.
    intros g HS NL. pose proof (getc_SF g HS) as G. destruct (sh_getc g) as [c1 g1].
    destruct G as (S1 & C1 & [(LT & Ec & Rc & R1 & NL1 & _) | (EQ & Ec & R1 & L1)]).
    - split; [exact S1|]. split; [exact C1|]. left. rewrite R1. replace (sh_rpos g + 1 - 1) with (sh_rpos g) by lia.
      pose proof (rem_cons (sh_rpos g) ltac:(destruct HS as (_ & _ & _ & R & _); lia)) as RC.
      split; [destruct HS as (_ & _ & _ & R & _); lia|]. split; [exact NL1|]. split; [reflexivity|]. split; [exists (rem (sh_rpos g + 1)); congruence | lia].
    - split; [exact S1|]. split; [exact C1|]. right. rewrite EQ, rem_p by lia. repeat split; try assumption; reflexivity.
  Qed.

  #[using="post Htxt NZ"] Lemma dig_loop_CUR : forall n K c g i, CUR K c g i -> Z.of_nat (length i) < Z.of_nat n ->
    exists c' g', is_dig_loop n 10 c g = Some (c', g') /\ CUR K c' g' (skipn (take_while_len is_digit i) i).
  Proof.
    induction n as [|n IH]; intros K c g i HC HL; [cbn in HL; lia|].
    cbn [is_dig_loop]. rewrite isdigit_eq.
    pose proof HC as HC'. destruct HC' as (Sg & Cg & [(R1 & NL & RM & [l ->] & Rc) | (-> & -> & L & Rp)]).
    - cbn [take_while_len]. destruct (is_digit c) eqn:DG.
      + pose proof (read_CUR g Sg NL) as RC. destruct (sh_getc g) as [c1 g1].
        assert (El : rem (sh_rpos g) = l).
        { pose proof (rem_length (sh_rpos g - 1) ltac:(destruct Sg as (_ & _ & _ & R & _); lia)) as LL. rewrite RM in LL. unfold zlength in LL. cbn in LL.
          rewrite (rem_cons (sh_rpos g - 1)) in RM by (destruct Sg as (_ & _ & _ & R & _); lia). replace (sh_rpos g - 1 + 1) with (sh_rpos g) in RM by lia. congruence. }
        rewrite El, Cg in RC. cbn [skipn]. apply (IH K c1 g1 l RC). cbn in HL. lia.
      + exists c, g. split; [reflexivity|]. cbn [skipn]. exact HC.
    - change (is_digit (-1)) with false. cbn. exists (-1), g. split; [reflexivity | exact HC].
  Qed.

  #[using="Type"] Lemma drop_while_hd : forall (f : Z -> bool) l c l', drop_while f l = c :: l' -> f c = false.
  Proof. clear. intros f l. induction l as [|a l IH]; intros c l' H; cbn in H; [discriminate H|]. destruct (f a) eqn:E; [apply (IH _ _ H) | congruence]. Qed.

  #[using="Type"] Lemma take_while_len_le : forall (f : Z -> bool) l, (take_while_len f l <= length l)%nat.
  Proof. clear. intros f l. induction l as [|a l IH]; cbn; [lia|]. destruct (f a); lia. Qed.

  #[using="post Htxt NZ"] Lemma intscan_SF : forall g c l, SF g -> sh_shlim_neg g = false -> sh_cnt0 g = sh_rpos g -> rem (sh_rpos g) = c :: l -> is_space c = false ->
    let i2 := (if (c =? 43) || (c =? 45) then l else c :: l) in
    let nd := take_while_len is_digit i2 in
    exists f6, intscan (S (length txt)) 10 0 g = Some f6 /\ SF f6 /\
      (nd = 0%nat -> sh_cnt f6 = 0) /\ (nd <> 0%nat -> sh_cnt f6 <> 0 /\ rem (sh_rpos f6) = skipn nd i2).
  Proof.
    intros g c l Sg NL CK RM SP. cbv zeta. unfold intscan. cbn [is_ws_loop].
    pose proof Sg as Sg'. destruct Sg' as (Bg & STg & Ng & Rg & Lg).
    pose proof (read_CUR g Sg NL) as RC. pose proof (getc_SF g Sg) as G. destruct (sh_getc g) as [c1 g1].
    pose proof (rem_length (sh_rpos g) ltac:(destruct Sg as (_ & _ & _ & R & _); lia)) as L0.
    destruct G as (S1 & C1 & [(LT & Ec & Rc & R1 & NL1 & _) | (EQ & Ec & R1 & L1)]);
      [| exfalso; rewrite EQ, rem_p in RM by lia; discriminate RM].
    assert (c1 = c) as ->. { rewrite (rem_cons (sh_rpos g)) in RM by lia. congruence. }
    rewrite RM in RC. rewrite isspace_eq by lia. rewrite SP.

    assert (SG : exists c2 g2, (if (c =? 43) || (c =? 45) then sh_getc g1 else (c, g1)) = (c2, g2) /\
                 CUR (sh_rpos g) c2 g2 (if (c =? 43) || (c =? 45) then l else c :: l)).
    { destruct ((c =? 43) || (c =? 45)).
      - pose proof (read_CUR g1 S1 NL1) as RC1. destruct (sh_getc g1) as [c2 g2]. exists c2, g2. split; [reflexivity|].
        rewrite C1, CK, R1 in RC1. replace l with (rem (sh_rpos g + 1)); [exact RC1|].
        rewrite (rem_cons (sh_rpos g)) in RM by lia. congruence.
      - exists c, g1. split; [reflexivity|]. rewrite CK in RC. exact RC. }
    destruct SG as (c2 & g2 & -> & CU).
    set (i2 := if (c =? 43) || (c =? 45) then l else c :: l) in *.
    assert (Li2 : (length i2 <= S (length l))%nat) by (subst i2; destruct ((c =? 43) || (c =? 45)); cbn; lia).
    change ((10 =? 16) && (c2 =? 48)) with false. cbn [andb].
    replace (10 <=? digval c2) with (negb (is_digit c2)) by (rewrite <- isdigit_eq; destruct (Z.ltb_spec0 (digval c2) 10); destruct (Z.leb_spec0 10 (digval c2)); cbn; try reflexivity; lia).
    pose proof CU as CU'. destruct CU' as (S2 & C2 & [(R2 & NL2 & RM2 & [l2 El2] & Rc2) | (Ei2 & -> & L2 & Rp2)]).
    - rewrite El2. cbn [take_while_len]. destruct (is_digit c2) eqn:DG; cbn [negb].
      +
        unfold is_digits. pose proof p_lt as PL. rewrite RM in L0. unfold zlength in L0. cbn [length] in L0.
        destruct (dig_loop_CUR (S (length txt)) (sh_rpos g) c2 g2 i2 CU ltac:(lia)) as (c' & g' & HD & CU3). rewrite HD.
        rewrite El2 in CU3. cbn [take_while_len] in CU3. rewrite DG in CU3. cbn [skipn] in CU3.
        eexists. split; [reflexivity|].
        destruct CU3 as (S3 & C3 & ALT).
        assert (U : SF (sh_unget g') /\ rem (sh_rpos (sh_unget g')) = skipn (take_while_len is_digit l2) l2 /\ sh_cnt0 (sh_unget g') = sh_rpos g).
        { destruct ALT as [(R3 & NL3 & RM3 & _ & _) | (E3 & _ & L3 & Rp3)].
          - destruct (unget_SF g' S3 ltac:(intros _; lia)) as (Su & Cu & Lu & Ru). rewrite NL3 in Ru. rewrite Ru, Cu.
            split; [exact Su|]. split; [exact RM3 | exact C3].
          - destruct (unget_SF g' S3 ltac:(intros X; congruence)) as (Su & Cu & Lu & Ru). rewrite L3 in Ru. rewrite Ru, Cu, Rp3, rem_p by lia.
            split; [exact Su|]. split; [symmetry; exact E3 | exact C3]. }
        destruct U as (Su & RMu & Cu). split; [exact Su|]. split; [intros X; discriminate X|]. intros _. split; [|exact RMu].
        unfold sh_cnt. rewrite Cu.
        pose proof (rem_length (sh_rpos (sh_unget g')) ltac:(destruct Su as (_ & _ & _ & R & _); lia)) as L6. rewrite RMu in L6.
        unfold zlength in L6. rewrite length_skipn in L6. pose proof (take_while_len_le is_digit l2). rewrite El2 in Li2. cbn in Li2. lia.
      +
        eexists. split; [reflexivity|].
        destruct (unget_SF g2 S2 ltac:(intros _; lia)) as (Su & Cu & Lu & Ru). destruct (lim0_SF _ Su) as (Sl & Rl & Cl & Nl).
        split; [exact Sl|]. split; [intros _; unfold sh_cnt; rewrite Cl, Rl; lia|]. intros X. exfalso. apply X. reflexivity.
    -
      rewrite Ei2. change (is_digit (-1)) with false. cbn [negb take_while_len].
      eexists. split; [reflexivity|].
      destruct (unget_SF g2 S2 ltac:(intros X; congruence)) as (Su & Cu & Lu & Ru). destruct (lim0_SF _ Su) as (Sl & Rl & Cl & Nl).
      split; [exact Sl|]. split; [intros _; unfold sh_cnt; rewrite Cl, Rl; lia|]. intros X. exfalso. apply X. reflexivity.
  Qed.

  #[using="post Htxt NZ"] Lemma vfD_SF : forall f, SF f ->
    let i1 := drop_while is_space (rem (sh_rpos f)) in
    let i2 := match i1 with c :: r => if (c =? 43) || (c =? 45) then r else i1 | [] => i1 end in
    let nd := take_while_len is_digit i2 in
    (i1 = [] -> vf_D (S (length txt)) f = VInput) /\
    (i1 <> [] -> nd = 0%nat -> vf_D (S (length txt)) f = VMatch) /\
    (nd <> 0%nat -> exists f6, vf_D (S (length txt)) f = VOk f6 /\ SF f6 /\ rem (sh_rpos f6) = skipn nd i2).
  Proof.
    intros f HS. cbv zeta. unfold vf_D.
    destruct (vfW_SF f HS) as (f2 & HW & S2 & RM2). rewrite HW.
    destruct (lim0_SF f2 S2) as (S3 & R3 & C3 & N3).
    pose proof S3 as S3'. destruct S3' as (B3 & ST3 & Nn3 & Rg3 & Lg3).
    pose proof (getc_SF (sh_lim0 f2) S3) as G. destruct (sh_getc (sh_lim0 f2)) as [c4 f4].
    destruct G as (S4 & C4 & [(LT & Ec & Rc & R4 & NL4 & _) | (EQ & Ec & R4 & L4)]).
    -
      replace (c4 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      pose proof (rem_cons (sh_rpos (sh_lim0 f2)) ltac:(lia)) as RC0. rewrite <- Ec, R3 in RC0.
      pose proof RC0 as RC. rewrite RM2 in RC.
      destruct (unget_SF f4 S4 ltac:(intros _; lia)) as (Su & Cu & Lu & Ru). rewrite NL4, R4 in Ru.
      pose proof (drop_while_hd _ _ _ _ RC) as SP.
      destruct (intscan_SF (sh_unget f4) c4 (rem (sh_rpos f2 + 1)) Su ltac:(congruence) ltac:(rewrite Cu, C4, C3, Ru, R3; lia)
                  ltac:(rewrite Ru, R3; replace (sh_rpos f2 + 1 - 1) with (sh_rpos f2) by lia; exact RC0) SP)
        as (f6 & HI & S6 & Z0 & NZ0).
      rewrite HI. rewrite RC.
      split; [intros X; discriminate X|]. split.
      + intros _ ND. rewrite (Z0 ND). reflexivity.
      + intros ND. destruct (NZ0 ND) as [CN RM6]. destruct (Z.eqb_spec (sh_cnt f6) 0); [lia|]. exists f6. split; [reflexivity|]. split; [exact S6 | exact RM6].
    -
      rewrite Ec. cbn. rewrite <- RM2, <- R3, EQ, rem_p by lia. cbn.
      split; [reflexivity|]. split; [intros X; exfalso; apply X; reflexivity|]. intros X; exfalso; apply X; reflexivity.
  Qed.

  #[using="post Htxt NZ"] Lemma vfL_SF : forall ch f, SF f -> 0 <= ch ->
    (rem (sh_rpos f) = [] -> vf_L ch f = VInput) /\
    (forall c l, rem (sh_rpos f) = c :: l -> c <> ch -> vf_L ch f = VMatch) /\
    (forall c l, rem (sh_rpos f) = c :: l -> c = ch -> exists f1, vf_L ch f = VOk f1 /\ SF f1 /\ rem (sh_rpos f1) = l).
  Proof.
    intros ch f HS Hch. unfold vf_L.
    destruct (lim0_SF f HS) as (S3 & R3 & C3 & N3). pose proof S3 as S3'. destruct S3' as (B3 & ST3 & Nn3 & Rg3 & Lg3).
    pose proof (getc_SF (sh_lim0 f) S3) as G. destruct (sh_getc (sh_lim0 f)) as [c4 f4].
    destruct G as (S4 & C4 & [(LT & Ec & Rc & R4 & NL4 & _) | (EQ & Ec & R4 & L4)]).
    - pose proof (rem_cons (sh_rpos (sh_lim0 f)) ltac:(lia)) as RC. rewrite <- Ec, R3 in RC. rewrite RC.
      split; [intros X; discriminate X|]. split.
      + intros c l E NE. injection E as <- <-. destruct (Z.eqb_spec c4 ch); [lia|]. replace (c4 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      + intros c l E Ee. injection E as <- <-. rewrite (proj2 (Z.eqb_eq c4 ch) Ee). exists f4. split; [reflexivity|]. split; [exact S4|]. rewrite R4, R3. reflexivity.
    - rewrite Ec, <- R3, EQ, rem_p by lia. destruct (Z.eqb_spec (-1) ch); [lia|]. cbn.
      split; [reflexivity|]. split; intros c l E; discriminate E.
  Qed.

  Definition sd_ok (d : sdir) : Prop := match d with SL ch => 0 <= ch | _ => True end.

  #[using="post Htxt NZ"] Theorem vfs_scan_count : forall ds f mt r, Forall sd_ok ds -> SF f -> 0 <= mt ->
    vfs (S (length txt)) ds f mt = Some r ->
    r = scan_count ds (rem (sh_rpos f)) mt \/ (r = -1 /\ scan_count ds (rem (sh_rpos f)) mt = 0).
  Proof.
    induction ds as [|d ds IH]; intros f mt r OK HS Hmt HV.
    { cbn in HV |- *. left. congruence. }
    apply Forall_cons_iff in OK. destruct OK as [OKd OK].
    cbn [vfs] in HV. cbn [scan_count]. destruct d as [| |ch].
    -
      pose proof (vfD_SF f HS) as D. cbv zeta in D. destruct D as (D1 & D2 & D3).
      set (i1 := drop_while is_space (rem (sh_rpos f))) in *.
      set (i2 := match i1 with [] => i1 | c :: r0 => if (c =? 43) || (c =? 45) then r0 else i1 end) in *.
      set (nd := take_while_len is_digit i2) in *.
      destruct (Nat.eqb_spec nd 0) as [ND|ND].
      + destruct i1 as [|c l] eqn:E1.
        * rewrite (D1 eq_refl) in HV. injection HV as <-. destruct (Z.eqb_spec mt 0); [right; split; [reflexivity | lia] | left; reflexivity].
        * rewrite (D2 ltac:(intros X; discriminate X) ND) in HV. left. congruence.
      + destruct (D3 ND) as (f6 & HD & S6 & RM6). rewrite HD in HV. rewrite <- RM6. apply (IH f6 (mt + 1) r OK S6 ltac:(lia) HV).
    -
      unfold vf_W in HV |- *. destruct (vfW_SF f HS) as (f2 & HW & S2 & RM2). unfold vf_W in HW. rewrite HW in HV. rewrite <- RM2.
      apply (IH f2 mt r OK S2 Hmt HV).
    -
      cbn in OKd. destruct (vfL_SF ch f HS OKd) as (L1 & L2 & L3).
      destruct (rem (sh_rpos f)) as [|c l] eqn:E.
      + rewrite (L1 eq_refl) in HV. injection HV as <-. destruct (Z.eqb_spec mt 0); [right; split; [reflexivity | lia] | left; reflexivity].
      + destruct (Z.eqb_spec c ch) as [Ee|NE].
        * destruct (L3 c l eq_refl Ee) as (f1 & HL & S1 & RM1). rewrite HL in HV. rewrite <- RM1. apply (IH f1 mt r OK S1 Hmt HV).
        * rewrite (L2 c l eq_refl NE) in HV. left. congruence.
  Qed.

  #[using="post Htxt"] Lemma ssf0_SF : SF (ssf0 txt p).
  Proof. unfold SF, ssf0. cbn. pose proof p_lt. unfold p, zlength in *. repeat split; try reflexivity; try lia. Qed.
End Txt.

Theorem sscanf_model_scan_count : forall ds pre post r,
  Forall (fun c => 0 < c < 256) pre -> Forall (sd_ok) ds ->
  sscanf_model ds (pre ++ 0 :: post) (zlength pre) = Some r ->
  r = scan_count ds pre 0 \/ (r = -1 /\ scan_count ds pre 0 = 0).
Proof.
  intros ds pre post r NZ OK H. unfold sscanf_model in H.
  pose proof (vfs_scan_count (pre ++ 0 :: post) pre post eq_refl NZ ds (ssf0 (pre ++ 0 :: post) (zlength pre)) 0 r OK
                (ssf0_SF (pre ++ 0 :: post) pre post eq_refl) ltac:(lia) H) as V.
  unfold rem, ssf0 in V. cbn [sh_rpos Z.to_nat skipn] in V. exact V.
Qed.

Lemma sd_ok_version : Forall sd_ok FMT_VERSION. Proof. unfold FMT_VERSION. repeat constructor; cbn; lia. Qed.
Lemma sd_ok_status : Forall sd_ok FMT_STATUSLINE. Proof. unfold FMT_STATUSLINE. repeat constructor; cbn; lia. Qed.
