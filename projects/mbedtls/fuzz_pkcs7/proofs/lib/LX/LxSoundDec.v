(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxDenot LxSoundExpr.
Import ListNotations.
Open Scope Z_scope.

Section Dec.
  Context {lxHT : lx_hints}.   (* [comment removed for export] *)
  Variable CS : Z -> Prop.
  Variable E : env.

  Notation nonneg := (fun e : expr => 0 <= zden E e).
  Notation pfok := (pfact_ok CS E).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma land_le_r : forall x m, 0 <= m -> Z.land x m <= m.
  Proof.
    intros x m Hm.
    assert (H : Z.lor (Z.ldiff m x) (Z.land m x) = m) by apply Z.lor_ldiff_and.
    assert (D : Z.land (Z.ldiff m x) (Z.land m x) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit m n), (Z.testbit x n); reflexivity. }
    pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite <- Z.lxor_lor in H by exact D.
    assert (0 <= Z.ldiff m x) by (apply Z.ldiff_nonneg; left; exact Hm).
    rewrite Z.land_comm. lia.
  Qed.

  Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
  Proof. intros []; cbn; lia. Qed.

  Lemma atom_free_sound : forall a e, In e (atom_free a) -> 0 <= zden E e.
  Proof.
    intros a e Hin. unfold atom_free in Hin.
    destruct a as [z|i|i|x y|c x|o x y]; cbn in Hin; try contradiction.
    - destruct Hin as [<-|[<-|[]]]; cbn; pose proof (bv_unsigned_in_range 64 (ew E i)) as R;
        unfold bv_modulus, two64 in *; cbn in R; lia.
    - destruct o; destruct y as [k| | | | |]; cbn in Hin; try contradiction;
      try match type of Hin with context [if ?c then _ else _] => destruct c eqn:HC; [|contradiction] end;
      destruct Hin as [<-|[<-|[]]]; cbn;
      try match goal with |- context [Z.b2z ?b] => pose proof (b2z_range b); lia end.
      + apply Z.leb_le in HC. pose proof (proj2 (Z.land_nonneg (zden E x) k) ltac:(right; exact HC)). lia.
      + apply Z.leb_le in HC. pose proof (land_le_r (zden E x) k HC). lia.
      + apply Z.leb_le in HC. unfold zlow. pose proof (Z.mod_pos_bound (zden E x) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
      + apply Z.leb_le in HC. unfold zlow. pose proof (Z.mod_pos_bound (zden E x) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
      + apply Z.ltb_lt in HC. unfold zswrap.
        pose proof (Z.mod_pos_bound (zden E x + 2 ^ (k - 1)) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
      + apply Z.ltb_lt in HC. unfold zswrap.
        pose proof (Z.mod_pos_bound (zden E x + 2 ^ (k - 1)) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)).
        replace (2 ^ k) with (2 * 2 ^ (k - 1)) in * by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia.
  Qed.

  Lemma al_lookup_sound : forall pf a, Forall pfok pf -> zden E a mod 2 ^ Z.of_N (al_lookup pf a) = 0.
  Proof.
    induction pf as [|f pf IH]; intros a HF; cbn.
    - rewrite Z.pow_0_r. apply Z.mod_1_r.
    - inversion HF; subst. destruct f as [| | |b k| | | | | | | |]; try (apply IH; assumption).
      destruct (expr_eqb a b) eqn:Q; [|apply IH; assumption].
      apply expr_eqb_eq in Q. subst b. cbn in H1. rewrite zdenp_ok in H1.
      specialize (IH a H2).
      apply mod0_divide; [apply Z.pow_pos_nonneg; lia|].
      destruct (N.le_ge_cases k (al_lookup pf a)) as [Hle|Hle].
      + rewrite N.max_r by exact Hle. apply mod0_divide in IH; [exact IH| apply Z.pow_pos_nonneg; lia].
      + rewrite N.max_l by exact Hle. apply mod0_divide in H1; [exact H1| apply Z.pow_pos_nonneg; lia].
  Qed.

  Lemma align_link_sound : forall pf a e, Forall pfok pf -> In e (align_link pf a) -> 0 <= zden E e.
  Proof.
    intros pf a e HF Hin. unfold align_link in Hin.
    assert (GEN : forall a', In e (let ex := al_lookup pf a' in
              if N.leb 1 ex && N.leb ex 62 then
                let q := eatom (EOp OShr a' (ELit (Z.of_N ex))) in
                [eadd (eatom a') (emulc (- 2 ^ Z.of_N ex) q); eadd (emulc (2 ^ Z.of_N ex) q) (emulc (-1) (eatom a'))]
              else []) -> 0 <= zden E e).
    { clear Hin a. intros a Hin. cbv zeta in Hin.
      destruct (N.leb 1 (al_lookup pf a) && N.leb (al_lookup pf a) 62) eqn:C; [|destruct Hin].
      pose proof (al_lookup_sound pf a HF) as AL. set (ex := Z.of_N (al_lookup pf a)) in *.
      assert (P : 0 < 2 ^ ex) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.div_mod (zden E a) (2 ^ ex) ltac:(lia)) as D. rewrite AL, Z.add_0_r in D.
      set (q := eatom (EOp OShr a (ELit ex))) in *.
      assert (HQ : zden E q = zden E a / 2 ^ ex) by (subst q; rewrite eatom_den; cbn [zden opden]; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      destruct Hin as [<-|[<-|[]]]; rewrite ?eadd_den, ?emulc_den, ?HQ, ?eatom_den; lia. }
    destruct a; try (destruct Hin; fail); try exact (GEN _ Hin); cbn in Hin; contradiction.
  Qed.

  Lemma flat_map_align_sound : forall pf ats, Forall pfok pf -> Forall nonneg (flat_map_align pf ats).
  Proof.
    intros pf ats HF. induction ats as [|a ats IH]; cbn; [constructor|].
    apply Forall_app. split; [|exact IH]. apply List.Forall_forall. intros e He. eapply align_link_sound; eauto.
  Qed.

  Lemma land_le_rk : forall x k, 0 <= k -> 0 <= Z.land x k <= k.
  Proof.
    intros x k Hk. split; [apply Z.land_nonneg; right; exact Hk|].
    assert (D2 : Z.land (Z.ldiff k x) (Z.land k x) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit k n), (Z.testbit x n); reflexivity. }
    pose proof (Z.lor_ldiff_and k x) as R.
    rewrite <- Z.lxor_lor in R by exact D2. rewrite <- (Z.add_nocarry_lxor _ _ D2) in R.
    pose proof (proj2 (Z.ldiff_nonneg k x) (or_introl Hk)). rewrite Z.land_comm. lia.
  Qed.
  Lemma lor_bounds : forall x k, 0 <= k -> x <= Z.lor x k <= x + k.
  Proof. intros x k Hk. pose proof (Z.add_lor_land x k). pose proof (land_le_rk x k Hk). lia. Qed.

  Lemma goal_free_sound : forall a e, In e (goal_free a) -> 0 <= zden E e.
  Proof.
    intros a e Hin. unfold goal_free in Hin.
    destruct a as [z|i|i|x y|c x|o x y]; cbn [andb] in Hin; try contradiction.
    destruct o; cbn [andb] in Hin; try contradiction; destruct y as [k| | | | |]; cbn [andb] in Hin; try contradiction.
    1:{ destruct (Z.leb_spec 0 k) as [K0|K0]; [|contradiction]. pose proof (lor_bounds (zden E x) k K0) as B.
        destruct Hin as [<-|[<-|[]]]; rewrite ?eadd_den, ?emulc_den, ?eatom_den; cbn [zden opden]; lia. }
    destruct (Z.leb_spec 0 k) as [K0|K0]; cbn [andb] in Hin; [|contradiction]. destruct (Z.leb_spec k 62) as [K62|K62]; [|contradiction].
    assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_mod (zden E x) (2 ^ k) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (zden E x) (2 ^ k) P) as MB.
    set (A := EOp OShr x (ELit k)) in *.
    assert (HA : zden E A = zden E x / 2 ^ k) by (subst A; cbn [zden opden]; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    destruct Hin as [<-|[<-|[]]]; rewrite ?eadd_den, ?emulc_den, ?eatom_den, ?HA; cbn [zden]; nia.
  Qed.

  Lemma flat_map_goal_free_sound : forall ats, Forall nonneg (flat_map_goal_free ats).
  Proof.
    induction ats as [|a ats IH]; cbn; [constructor|].
    apply Forall_app. split; [|exact IH]. apply List.Forall_forall. intros e He. eapply goal_free_sound; eauto.
  Qed.

  Lemma flat_map_free_sound : forall ats, Forall nonneg (flat_map_free ats).
  Proof.
    induction ats as [|a ats IH]; cbn; [constructor|].
    apply Forall_app. split; [|exact IH]. apply List.Forall_forall. intros e He. eapply atom_free_sound; eauto.
  Qed.

  Lemma pf_pool_sound : forall pf, Forall pfok pf -> Forall nonneg (pf_pool pf).
  Proof.
    induction pf as [|f pf IH]; intros H; cbn; [constructor|].
    inversion H; subst. destruct f; cbn; try (apply IH; assumption).
    constructor; [|apply IH; assumption]. cbn in H2. rewrite zdenp_ok in H2. exact H2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma nth_N_In : forall {A} (l : list A) n d, nth_N l n d = d \/ In (nth_N l n d) l.
  Proof.
    induction l as [|x l IH]; intros n d; cbn; [left; reflexivity|].
    destruct (N.eqb n 0); [right; left; reflexivity|].
    destruct (IH (N.pred n) d) as [H|H]; [left; exact H| right; right; exact H].
  Qed.

  Lemma fk_sum_nonneg : forall pool l s, Forall nonneg pool -> fk_sum pool l = Some s -> 0 <= zden E s.
  Proof.
    intros pool l. induction l as [|[i lam] l IH]; intros s HP H; cbn in H.
    - injection H; intros <-. cbn. lia.
    - destruct (Z.ltb_spec 0 lam); [|discriminate].
      destruct (fk_sum pool l) as [acc|] eqn:Hs; [|discriminate]. injection H; intros <-.
      rewrite eadd_den, emulc_den. specialize (IH acc HP eq_refl).
      assert (0 <= zden E (nth_N pool i (ELit 0))).
      { destruct (nth_N_In pool i (ELit 0)) as [-> | Hin]; [cbn; lia|].
        rewrite List.Forall_forall in HP. apply HP. exact Hin. }
      nia.
  Qed.

  Lemma fk_check_sound : forall pool l, fk_check pool l = true -> ~ Forall nonneg pool.
  Proof.
    intros pool l H HP. unfold fk_check in H.
    destruct (fk_sum pool l) as [s|] eqn:Hs; [|discriminate].
    pose proof (fk_sum_nonneg pool l s HP Hs) as NN.
    destruct s; try discriminate. cbn in NN. apply Z.ltb_lt in H. lia.
  Qed.

  Lemma sep_l_den : forall a n b, zden E (sep_l a n b) = zden E b - zden E a - zden E n.
  Proof. intros. unfold sep_l. rewrite eadd_den, emulc_den, eadd_den. lia. Qed.

  Lemma sep_r_den : forall a b k, zden E (sep_r a b k) = zden E a - zden E b - zden E k.
  Proof. intros. unfold sep_r. rewrite eadd_den, emulc_den, eadd_den. lia. Qed.

  (* [comment removed for export] *)
  Lemma terms_divq_den : forall g ts, 0 < g -> forallb (fun t => Z.eqb (fst t mod g) 0) ts = true ->
    tden E ts = g * tden E (terms_divq g ts).
  Proof.
    intros g ts Hg. induction ts as [|[k a] ts IH]; cbn; intros H; [lia|].
    apply andb_prop in H as [Hk H]. apply Z.eqb_eq in Hk. rewrite (IH H).
    pose proof (Z.div_mod k g ltac:(lia)) as D. rewrite Hk, Z.add_0_r in D. rewrite D at 1. lia.
  Qed.

  Lemma cut_steps_sound : forall cuts pool pool', Forall nonneg pool -> cut_steps pool cuts = Some pool' -> Forall nonneg pool'.
  Proof.
    induction cuts as [|[pv g] cuts IH]; intros pool pool' HP H; cbn in H.
    - injection H; intros <-. exact HP.
    - destruct (fk_sum pool pv) as [e|] eqn:FS; [|discriminate].
      destruct (lin_of e) as [ts c] eqn:LE.
      destruct (Z.ltb 0 g && forallb (fun t => Z.eqb (fst t mod g) 0) ts) eqn:CK; [|discriminate].
      apply andb_prop in CK as [G0 DV]. apply Z.ltb_lt in G0.
      apply (IH _ _ ) in H; [exact H|]. apply Forall_app. split; [exact HP|]. constructor; [|constructor].
      cbn beta. rewrite of_terms_den.
      pose proof (fk_sum_nonneg pool pv e HP FS) as NN. pose proof (lin_of_den E e) as LD. rewrite LE in LD. cbn [fst snd] in LD.
      rewrite (terms_divq_den g ts G0 DV) in LD.
      pose proof (Z.div_mod c g ltac:(lia)) as D. pose proof (Z.mod_pos_bound c g G0) as MB. nia.
  Qed.

  Lemma cert_check_sound : forall pf c pool,
    Forall pfok pf -> cert_check pf pool c = true -> ~ Forall nonneg pool.
  Proof.
    intros pf c. induction c as [l|cuts l|j cl IHl cr IHr|j c0 IH0 cl IHl cr IHr]; intros pool HF H HP; cbn in H.
    - exact (fk_check_sound pool l H HP).
    - destruct (cut_steps pool cuts) as [pool'|] eqn:CS'; [|discriminate].
      exact (fk_check_sound pool' l H (cut_steps_sound cuts pool pool' HP CS')).
    - destruct (nth_N pf j (FGe (ELit 0))) as [|a n b k| | | | | | | | | |] eqn:Hj; try discriminate.
      apply andb_prop in H as [Hl Hr].
      assert (Hf : pfok (FSep a n b k)).
      { destruct (nth_N_In pf j (FGe (ELit 0))) as [X|X]; rewrite Hj in X; [discriminate|].
        rewrite List.Forall_forall in HF. apply HF. exact X. }
      cbn in Hf. rewrite !zdenp_ok in Hf. destruct Hf as [Hf|Hf].
      + apply (IHl _ HF Hl). constructor; [|exact HP]. cbn beta. rewrite sep_l_den. lia.
      + apply (IHr _ HF Hr). constructor; [|exact HP]. cbn beta. rewrite sep_r_den. lia.
    - destruct (nth_N pf j (FGe (ELit 0))) as [| |z a n b k| | | | | | | | |] eqn:Hj; try discriminate.
      apply andb_prop in H as [H Hr]. apply andb_prop in H as [H0 Hl].
      assert (Hf : pfok (FSep0 z a n b k)).
      { destruct (nth_N_In pf j (FGe (ELit 0))) as [X|X]; rewrite Hj in X; [discriminate|].
        rewrite List.Forall_forall in HF. apply HF. exact X. }
      cbn in Hf. rewrite !zdenp_ok in Hf. destruct Hf as [Hf|[Hf|Hf]].
      + apply (IH0 _ HF H0). constructor; [cbn beta; lia|]. constructor; [|exact HP]. cbn beta. rewrite emulc_den. lia.
      + apply (IHl _ HF Hl). constructor; [|exact HP]. cbn beta. rewrite sep_l_den. lia.
      + apply (IHr _ HF Hr). constructor; [|exact HP]. cbn beta. rewrite sep_r_den. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma comm_links_sound : forall ats all, Forall nonneg (comm_links ats all).
  Proof.
    induction ats as [|x ats IH]; intros all; cbn [comm_links]; [constructor|].
    destruct x as [| | | | |o a b]; try apply IH. destruct o; try apply IH.
    destruct (expr_mem _ _); [|apply IH].
    constructor; [|constructor; [|apply IH]]; cbn beta; rewrite eadd_den, emulc_den, !eatom_den; cbn; lia.
  Qed.

  Lemma all_lits_false_sound : forall goals b,
    all_lits_false goals = Some b -> (b = true <-> Exists nonneg goals).
  Proof.
    induction goals as [|g gs IH]; intros b H; cbn in H.
    - injection H; intros <-. split; [discriminate| intros X; inversion X].
    - destruct (is_lit g) as [c|] eqn:L; [|discriminate].
      apply is_lit_den with (E := E) in L.
      destruct (Z.leb_spec 0 c).
      + injection H; intros <-. split; [|reflexivity]. intros _. constructor. lia.
      + specialize (IH b H). split.
        * intros Hb. apply Exists_cons_tl. apply IH. exact Hb.
        * intros X. inversion X; subst; [lia|]. apply IH. assumption.
  Qed.

  Lemma neg_goals_nonneg : forall goals,
    ~ Exists nonneg goals -> Forall nonneg (map (fun g => eadd (ELit (-1)) (emulc (-1) g)) goals).
  Proof.
    induction goals as [|g gs IH]; intros H; cbn [map]; constructor.
    - cbn beta. rewrite eadd_den, emulc_den. cbn [zden].
      destruct (Z.lt_ge_cases (zden E g) 0); [lia|]. exfalso. apply H. constructor. lia.
    - apply IH. intros X. apply H. apply Exists_cons_tl. exact X.
  Qed.

  Lemma Exists_nonneg_dec : forall goals, Exists nonneg goals \/ ~ Exists nonneg goals.
  Proof.
    induction goals as [|g gs IH].
    - right. intros X. inversion X.
    - destruct (Z_le_gt_dec 0 (zden E g)).
      + left. constructor. assumption.
      + destruct IH as [IH|IH]; [left; apply Exists_cons_tl; exact IH|].
        right. intros X. inversion X; subst; [lia|]. apply IH. assumption.
  Qed.

  Theorem lin_ge_gen_sound : forall ext pf goals,
    Forall pfok pf -> lin_ge_gen ext pf goals = true -> Exists nonneg goals.
  Proof.
    intros ext pf goals HF H. unfold lin_ge_gen in H.
    destruct (all_lits_false goals) as [b|] eqn:AL.
    { apply (all_lits_false_sound goals b AL). exact H. }
    assert (POOL : ~ Exists nonneg goals -> Forall nonneg (base_pool pf goals)).
    { intros X. unfold base_pool.
      apply Forall_app. split; [apply neg_goals_nonneg; exact X|].
      apply Forall_app. split; [apply pf_pool_sound; exact HF|]. apply Forall_app. split; [apply flat_map_free_sound|].
      apply Forall_app. split; [apply flat_map_goal_free_sound|]. apply Forall_app. split; [apply flat_map_align_sound; exact HF| apply comm_links_sound]. }
    destruct (Exists_nonneg_dec goals) as [X|X]; [exact X|]. exfalso.
    apply lx_decide_true in H. destruct H as [c H].   (* [comment removed for export] *)
    exact (cert_check_sound pf c _ HF H (POOL X)).
  Qed.

  Theorem lin_ge_list_sound : forall pf goals,
    Forall pfok pf -> lin_ge_list pf goals = true -> Exists nonneg goals.
  Proof. intros pf goals. apply lin_ge_gen_sound. Qed.

  Theorem lin_ge_splits_sound : forall ext pf goals,
    Forall pfok pf -> lin_ge_splits ext pf goals = true -> Exists nonneg goals.
  Proof.
    intros ext pf goals HF H. unfold lin_ge_splits in H.
    destruct (all_lits_false goals) as [b|] eqn:AL.
    { apply (all_lits_false_sound goals b AL). exact H. }
    assert (POOL : ~ Exists nonneg goals -> Forall nonneg (base_pool pf goals)).
    { intros X. unfold base_pool.
      apply Forall_app. split; [apply neg_goals_nonneg; exact X|].
      apply Forall_app. split; [apply pf_pool_sound; exact HF|]. apply Forall_app. split; [apply flat_map_free_sound|].
      apply Forall_app. split; [apply flat_map_goal_free_sound|]. apply Forall_app. split; [apply flat_map_align_sound; exact HF| apply comm_links_sound]. }
    destruct (Exists_nonneg_dec goals) as [X|X]; [exact X|]. exfalso.
    apply lx_decide_true in H. destruct H as [c H].   (* [comment removed for export] *)
    exact (cert_check_sound pf c _ HF H (POOL X)).
  Qed.
  Theorem lin_geS_sound : forall pf e, Forall pfok pf -> lin_geS pf e = true -> 0 <= zden E e.
  Proof.
    intros pf e HF H. apply (lin_ge_splits_sound false pf [e] HF) in H. inversion H; subst; [assumption|]. inversion H1.
  Qed.

  Theorem lin_ge0_sound : forall pf e, Forall pfok pf -> lin_ge0 pf e = true -> 0 <= zden E e.
  Proof.
    intros pf e HF H. unfold lin_ge0 in H.
    assert (X : Exists nonneg [e]).
    { destruct (all_lits_false [e]) as [b|] eqn:AL.
      { apply (all_lits_false_sound [e] b AL). exact H. }
      destruct (Exists_nonneg_dec [e]) as [X|X]; [exact X|]. exfalso.
      apply lx_decide_true in H. destruct H as [c0 H].   (* [comment removed for export] *)
      apply (cert_check_sound pf c0 _ HF H). unfold base_pool.
      apply Forall_app. split; [apply neg_goals_nonneg; exact X|].
      apply Forall_app. split; [apply pf_pool_sound; exact HF|]. apply Forall_app. split; [apply flat_map_free_sound|].
      apply Forall_app. split; [apply flat_map_goal_free_sound|]. apply Forall_app. split; [apply flat_map_align_sound; exact HF| apply comm_links_sound]. }
    inversion X; subst; [assumption|]. inversion H1.
  Qed.

  Theorem lin_ge_fm_sound : forall deep pf goals,
    Forall pfok pf -> lin_ge_fm deep pf goals = true -> Exists nonneg goals.
  Proof.
    intros deep pf goals HF H. unfold lin_ge_fm in H.
    destruct (all_lits_false goals) as [b|] eqn:AL.
    { apply (all_lits_false_sound goals b AL). exact H. }
    assert (POOL : ~ Exists nonneg goals -> Forall nonneg (base_pool pf goals)).
    { intros X. unfold base_pool.
      apply Forall_app. split; [apply neg_goals_nonneg; exact X|].
      apply Forall_app. split; [apply pf_pool_sound; exact HF|]. apply Forall_app. split; [apply flat_map_free_sound|].
      apply Forall_app. split; [apply flat_map_goal_free_sound|]. apply Forall_app. split; [apply flat_map_align_sound; exact HF| apply comm_links_sound]. }
    destruct (Exists_nonneg_dec goals) as [X|X]; [exact X|]. exfalso.
    apply lx_decide_true in H. destruct H as [c H].   (* [comment removed for export] *)
    exact (cert_check_sound pf c _ HF H (POOL X)).
  Qed.

  Theorem lin_ge00_sound : forall pf e, Forall pfok pf -> lin_ge00 pf e = true -> 0 <= zden E e.
  Proof.
    intros pf e HF H. unfold lin_ge00 in H.
    assert (X : Exists nonneg [e]).
    { destruct (all_lits_false [e]) as [b|] eqn:AL.
      { apply (all_lits_false_sound [e] b AL). exact H. }
      destruct (Exists_nonneg_dec [e]) as [X|X]; [exact X|]. exfalso.
      apply lx_decide_true in H. destruct H as [c0 H].   (* [comment removed for export] *)
      apply (cert_check_sound pf c0 _ HF H). unfold base_pool.
      apply Forall_app. split; [apply neg_goals_nonneg; exact X|].
      apply Forall_app. split; [apply pf_pool_sound; exact HF|]. apply Forall_app. split; [apply flat_map_free_sound|].
      apply Forall_app. split; [apply flat_map_goal_free_sound|]. apply Forall_app. split; [apply flat_map_align_sound; exact HF| apply comm_links_sound]. }
    inversion X; subst; [assumption|]. inversion H1.
  Qed.

  Lemma refute_sound : forall pf e, Forall pfok pf -> refute pf e = true -> ~ (0 <= zden E e).
  Proof. intros pf e HF H. unfold refute in H. apply lin_ge0_sound in H; [|exact HF]. rewrite eadd_den, emulc_den in H. cbn [zden] in H. lia. Qed.

  Lemma settle1_sound : forall pf f, Forall pfok pf -> pfok f -> pfok (settle1 pf f).
  Proof.
    intros pf f HF Hf. unfold settle1.
    assert (SEP : forall a n b k, (zden E a + zden E n <= zden E b \/ zden E b + zden E k <= zden E a) ->
      pfok (if refute pf (sep_l a n b) then FGe (sep_r a b k) else if refute pf (sep_r a b k) then FGe (sep_l a n b) else FSep a n b k)).
    { intros a n b k H. destruct (refute pf (sep_l a n b)) eqn:R1.
      - apply refute_sound in R1; [|exact HF]. rewrite sep_l_den in R1. cbn. rewrite zdenp_ok, sep_r_den. lia.
      - destruct (refute pf (sep_r a b k)) eqn:R2.
        + apply refute_sound in R2; [|exact HF]. rewrite sep_r_den in R2. cbn. rewrite zdenp_ok, sep_l_den. lia.
        + cbn. rewrite !zdenp_ok. exact H. }
    destruct f; try exact Hf; cbn in Hf; rewrite !zdenp_ok in Hf.
    - apply SEP. exact Hf.
    - destruct (lin_ge0 pf (eadd z (ELit (-1)))) eqn:NZ.
      + apply SEP. apply lin_ge0_sound in NZ; try exact HF. rewrite eadd_den, ?emulc_den in NZ; cbn [zden] in NZ; lia.
      + destruct (lin_ge0 pf (eadd (emulc (-1) z) (ELit (-1)))) eqn:NZ2.
        * apply SEP. apply lin_ge0_sound in NZ2; try exact HF. rewrite eadd_den, ?emulc_den in NZ2; cbn [zden] in NZ2; lia.
        * cbn. rewrite !zdenp_ok. exact Hf.
  Qed.

  Lemma settle_seps_sound : forall pf, Forall pfok pf -> Forall pfok (settle_seps pf).
  Proof.
    intros pf HF. unfold settle_seps. apply List.Forall_forall. intros f Hf. apply in_map_iff in Hf as (g & <- & Hg).
    apply settle1_sound; [exact HF|]. rewrite List.Forall_forall in HF. apply HF. exact Hg.
  Qed.

  Theorem lin_ge_listX_sound : forall pf goals,
    Forall pfok pf -> lin_ge_listX pf goals = true -> Exists nonneg goals.
  Proof. intros pf goals. apply lin_ge_gen_sound. Qed.

  Theorem lin_ge_sound : forall pf e, Forall pfok pf -> lin_ge pf e = true -> 0 <= zden E e.
  Proof.
    intros pf e HF H. unfold lin_ge in H. apply lin_ge_list_sound in H; [|exact HF].
    inversion H; subst; [assumption|]. inversion H1.
  Qed.

  Theorem lin_geX_sound : forall pf e, Forall pfok pf -> lin_geX pf e = true -> 0 <= zden E e.
  Proof.
    intros pf e HF H. unfold lin_geX in H. apply lin_ge_listX_sound in H; [|exact HF].
    inversion H; subst; [assumption|]. inversion H1.
  Qed.


  Theorem mk_oracle_sound : forall pf, Forall pfok pf -> osound E (mk_oracle pf).
  Proof.
    intros pf HF. split.
    - intros e. apply lin_ge_sound. exact HF.
    - intros a. apply al_lookup_sound. exact HF.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma dec_le_sound : forall pf a b, Forall pfok pf -> dec_le pf a b = true -> zden E a <= zden E b.
  Proof. intros pf a b HF H. apply lin_ge_sound in H; [|exact HF]. rewrite eadd_den, emulc_den in H. lia. Qed.

  Lemma dec_lt_sound : forall pf a b, Forall pfok pf -> dec_lt pf a b = true -> zden E a < zden E b.
  Proof. intros pf a b HF H. apply lin_ge_sound in H; [|exact HF]. rewrite !eadd_den, emulc_den in H. cbn in H. lia. Qed.

  Lemma dec_eq_sound : forall pf a b, Forall pfok pf -> dec_eq pf a b = true -> zden E a = zden E b.
  Proof.
    intros pf a b HF H. apply andb_prop in H as [H1 H2].
    apply dec_le_sound in H1; [|exact HF]. apply dec_le_sound in H2; [|exact HF]. lia.
  Qed.

  Lemma dec_leX_sound : forall pf a b, Forall pfok pf -> dec_leX pf a b = true -> zden E a <= zden E b.
  Proof. intros pf a b HF H. apply lin_geX_sound in H; [|exact HF]. rewrite eadd_den, emulc_den in H. lia. Qed.

  Lemma dec_le0_sound : forall pf a b, Forall pfok pf -> dec_le0 pf a b = true -> zden E a <= zden E b.
  Proof. intros pf a b HF H. apply lin_ge0_sound in H; [|exact HF]. rewrite eadd_den, emulc_den in H. lia. Qed.
  Lemma dec_le00_sound : forall pf a b, Forall pfok pf -> dec_le00 pf a b = true -> zden E a <= zden E b.
  Proof. intros pf a b HF H. apply lin_ge00_sound in H; [|exact HF]. rewrite eadd_den, emulc_den in H. lia. Qed.

  Lemma dec_inside0_sound : forall pf a n b k, Forall pfok pf -> dec_inside0 pf a n b k = true ->
    zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k.
  Proof.
    intros pf a n b k HF H. unfold dec_inside0 in H. destruct (dec_le0 pf b a) eqn:H1; [|discriminate].
    apply dec_le0_sound in H1; [|exact HF]. apply dec_le0_sound in H; [|exact HF]. rewrite !eadd_den in H. lia.
  Qed.

  Lemma dec_inside1_sound : forall pf a n b k, Forall pfok pf -> dec_inside1 pf a n b k = true ->
    zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k.
  Proof.
    intros pf a n b k HF H. unfold dec_inside1 in H. destruct (dec_le pf b a) eqn:H1; [|discriminate].
    apply dec_le_sound in H1; [|exact HF]. apply dec_le_sound in H; [|exact HF]. rewrite !eadd_den in H. lia.
  Qed.

  Lemma dec_insideX_sound : forall pf a n b k, Forall pfok pf -> dec_insideX pf a n b k = true ->
    zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k.
  Proof.
    intros pf a n b k HF H. unfold dec_insideX in H. destruct (dec_leX pf b a) eqn:H1; [|discriminate].
    apply dec_leX_sound in H1; [|exact HF]. apply dec_leX_sound in H; [|exact HF]. rewrite !eadd_den in H. lia.
  Qed.

  Lemma any_iv_exists : forall test ivs, any_iv test ivs = true -> exists b k, In (b, k) ivs /\ test b k = true.
  Proof.
    intros test ivs. induction ivs as [|[b k] ivs IH]; cbn; intros H; [discriminate|].
    destruct (test b k) eqn:T.
    - exists b, k. split; [left; reflexivity| exact T].
    - destruct (IH H) as (b' & k' & Hin & T'). exists b', k'. split; [right; exact Hin| exact T'].
  Qed.

  Lemma dec_inside_sound : forall pf a n b k, Forall pfok pf -> dec_inside pf a n b k = true ->
    zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k.
  Proof.
    intros pf a n b k HF H. unfold dec_inside in H.
    destruct (dec_inside1 pf a n b k) eqn:D1; [exact (dec_inside1_sound pf a n b k HF D1)| exact (dec_insideX_sound pf a n b k HF H)].
  Qed.

  Lemma lin_ge_list2_sound : forall pf goals,
    Forall pfok pf -> (if lin_ge_list pf goals then true else lin_ge_listX pf goals) = true -> Exists nonneg goals.
  Proof.
    intros pf goals HF H. destruct (lin_ge_list pf goals) eqn:D; [exact (lin_ge_list_sound pf goals HF D)| exact (lin_ge_listX_sound pf goals HF H)].
  Qed.

  Lemma iv_inside_syn_sound : forall x m A N, iv_inside_syn x m A N = true ->
    zden E A <= zden E x /\ zden E x + zden E m <= zden E A + zden E N.
  Proof.
    intros x m A N H. unfold iv_inside_syn in H.
    destruct (ediff_lit x A) as [d|] eqn:HD; [|discriminate]. apply ediff_lit_den with (E := E) in HD.
    apply andb_prop in H as [H0 H]. apply Z.leb_le in H0.
    destruct (is_lit m) as [mz|] eqn:LM; [destruct (is_lit N) as [nz|] eqn:LN|].
    - apply is_lit_den with (E := E) in LM. apply is_lit_den with (E := E) in LN. apply Z.leb_le in H. lia.
    - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply expr_eqb_eq in H2. subst. lia.
    - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply expr_eqb_eq in H2. subst. lia.
  Qed.

  Lemma sep_sides_sound : forall a n b k A N B K, sep_sides a n b k A N B K = true ->
    (zden E A + zden E N <= zden E B \/ zden E B + zden E K <= zden E A) ->
    zden E a + zden E n <= zden E b \/ zden E b + zden E k <= zden E a.
  Proof.
    intros a n b k A N B K H HS. unfold sep_sides in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
      apply iv_inside_syn_sound in H1; apply iv_inside_syn_sound in H2; lia.
  Qed.

  Lemma sep_lookup_sound : forall zok pf a n b k, Forall pfok pf -> sep_lookup zok pf a n b k = true ->
    (zok = true /\ (zden E n <= 0 \/ zden E k <= 0)) \/ zden E a + zden E n <= zden E b \/ zden E b + zden E k <= zden E a.
  Proof.
    intros zok pf a n b k HF. induction pf as [|f pf IH]; intros H; [discriminate|].
    inversion HF as [|f' pf' Hf HF']; subst f' pf'. specialize (IH HF'). cbn [sep_lookup] in H.
    destruct f as [|A N B K|z A N B K| | | | | | | | |]; try exact (IH H).
    - apply orb_prop in H as [H|H]; [|exact (IH H)]. right. cbn -[zdenp] in Hf. rewrite !zdenp_ok in Hf.
      exact (sep_sides_sound _ _ _ _ _ _ _ _ H Hf).
    - apply orb_prop in H as [H|H]; [|exact (IH H)]. apply andb_prop in H as [H HS]. apply andb_prop in H as [HZ HE].
      cbn -[zdenp] in Hf. rewrite !zdenp_ok in Hf. destruct Hf as [Z0|Hf]; [|right; exact (sep_sides_sound _ _ _ _ _ _ _ _ HS Hf)].
      left. split; [exact HZ|]. apply orb_prop in HE as [HE|HE]; apply expr_eqb_eq in HE; subst; lia.
  Qed.

  Lemma dec_apart_sound : forall pf a n b k, Forall pfok pf -> dec_apart pf a n b k = true ->
    zden E a + zden E n <= zden E b \/ zden E b + zden E k <= zden E a.
  Proof.
    intros pf a n b k HF H. unfold dec_apart in H.
    destruct (sep_lookup false pf a n b k) eqn:SL.
    { destruct (sep_lookup_sound false pf a n b k HF SL) as [[X _]|X]; [discriminate| exact X]. }
    apply lin_ge_list2_sound in H; [|exact HF].
    apply Exists_cons in H. destruct H as [H|H].
    - rewrite sep_l_den in H. left. lia.
    - apply Exists_cons in H. destruct H as [H|H]; [|apply Exists_nil in H; contradiction].
      rewrite sep_r_den in H. right. lia.
  Qed.
End Dec.
