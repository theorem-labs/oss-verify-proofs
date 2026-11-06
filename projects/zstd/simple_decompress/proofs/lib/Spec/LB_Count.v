(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Geom MI_Cnt MI_Pres1 MI_WKill MI_WFree2 KStep KLink KEv LB_Tables LB_Inv LB_Sum LB_Kernel LB_Bound.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Lemma CAP_monoC P P' c : (forall c, P c <= P' c) -> CAP P c <= CAP P' c.
Proof.
  intros HP. unfold CAP, HOSTSTD.
  assert (zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests)
          <= zsum (map (fun c' => if bighost c' =? c then (CAP0 P' c' + 32) / cmax c' else 0) guests)); [| assert (C0 : CAP0 P c <= CAP0 P' c) by (unfold CAP0; specialize (HP c); lia); lia].
  apply zsum_map_le. intros c' Hc'. destruct (bighost c' =? c); [| lia].
  assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia).
  pose proof (tab_basic_ok c' G) as (_ & CM & _). apply Z.div_le_mono; [lia|]. assert (C0 : CAP0 P c' <= CAP0 P' c') by (unfold CAP0; specialize (HP c'); lia). lia.
Qed.

Lemma NGM_mono P P' : (forall c, P c <= P' c) -> NGM P <= NGM P'.
Proof.
  intros HP. unfold NGM. apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (tab_basic_ok c Hc) as (_ & CM & _). destruct (std_nested c); [lia|].
  apply Z.div_le_mono; [lia|]. pose proof (CAP_monoC P P' c HP). lia.
Qed.

Lemma NCNT_mono P P' : (forall c, P c <= P' c) -> NCNT P <= NCNT P'.
Proof. intros HP. unfold NCNT. pose proof (NGM_mono P P' HP). pose proof (HP 63). lia. Qed.

Lemma zlen_zrange' lo n : 0 <= n -> zlen (zrange lo n) = n.
Proof. intros Hn. unfold zlen, zrange. rewrite length_map, length_seq. lia. Qed.

(* [comment removed for export] *)
Lemma nodup_range_zlen (l : list Z) s : 0 <= s -> List.NoDup l -> (forall j, In j l -> 1 <= j <= s) -> zlen l <= s.
Proof.
  intros Hs ND Hr. rewrite <- (zlen_zrange' 1 s Hs). unfold zlen. apply inj_le.
  apply (List.NoDup_incl_length ND). intros j Hj. apply in_zrange; [lia|]. pose proof (Hr j Hj). lia.
Qed.

Section COUNT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SI : SINV X st BL.
Hypothesis HAQ : AQ st BL P.
Let IR := proj1 INV.
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Definition mappedb (mb : aptr * aptr) : bool := negb (m_maplen (MR st (fst mb)) =? 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma groups_le_mapped : x_pend X = None ->
  zlen (ld_groups L) <= zcount mappedb (gmetas st) + 1.
Proof.
  intros HP. rewrite (zlen_perm _ _ (ir_groups _ _ _ IR)).
  set (regs := map_to_list (s_regions st)).
  assert (STEP : forall rs : list (N * region), List.NoDup (map fst rs) ->
            (forall kr, In kr rs -> s_regions st !! fst kr = Some (snd kr)) ->
            (forall kr, In kr rs -> r_kind (snd kr) = RKGroup -> x_orph X <> Some (fst kr)) ->
            zlen (List.filter isGb rs) <= zcount mappedb (gmetas st)).
  { intros rs ND Hrs NO. rewrite zcount_eq_zsum. unfold zlen.
    replace (Z.of_nat (length (List.filter isGb rs))) with (zsum (map (fun _ => 1) (List.filter isGb rs))) by (rewrite zsum_map_const; unfold zlen; lia).
    apply (zsum_inj_le (dec_pair) _ _ (topof st)).
    - apply List.NoDup_filter. revert ND. clear. induction rs as [|kr rs IH]; cbn; intros ND; [constructor|]. inversion ND; subst. constructor; [| apply IH; assumption].
      intros Hin. apply H1. apply in_map_iff. exists kr. auto.
    - intros [rid r] Hin. apply filter_In in Hin as [Hin K]. unfold isGb in K. cbn in K. specialize (Hrs _ Hin). cbn in Hrs.
      assert (Kg : r_kind r = RKGroup) by (destruct (r_kind r); try discriminate; reflexivity).
      destruct (ig_top _ _ _ IG rid r Hrs Kg (NO _ Hin Kg)) as (m & [ai Hm] & Hml).
      unfold topof. cbn [fst snd]. rewrite Hm. cbn. split; [apply gmetas_in; exists ai; exact Hm|].
      unfold mappedb. cbn [fst]. destruct (Z.eqb_spec (m_maplen (MR st m)) 0); [contradiction| cbn; lia].
    - intros [rid1 r1] [rid2 r2] H1 H2 E. unfold topof in E. cbn in E. apply filter_In in H1 as [H1 _]. apply filter_In in H2 as [H2 _].
      assert (rid1 = rid2) by (inversion E; reflexivity). subst rid2. pose proof (Hrs _ H1) as A1. pose proof (Hrs _ H2) as A2. cbn in A1, A2. rewrite A1 in A2. inversion A2. reflexivity.
    - intros y _. destruct (mappedb y); lia. }
  assert (FL : forall rs : list (N * region),
            zlen (map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) (List.filter (fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end) rs))
            = zlen (List.filter isGb rs)).
  { intros rs. rewrite zlen_map. reflexivity. }
  rewrite FL.
  destruct (x_orph X) as [orid|] eqn:HO.
  - destruct (s_regions st !! orid) as [ro|] eqn:Hro.
    + subst regs. rewrite (zlen_perm _ _ (Permutation_filter _ _ _ (mtl_delete (s_regions st) orid ro Hro))) || idtac.
      assert (PF : Permutation (List.filter isGb (map_to_list (s_regions st))) (List.filter isGb ((orid, ro) :: map_to_list (delete orid (s_regions st))))).
      { pose proof (mtl_delete (s_regions st) orid ro Hro) as PM. clear -PM. induction PM; cbn; [constructor| | |].
        - destruct (isGb x); [apply perm_skip|]; assumption.
        - destruct (isGb y); destruct (isGb x); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
        - etransitivity; eassumption. }
      rewrite (zlen_perm _ _ PF). cbn [List.filter].
      assert (R : zlen (List.filter isGb (map_to_list (delete orid (s_regions st)))) <= zcount mappedb (gmetas st)).
      { apply STEP.
        - apply mtl_nodup_keys.
        - intros [q rq] Hin. cbn. apply mtl_in in Hin. rewrite lookup_delete_Some in Hin. tauto.
        - intros [q rq] Hin _ E. cbn in E. inversion E; subst. apply mtl_in in Hin. rewrite lookup_delete_eq in Hin. discriminate. }
      destruct (isGb (orid, ro)); [rewrite zlen_cons|]; lia.
    + pose proof (STEP regs (mtl_nodup_keys _) ltac:(intros [q rq] Hin; apply mtl_in; exact Hin)
                   ltac:(intros [q rq] Hin _ E; cbn in E; inversion E; subst; apply mtl_in in Hin; cbn in Hin; rewrite Hro in Hin; discriminate)). lia.
  - pose proof (STEP regs (mtl_nodup_keys _) ltac:(intros [q rq] Hin; apply mtl_in; exact Hin) ltac:(intros kr _ _; discriminate)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is63b (mb : aptr * aptr) : bool := m_sizeclass (MR st (fst mb)) =? 63.
Definition isstdb (mb : aptr * aptr) : bool := (m_sizeclass (MR st (fst mb)) <? 48) && stdg st (fst mb) && mappedb mb.
Definition issmb (mb : aptr * aptr) : bool := (m_sizeclass (MR st (fst mb)) <? 48) && negb (stdg st (fst mb)).

Lemma mapped_split : zcount mappedb (gmetas st) <= zcount is63b (gmetas st) + zcount isstdb (gmetas st) + zcount issmb (gmetas st).
Proof.
  rewrite !zcount_eq_zsum, <- !zsum_map_add. apply zsum_map_le. intros [m b] Hin.
  destruct (gfacts X st L BL LS INV m b Hin) as (_ & _ & CL). unfold is63b, isstdb, issmb, mappedb. cbn [fst].
  destruct CL as [Hc|(Hc & _)].
  - replace (m_sizeclass (MR st m) =? 63) with false by (symmetry; apply Z.eqb_neq; lia). replace (m_sizeclass (MR st m) <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. destruct (stdg st m); cbn; destruct (negb _); lia.
  - rewrite Hc. cbn. destruct (negb _); lia.
Qed.

Lemma count63 : x_pend X = None -> zcount is63b (gmetas st) <= P 63.
Proof.
  intros HP. transitivity (n63 BL); [| exact (aq_big _ _ _ HAQ)]. unfold n63.
  rewrite (zcount_eq_zsum isbig BL). unfold zcount.
  replace (zlen (List.filter is63b (gmetas st))) with (zsum (map (fun _ => 1) (List.filter is63b (gmetas st)))) by (rewrite zsum_map_const; lia).
  apply (zsum_inj_le (fun x y : blk => decide (x = y)) _ _ (blk_of st BL)).
  - apply List.NoDup_filter. apply gmetas_nodup.
  - intros [m b] Hin. apply filter_In in Hin as [Hin Hc]. unfold is63b in Hc. cbn in Hc. apply Z.eqb_eq in Hc.
    destruct (blk63 X st L BL LS INV SI m b HP Hin Hc) as (Hk & _ & BIG & _). split; [exact Hk|]. rewrite BIG. lia.
  - intros [m1 b1] [m2 b2] H1 H2 E. apply filter_In in H1 as [H1 C1]. apply filter_In in H2 as [H2 C2]. unfold is63b in C1, C2. cbn in C1, C2. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
    destruct (blk63 X st L BL LS INV SI m1 b1 HP H1 C1) as (_ & S1 & _). destruct (blk63 X st L BL LS INV SI m2 b2 HP H2 C2) as (_ & S2 & _). rewrite E in S1. rewrite S1 in S2.
    destruct (gmetas_ok X st L BL LS INV m1 b1 H1) as (ai1 & Hg1 & G1). destruct (gmetas_ok X st L BL LS INV m2 b2 H2) as (ai2 & Hg2 & G2).
    destruct (slot_key_inj _ _ _ IS b1 m1 b2 m2 0 0 (ex_intro _ ai1 Hg1) (ex_intro _ ai2 Hg2) ltac:(pose proof (g_li _ _ _ _ _ _ G1); lia) ltac:(pose proof (g_li _ _ _ _ _ _ G2); lia) S2) as [<- _].
    rewrite (gmetas_meta_inj X st L BL LS INV m1 b1 b2 H1 H2). reflexivity.
  - intros k _. destruct (isbig k); lia.
Qed.

Lemma countstd : zcount isstdb (gmetas st) <= NGM P.
Proof.
  unfold NGM. rewrite zcount_eq_zsum.
  rewrite (zsum_by_class (cf st) _ (gmetas st) (cf_range X st L BL LS INV)). apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (tab_basic_ok c Hc) as (TB1 & TB2 & TB3 & TB4 & TB5).
  assert (PT : forall m b, In (m, b) (gmetas st) -> cf st (m, b) = c -> stdg st m = true ->
            (m_maplen (MR st m) = 0 <-> std_nested c = true) /\ m_sizeclass (MR st m) = c /\ cnt_of (MR st m) = cmax c).
  { intros m b Hin Ecf SG. destruct (gmetas_ok X st L BL LS INV m b Hin) as (ai & Hg & G).
    pose proof (std_lt48 X st L BL LS INV m b Hin SG) as L48.
    assert (Ec : m_sizeclass (MR st m) = c) by (unfold cf in Ecf; cbn in Ecf; destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48); [exact Ecf| lia]).
    destruct (qg_std _ _ _ SI b m ai Hg SG) as (Q1 & Q2 & Q3). rewrite Ec in Q1.
    unfold stdg in SG. apply andb_prop in SG as [SG _]. apply Z.eqb_eq in SG. unfold cls in SG. rewrite Ec in SG. auto. }
  destruct (std_nested c) eqn:NS.
  - apply Z.eq_le_incl. transitivity (zsum (map (fun _ : aptr * aptr => 0) (gmetas st))); [| rewrite zsum_map_const; lia].
    apply zsum_map_ext. intros [m b] Hin. destruct (Z.eqb_spec (cf st (m, b)) c) as [E|NE]; [| reflexivity].
    unfold isstdb, mappedb. cbn [fst]. destruct (stdg st m) eqn:SG; [| rewrite andb_false_r; reflexivity].
    destruct (PT m b Hin E SG) as (Q1 & Ec & _). rewrite (proj2 Q1 eq_refl). cbn. rewrite andb_false_r. reflexivity.
  - set (CNT := zcount (fun mb : aptr * aptr => (m_sizeclass (MR st (fst mb)) =? c) && stdg st (fst mb)) (gmetas st)).
    transitivity CNT.
    + unfold CNT. rewrite zcount_eq_zsum. apply zsum_map_le. intros [m b] Hin. unfold isstdb. cbn [fst].
      destruct (Z.eqb_spec (cf st (m, b)) c) as [E|NE].
      * destruct (stdg st m) eqn:SG.
        -- destruct (PT m b Hin E SG) as (Q1 & Ec & _). rewrite Ec, Z.eqb_refl. replace (c <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
           cbn [andb]. destruct (mappedb (m, b)); lia.
        -- rewrite !andb_false_r. cbn [andb]. lia.
      * destruct ((m_sizeclass (MR st m) =? c) && stdg st m); lia.
    + apply Zdiv_le_lower_bound; [lia|].
      transitivity (gcnt st c); [| exact (aq_slots _ _ _ HAQ c Hc)].
      rewrite gcnt_gmetas. unfold CNT. rewrite zcount_eq_zsum, Z.mul_comm, <- zsum_map_mul. apply zsum_map_le. intros [m b] Hin. cbn [fst].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|NE]; cbn [andb]; [| lia].
      destruct (stdg st m) eqn:SG; [| destruct (gfacts X st L BL LS INV m b Hin) as ([? ?] & _); lia].
      destruct (PT m b Hin ltac:(unfold cf; cbn; rewrite Ec; replace (c <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) SG) as (_ & _ & Ecnt). rewrite Ecnt. lia.
Qed.

Lemma countsmall : zcount issmb (gmetas st) <= 48 * 159.
Proof.
  rewrite zcount_eq_zsum.
  rewrite (zsum_by_class (cf st) _ (gmetas st) (cf_range X st L BL LS INV)).
  transitivity (zsum (map (fun _ : Z => 159) classes)); [| rewrite zsum_map_const; replace (zlen classes) with 48 by reflexivity; lia].
  apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (qg_small _ _ _ SI c Hc) as SM.
  transitivity (nsc st c); [| lia].
  unfold nsc. apply zsum_map_le. intros [m b] Hin. unfold issmb, cls. cbn [fst].
  destruct (gfacts X st L BL LS INV m b Hin) as (CNT & ML & _).
  unfold cf. cbn [fst]. destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48) as [LT|GE]; cbn [andb].
  - destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [E|NE]; cbn [andb].
    + destruct (stdg st m); cbn [negb]; lia.
    + destruct (Z.eqb_spec 0 c); [subst c|]; lia.
  - destruct (0 =? c); destruct ((m_sizeclass (MR st m) =? c) && negb (stdg st m)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_metas : NCAP P <= 2^40 -> zlen (ld_metas L) <= 34.
Proof.
  intros HNC. rewrite (zlen_perm _ _ (ir_metas _ _ _ IR)), zlen_map.
  set (ms := List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st))).
  assert (ND : List.NoDup ms) by (subst ms; apply List.NoDup_filter; apply mtl_nodup).
  assert (MS : forall kr, In kr ms -> s_regions st !! fst kr = Some (snd kr) /\ r_kind (snd kr) = RKMeta).
  { intros [rid r] Hin. subst ms. apply filter_In in Hin as [Hin K]. apply mtl_in in Hin. cbn in K |- *. split; [exact Hin|]. destruct (r_kind r); try discriminate; reflexivity. }
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  pose proof (aq_carved _ _ _ HAQ) as AC.
  destruct (Z.lt_ge_cases (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
  - (* [comment removed for export] *)
    destruct ms as [|[rid r] l] eqn:E; [unfold zlen; cbn [length]; lia|]. exfalso.
    destruct (MS (rid, r) ltac:(left; reflexivity)) as [Hin K]. cbn in Hin, K.
    destruct (meta_region_j X st BL SI rid r Hin K) as [[J1 J2] _]. lia.
  - pose proof (qm_shift _ _ _ SI S1) as QS.
    assert (SH : c_meta_alloc_shift (s_ctx st) <= 34).
    { destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 34) as [|GT]; [assumption|]. exfalso.
      assert (2 ^ 35 <= 2 ^ c_meta_alloc_shift (s_ctx st)) by (apply Z.pow_le_mono_r; lia). lia. }
    rewrite <- (zlen_map j_of). apply nodup_range_zlen; [lia| |].
    + (* [comment removed for export] *)
      assert (INJ : forall a b, In a ms -> In b ms -> j_of a = j_of b -> a = b).
      { intros [q1 r1] [q2 r2] H1 H2 E. destruct (MS _ H1) as [A1 M1]. destruct (MS _ H2) as [A2 M2]. cbn in A1, A2, M1, M2.
        destruct (meta_region_j X st BL SI q1 r1 A1 M1) as [_ E1]. destruct (meta_region_j X st BL SI q2 r2 A2 M2) as [_ E2].
        destruct (N.eq_dec q1 q2) as [->|NE]; [rewrite A1 in A2; inversion A2; reflexivity|].
        exfalso. apply (qm_dist _ _ _ SI q1 q2 r1 r2 A1 A2 M1 M2 NE). rewrite E1, E2, E. reflexivity. }
      revert ND INJ. clear. intros ND INJ.
      induction ms as [|a l IH]; cbn; [constructor|]. inversion ND; subst. constructor.
      * intros Hin. apply in_map_iff in Hin as (b & E & Hb). rewrite (INJ a b ltac:(left; reflexivity) ltac:(right; exact Hb) (eq_sym E)) in H1. exact (H1 Hb).
      * apply IH; [assumption|]. intros x y Hx Hy. apply INJ; right; assumption.
    + intros j Hj. apply in_map_iff in Hj as ([rid r] & <- & Hin). destruct (MS _ Hin) as [A K]. cbn in A, K.
      pose proof (proj1 (meta_region_j X st BL SI rid r A K)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ledger_count : x_pend X = None -> NCAP P <= 2^40 ->
  zlen (ld_groups L) + zlen (ld_metas L) <= NCNT P.
Proof.
  intros HP HNC. unfold NCNT.
  pose proof (groups_le_mapped HP). pose proof mapped_split. pose proof (count63 HP). pose proof countstd. pose proof countsmall. pose proof (count_metas HNC).
  lia.
Qed.
End COUNT.
