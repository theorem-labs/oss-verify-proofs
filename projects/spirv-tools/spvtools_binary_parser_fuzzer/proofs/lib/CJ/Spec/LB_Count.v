(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Geom MI_Cnt MI_Pres1
  LB_Tables LB_Sum LB_Inv LB_Kernel LB_Cnt LB_Bound.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition NGRP (P : Z -> Z) : Z :=
  zsum (map (fun c => (if std_nested c then 0 else (CAP P c + 32) / cmax c) + 160) classes) + P 63.
Definition NMETA (P : Z -> Z) : Z := Z.log2 ((2 * NCAP P + 101) / 101 + 1).
Definition NBRK (P : Z -> Z) : Z := NCAP P / 101 + 2.
Definition NE (P : Z -> Z) : Z := NGRP P + NMETA P + NBRK P.

Section COUNT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SI : SINV X st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis HPEND : x_pend X = None.
Hypothesis HORPH : x_orph X = None.
Let IR := proj1 INV.
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Local Notation REGS := (map_to_list (s_regions st)).

Definition mapped (mb : aptr * aptr) : bool := negb (m_maplen (MR st (fst mb)) =? 0).

Lemma ngroup_regions : zcount isGb REGS <= zcount mapped (gmetas st).
Proof.
  apply (zcount_inj_le dec_pair isGb mapped (topof st)).
  - apply mtl_nodup.
  - intros [rid r] Hin K. apply mtl_in in Hin. unfold isGb in K. cbn in K.
    assert (Kg : r_kind r = RKGroup) by (destruct (r_kind r); try discriminate; reflexivity).
    destruct (ig_top _ _ _ IG rid r Hin Kg ltac:(rewrite HORPH; discriminate)) as (m & [ai Hm] & Hml).
    pose proof (ig_ok _ _ _ IG _ _ _ Hm) as G. destruct (g_top _ _ _ _ _ _ G Hml) as (_ & r' & Hr' & _ & E & _). cbn in Hr'. rewrite Hin in Hr'. inversion Hr'; subst r'.
    unfold topof. cbn [fst snd]. rewrite Hm. cbn. split; [apply gmetas_in; exists ai; exact Hm|].
    unfold mapped. cbn. destruct (Z.eqb_spec (m_maplen (MR st m)) 0); [| reflexivity]. exfalso. apply Hml. assumption.
  - intros [rid1 r1] [rid2 r2] H1 H2 _ _ E. unfold topof in E. cbn in E. apply mtl_in in H1. apply mtl_in in H2.
    assert (rid1 = rid2) by (inversion E; reflexivity). subst rid2. rewrite H1 in H2. inversion H2. reflexivity.
Qed.

Definition G63 (mb : aptr * aptr) : bool := m_sizeclass (MR st (fst mb)) =? 63.
Definition GST (mb : aptr * aptr) : bool := (m_sizeclass (MR st (fst mb)) <? 48) && stdg st (fst mb) && mapped mb.
Definition GNS (mb : aptr * aptr) : bool := (m_sizeclass (MR st (fst mb)) <? 48) && negb (stdg st (fst mb)).

Lemma mapped_split : zcount mapped (gmetas st) <= zcount G63 (gmetas st) + zcount GST (gmetas st) + zcount GNS (gmetas st).
Proof.
  rewrite !zcount_eq_zsum, <- !zsum_map_add. apply zsum_map_le. intros [m b] Hin.
  destruct (gfacts X st L BL LS INV m b Hin) as (_ & _ & CL). unfold G63, GST, GNS, mapped. cbn [fst].
  destruct CL as [Hc|(Hc & _)].
  - replace (m_sizeclass (MR st m) =? 63) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (m_sizeclass (MR st m) <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. destruct (stdg st m), (m_maplen (MR st m) =? 0); cbn; lia.
  - rewrite Hc. cbn. destruct (negb _); lia.
Qed.

Lemma G63_bound : zcount G63 (gmetas st) <= n63 BL.
Proof.
  unfold n63. apply (zcount_inj_le (fun x y : blk => decide (x = y)) G63 isbig (blk_of st BL)).
  - apply gmetas_nodup.
  - intros [m b] Hin Hc. unfold G63 in Hc. cbn in Hc. apply Z.eqb_eq in Hc.
    destruct (blk63 X st L BL LS INV SI m b HPEND Hin Hc) as (Hk & _ & BIG & _). auto.
  - intros [m1 b1] [m2 b2] H1 H2 C1 C2 E. unfold G63 in C1, C2. cbn in C1, C2. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
    destruct (blk63 X st L BL LS INV SI m1 b1 HPEND H1 C1) as (_ & S1 & _). destruct (blk63 X st L BL LS INV SI m2 b2 HPEND H2 C2) as (_ & S2 & _).
    rewrite E in S1. rewrite S1 in S2.
    destruct (gmetas_ok X st L BL LS INV m1 b1 H1) as (ai1 & Hg1 & G1). destruct (gmetas_ok X st L BL LS INV m2 b2 H2) as (ai2 & Hg2 & G2).
    destruct (slot_key_inj _ _ _ IS b1 m1 b2 m2 0 0 (ex_intro _ ai1 Hg1) (ex_intro _ ai2 Hg2) ltac:(pose proof (g_li _ _ _ _ _ _ G1); lia) ltac:(pose proof (g_li _ _ _ _ _ _ G2); lia) S2) as [<- _].
    rewrite (gmetas_meta_inj X st L BL LS INV m1 b1 b2 H1 H2). reflexivity.
Qed.

Lemma GST_bound : zcount GST (gmetas st) <= zsum (map (fun c => if std_nested c then 0 else (CAP P c + 32) / cmax c) classes).
Proof.
  rewrite zcount_eq_zsum. rewrite (zsum_by_class (cf st) _ (gmetas st) (cf_range X st L BL LS INV)). apply zsum_map_le. intros c Hc. apply In_classes in Hc.
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
    unfold GST, mapped. cbn [fst]. destruct (stdg st m) eqn:SG; [| rewrite andb_false_r; reflexivity].
    destruct (PT m b Hin E SG) as (Q1 & Ec & _). rewrite (proj2 Q1 eq_refl). cbn. rewrite andb_false_r. reflexivity.
  - set (CNT := zcount (fun mb : aptr * aptr => (m_sizeclass (MR st (fst mb)) =? c) && stdg st (fst mb)) (gmetas st)).
    transitivity CNT.
    + unfold CNT. rewrite zcount_eq_zsum. apply zsum_map_le. intros [m b] Hin. unfold GST. cbn [fst].
      destruct (Z.eqb_spec (cf st (m, b)) c) as [E|NE].
      * destruct (stdg st m) eqn:SG.
        -- destruct (PT m b Hin E SG) as (_ & Ec & _). rewrite Ec, Z.eqb_refl. cbn. destruct (_ && _); lia.
        -- rewrite !andb_false_r. cbn. lia.
      * destruct (_ && _); lia.
    + apply Z.div_le_lower_bound; [lia|].
      transitivity (gcnt st c); [| exact (aq_slots _ _ _ HAQ c Hc)].
      rewrite gcnt_gmetas. unfold CNT. rewrite zcount_eq_zsum, <- zsum_map_mul. apply zsum_map_le. intros [m b] Hin. cbn [fst].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|NE]; cbn [andb]; [| lia].
      destruct (stdg st m) eqn:SG; [| destruct (gfacts X st L BL LS INV m b Hin) as ([? ?] & _); lia].
      destruct (PT m b Hin ltac:(unfold cf; cbn; rewrite Ec; replace (c <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) SG) as (_ & _ & Ecnt). rewrite Ecnt. lia.
Qed.

Lemma GNS_bound : zcount GNS (gmetas st) <= zsum (map (fun _ => 160) classes).
Proof.
  rewrite zcount_eq_zsum. rewrite (zsum_by_class (cf st) _ (gmetas st) (cf_range X st L BL LS INV)). apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (qg_small _ _ _ SI c Hc) as SM.
  transitivity (nsc st c); [| lia].
  unfold nsc. apply zsum_map_le. intros [m b] Hin. unfold GNS, cls, cf. cbn [fst].
  destruct (gfacts X st L BL LS INV m b Hin) as (CNT1 & _).
  destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48) as [LT|GE]; cbn [andb].
  - destruct (Z.eqb_spec (m_sizeclass (MR st m)) c); cbn [andb]; [destruct (negb _); lia| lia].
  - destruct (0 =? c), ((m_sizeclass (MR st m) =? c) && negb (stdg st m)); lia.
Qed.

Lemma nmeta_regions : zcount isMb REGS <= Z.max 0 (c_meta_alloc_shift (s_ctx st)).
Proof.
  unfold zcount.
  set (l := List.filter isMb REGS).
  assert (ND : List.NoDup (map j_of l)).
  { assert (ND0 : List.NoDup l) by (apply List.NoDup_filter; apply mtl_nodup).
    assert (INJ : forall a b, In a l -> In b l -> j_of a = j_of b -> a = b).
    { intros [q1 r1] [q2 r2] H1 H2 E. apply filter_In in H1 as [H1 K1]. apply filter_In in H2 as [H2 K2]. apply mtl_in in H1. apply mtl_in in H2.
      unfold isMb in K1, K2. cbn in K1, K2.
      assert (M1 : r_kind r1 = RKMeta) by (destruct (r_kind r1); try discriminate; reflexivity).
      assert (M2 : r_kind r2 = RKMeta) by (destruct (r_kind r2); try discriminate; reflexivity).
      destruct (meta_region_j X st BL SI q1 r1 H1 M1) as [_ E1]. destruct (meta_region_j X st BL SI q2 r2 H2 M2) as [_ E2].
      destruct (N.eq_dec q1 q2) as [->|NEq]; [rewrite H1 in H2; inversion H2; reflexivity|].
      exfalso. apply (qm_dist _ _ _ SI q1 q2 r1 r2 H1 H2 M1 M2 NEq). rewrite E1, E2, E. reflexivity. }
    revert ND0 INJ. generalize l. clear. intros l ND INJ.
    induction l as [|a l IH]; cbn; [constructor|]. inversion ND; subst. constructor.
    * intros Hin. apply in_map_iff in Hin as (b & E & Hb). rewrite (INJ a b ltac:(left; reflexivity) ltac:(right; exact Hb) (eq_sym E)) in H1. exact (H1 Hb).
    * apply IH; [assumption|]. intros x y Hx Hy. apply INJ; right; assumption. }
  assert (RNG : forall j, In j (map j_of l) -> 1 <= j <= c_meta_alloc_shift (s_ctx st)).
  { intros j Hj. apply in_map_iff in Hj as ([rid r] & <- & Hin). apply filter_In in Hin as [Hin K]. apply mtl_in in Hin. unfold isMb in K. cbn in K.
    exact (proj1 (meta_region_j X st BL SI rid r Hin ltac:(destruct (r_kind r); try discriminate; reflexivity))). }
  rewrite <- (zlen_map j_of).
  destruct (Z_lt_le_dec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
  - destruct (map j_of l) as [|j js] eqn:E; [rewrite zlen_nil; lia|]. exfalso. pose proof (RNG j ltac:(left; reflexivity)). lia.
  - pose proof (NoDup_incl_length ND (l' := map Z.of_nat (seq 1 (Z.to_nat (c_meta_alloc_shift (s_ctx st)))))) as LEN.
    unfold zlen. rewrite (length_map Z.of_nat), length_seq in LEN.
    assert (length (map j_of l) <= Z.to_nat (c_meta_alloc_shift (s_ctx st)))%nat; [| lia].
    apply LEN. intros j Hj. pose proof (RNG j Hj). apply in_map_iff. exists (Z.to_nat j). split; [lia|]. apply in_seq. lia.
Qed.

Lemma shift_bound : c_meta_alloc_shift (s_ctx st) <= NMETA P.
Proof.
  unfold NMETA. pose proof (proj1 (ir_shift _ _ _ IR)) as S0.
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg). pose proof (aq_carved _ _ _ HAQ) as AC.
  destruct (Z_lt_le_dec (c_meta_alloc_shift (s_ctx st)) 1) as [S1|S1].
  - transitivity 0; [lia|]. apply Z.log2_nonneg.
  - pose proof (qm_shift _ _ _ SI S1) as QS.
    assert (2 ^ c_meta_alloc_shift (s_ctx st) <= (2 * NCAP P + 101) / 101 + 1).
    { assert (2 ^ c_meta_alloc_shift (s_ctx st) - 1 <= (2 * NCAP P + 101) / 101); [| lia]. apply Z.div_le_lower_bound; lia. }
    rewrite <- (Z.log2_pow2 (c_meta_alloc_shift (s_ctx st))) by lia. apply Z.log2_le_mono. exact H.
Qed.

Lemma CB_bound : CB L <= brk_pages st.
Proof.
  pose proof (brk_pages_nonneg X st L BL LS INV) as BP.
  assert (REG : forall b l, ld_brkreg L = Some (b, l) -> l / PGSZ <= brk_pages st).
  { intros b l H. apply (ir_brkreg _ _ _ IR) in H as (rid & r & Hr & K & _ & El).
    unfold brk_pages, regions_l. change (zsum (map ?f (map_to_list (s_regions st)))) with (msum f (s_regions st)).
    rewrite (msum_delete _ (s_regions st) rid r Hr). cbn. rewrite K, El.
    assert (NN : 0 <= msum (fun kr : N * region => match r_kind kr.2 with RKBrk => r_len kr.2 / PGSZ | _ => 0 end) (delete rid (s_regions st))); [| lia].
    apply msum_nonneg. intros q rq Hq. cbn. rewrite lookup_delete_Some in Hq. destruct Hq as [_ Hq].
    pose proof (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). destruct (r_kind rq); try lia. apply Z.div_pos; unfold PGSZ; lia. }
  unfold CB. pose proof (ir_brk _ _ _ IR) as B. destruct (c_brk (s_ctx st)) as [| |rid off].
  - destruct B as [-> _]. lia.
  - first [rewrite B | destruct B as [B' _]; rewrite B']. destruct (ld_brkreg L) as [[b l]|] eqn:E; [apply (REG b l eq_refl)| lia].
  - destruct B as [-> _]. destruct (ld_brkreg L) as [[b l]|] eqn:E; [apply (REG b l eq_refl)| lia].
Qed.

Lemma brk_pages_bound : brk_pages st <= NBRK P.
Proof.
  unfold NBRK. pose proof (brk_pages_boundQ X st L IR (qm_brk _ _ _ SI)) as H.
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg). pose proof (aq_carved _ _ _ HAQ) as AC.
  assert (ncarved st / 101 <= NCAP P / 101) by (apply Z.div_le_mono; lia). unfold PGSZ in H. nia.
Qed.

Lemma gc_regions : gc L = zcount isGb REGS + zcount isMb REGS.
Proof.
  unfold gc, zcount, zlen. rewrite (Permutation_length (ir_groups _ _ _ IR)), (Permutation_length (ir_metas _ _ _ IR)), !length_map.
  unfold isGb, isMb. reflexivity.
Qed.

Theorem count_bound : gc L + CB L <= NE P.
Proof.
  unfold NE, NGRP. rewrite gc_regions.
  pose proof ngroup_regions as A1. pose proof mapped_split as A2. pose proof G63_bound as A3. pose proof GST_bound as A4. pose proof GNS_bound as A5.
  pose proof nmeta_regions as A6. pose proof shift_bound as A7. pose proof CB_bound as A8. pose proof brk_pages_bound as A9.
  pose proof (aq_big _ _ _ HAQ) as A10. pose proof (proj1 (ir_shift _ _ _ IR)) as S0.
  rewrite zsum_map_add. lia.
Qed.
End COUNT.

End AC_1.
