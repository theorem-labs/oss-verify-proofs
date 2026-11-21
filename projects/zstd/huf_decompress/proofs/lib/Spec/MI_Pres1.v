(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (slot_key_inj, one5_E_irrel, R'_eq and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Pres1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4base4fmapC35stdpp4base6lookupC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base5EmptyC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres15R'_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres18R'_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext>live_group_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3iffC59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@lookup_metas_updC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib4Spec8MI_Pres15keys'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres16R'_cntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres15R'_scC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres16R'_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulc59OSSVerify5KrLib4Spec8MI_Pres16hosts'C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsBsubrelation_properc59OSSVerify5KrLib4Spec8MI_Pres17R'_lastC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17R'_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17R'_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6MI_KitAget_head_upd_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:removelastC46Stdlib5Lists4List2tlC59OSSVerify5KrLib4Spec7MI_List:linked_extC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib4Spec8MI_Pres15live'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib4Spec8MI_Pres19R'_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19R'_sstartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres18R'_gbaseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19R'_maplenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1>R'_slot_start'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1<slot_key_injC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1<one5_E_irrelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;inv_SH_viewC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1;st'_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17st'_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19st'_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1:st'_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17fR_lastC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres14R'_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19fR_maplenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres15fR_scC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres18fR_freedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres18fR_availC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17g_hostsC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveI59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres1;fR_freeableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19fR_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres17fR_gendC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres19st'_slotsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 :
  hosts st b1 m1 -> hosts st b2 m2 -> 0 <= i1 <= m_last_idx (MR st m1) -> 0 <= i2 <= m_last_idx (MR st m2) ->
  slot_start' (MR st m1) i1 = slot_start' (MR st m2) i2 -> m1 = m2 /\ i1 = i2.
Proof.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

(* [comment removed for export] *)
Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
  unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : 0 <= A' /\ 0 <= F'
  /\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
  /\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
  /\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
  let s := slot_start' (R g) i in
  one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).
(* [comment removed for export] *)
Hypothesis C_pend : pend' = x_pend X \/
  ((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
   /\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.

Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fR_mem : m_mem (f (R g)) = m_mem (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00VFj11Tg00E9j20Tg0087p,2stp,1g'2#1'0o"). Qed.
Lemma fR_prev : m_prev (f (R g)) = m_prev (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00W<j11Tg00E9j20Tg0087p,2stp,1g'2#1'0o"). Qed.
Lemma fR_next : m_next (f (R g)) = m_next (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00X3j11Tg00E9j20Tg0087p,2stp,1g'2#1'0o"). Qed.
Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00?5j11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00Xjj11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00Yej11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00Zaj11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_avail : m_avail (f (R g)) = A'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2g00E9j20Tg00G0p,2A''0o"). Qed.
Lemma fR_freed : m_freed (f (R g)) = F'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2g00E9j20Tg00G0p,2F''0o"). Qed.
Lemma fR_stride : get_stride (f (R g)) = get_stride (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00[Zj11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_gbase : gbase (f (R g)) = gbase (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00\Uj11Tg00E9j20Tg002Pp,2stp,1g'2#1'0o"). Qed.
Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h01ip;2g00>Bj22Tg00]Kj21Tg00E9j20Tg00G0R0p,2stp,1g'2f0R1'1,00X00P1O1W0o"). Qed.
Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h01ip;2g00>Bj22Tg00@Kj21Tg00E9j20Tg00G0R0g002Pp,2stp,1g'2f0R1'1'0X00P1O1W0o"). Qed.
Lemma fR_gend : gend (f (R g)) = gend (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00^Bj11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.
Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;2p;1g00>Bj22Tg00_7j11Tg00E9j20Tg00G0p,2stp,1g'2#1'0o"). Qed.

(* [comment removed for export] *)
Lemma R'_mem x : m_mem (R' x) = m_mem (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00VFj10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g0087R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_prev x : m_prev (R' x) = m_prev (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00W<j10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g0087R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_next x : m_next (R' x) = m_next (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00X3j10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g0087R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00?5j10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00Xjj10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00Yej10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00Zaj10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_stride x : get_stride (R' x) = get_stride (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00[Zj10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_gbase x : gbase (R' x) = gbase (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;6p;3g00PCj25Tg00>Bj22Tg00\Uj10Tg00_nj2:Tg00`lR0j29Tg00E9j24Tg005Mj63Tg00Kjj18Tg00SPj17Tg003Ej36Tg002PR1f1R2f0R336p=1g00Q<R4g00R3R5P4p,1gR6,53R7p,1fp,2stR8/26R9O1R:1283R;n0100000020000%031282#0'1X341:361136/971526P5P0f2/16P5P4P2P:f4R4,28R8n0100000020000#0%08R8'1P2f3/16R2P1P6%0:%0;'1X01%09,41P4P3E3W2P3O1%821418W4P3O1n10210310200021010010101b1b5p,3st'/23%73E3X01P3O1X01o"). Qed.
Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh11ih22b0h31ei001eh41mh51ni011nh61ri021ri031bp;2p;3p;6p;1g00PCj25Tg00>Bj22Tg00]Kj20Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00G0R2g00Q<R3g00R3R4P3f1R5p,1gR6'5R7p,1fp,2stR8/26R9O1R:1285n0100000020000f0R;/05f2R<,28/05512X431956A1156/8715<6P4P0f3=116P4P3P5P:f5R3,28R4n0100000020000f4R0'01040R4512P5A1106R<P1P610:3128;/03512X011090,42P3P;E3W3P;O1%6<1424W5P;O1n10210310200021010010101b2b6p,3st'/25%75E3X12X01P5P;O2W1W0o"). Qed.
Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh11ih22b0h31ei001eh41mh51ni011nh61ri021ri031bp;2p;6p;1p;3g00PCj25Tg00>Bj22Tg00@Kj20Tg00_nj2:Tg00`lR0j29Tg00E9j24Tg005Mj63Tg00Kjj18Tg00SPj17Tg003Ej36Tg002PR1f1R2f0R336p=1g00G0R4g00Q<R5g00R3R6P5p,1gR7,52R8p,1fp,2stR9/27R:O1R;1292n01000000200001032f2R<,29/02'1X451:271127/9815<7P6P0f3/17P6P5P2P;f5R5,29R6n0100000020000f4R0'01060R6'1P21107R<P1P710;51293/05'1X0110:0,41P5P3E3W3P3O1%8<1416W5P3O1n10210310200021010010101b2b6p,3st'/22%72E3X14X01P2P3O2W1X01o"). Qed.
Lemma R'_gend x : gend (R' x) = gend (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00^Bj10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p'0h01xh12b0h21ei001eh31mh41ni011nh51ri021ri031bp;2p;1p;3p;6g00PCj25Tg00>Bj22Tg00_7j10Tg003Ej31Tg00_nj29Tg00`lR0j28Tg00E9j24Tg005Mj63Tg00Kjj16Tg00SPj17Tg002PR1g00Q<R2g00R3R3P2f0R4p,1gR5'5R6p,1fp,2stR7/25R8O1R91274R:n0100000020000g00G0R;%04f1R<,27#031X321945A1145/8615<5P3P0f2=115P3P2P<P9f4R2,27R7n0100000020000#0%07R751;P<f3=115R<P1P5%09%0:51;X01%08,4;P2P4E3W2P4O1%6<14;7W4P4O1n10210310200021010010101b1b5p,3st'/24%74E3X01P4O1W0o"). Qed.
Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h01xh11mp;3p;1p;2p;6g003Ej32Tg00Kjj16Tg00>Bj20Tg00aOj11Tg00E9j25Tg00bGj24Tg005Mj63Tg002PR0f0R1p,1g520#6g00Q<R2p,2stR3f1R4'0R5g00G0R6%11f2,03#132X12%15,56p,3st'/041441E3UX00P1O1W0o"). Qed.
Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h01xh11mp;3p;1p;2p;6g003Ej32Tg00Kjj16Tg00>Bj20Tg00cBj11Tg00E9j25Tg00bGj24Tg005Mj63Tg002PR0f0R1p,1g520#6g00Q<R2p,2stR3f1R4'0R5g00G0R6%11f2,03#132X12%15,56p,3st'/041441E3UX00P1O1W0o"). Qed.

Lemma st'_groups : s_groups st' = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;4p;6p;1p;2g00CBj44Tg00C`j63Tg00:Oj40Tg00d:j11Tg00E9j22Tg002Pg00I^R0g00J<R1g00G0R2g00JUR3C4P0P1g00JnP2P3g00KLE3g00e3C0p,2st#1'2o"). Qed.
Lemma st'_slots : s_slots st' = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;4p;6p;2p;1g00CBj45Tg00C`j64Tg00B@j20Tg00:Oj41Tg00DAj13Tg00E9j22Tg002PR0g00I^R1g00J<R2g00G0R3g00JUR4C5P1P2g00JnP3P4g00KLE41003C1p,2st#3'2o"). Qed.
Lemma st'_regions : s_regions st' = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;4p;1p;2g00:Oj42Tg00ejj11Tg00E9j20Tg00I^g00J<g00Jng00fdC2p,2st#1'0o"). Qed.
Lemma st'_ctx : s_ctx st' = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;1p;2g00g]j11Tg00E9j20Tg00hSp,2st#1'0o"). Qed.
Lemma st'_areas : s_areas st' = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;4p;6p;1p;2g00CBj44Tg00C`j63Tg00:Oj40Tg00iJj11Tg00E9j22Tg002Pg00I^R0g00J<R1g00G0R2g00JUR3C4P0P1g00JnP2P3g00KLE3g00jBC0p,2st#1'2o"). Qed.
Lemma st'_shadow : s_shadow st' = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "p;4p;1p;2g00:Oj42Tg00k9j11Tg00E9j20Tg00I^g00J<g00Jng00l2C2p,2st#1'0o"). Qed.
Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h02bbh11mp;4p;6p;1p;2p;5g00CBj45Tg00C`j64Tg00:Oj40Tg00d:j11Tg00E9j23Tg00lkj52Tg002PR0p,2stR1p,3st'P0g00I^R2g00J<R3g00G0R4g00JUR5C5P2P3g00JnP4P5g00KLE4g00e3C0%11'3f1R1f0R5D2X10X00P1P5O2X10W0o"). Qed.
Lemma live' m : live_group st' m <-> live_group st m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h01mp;4p;6p;1p;2g00CBj45Tg00C`j64Tg00:Oj40Tg00d:j11Tg00E9j23Tg00mej42Tg002PR0p,2stR1p,3st'P0g00I^R2g00J<R3g00G0R4g00JUR5C5P2P3g00JnP4P5g00KLE4g00e3C0%11'3f0R1C2X00P1O1W0o"). Qed.
Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

Lemma g_hosts : hosts st b g.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres1 ()) ["MASK"] "h02aip;1p;4p;6p;2p;3g00B`j1:Tg00CBj49Tg00C`j62Tg00:Oj41Tg006Dj48Tg00d:j14Tg007Gj63Tg00FNj20Tg017aj25Tg003Ej36Tg018Xj47Tg00G0R0g00e3R1#:g002PR2P1P2g00I^R3g00J<R4P0g00JUR5C9R6P3P4g00JnP0P5g00KLE2R5P1C1P2P6P5P1C8p,1bp,2st#4E3p,1g,02f0'5,0136X00p,2aip,2HgC7o"). Qed.

Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      * (* [comment removed for export] *)
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      * (* [comment removed for export] *)
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.
