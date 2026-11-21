(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (In_map_to_list_regions, lranges_iff, forallb_ext and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Ledger () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupI35stdpp4gmap4gmap00C35stdpp8fin_mapsCelem_of_map_to_listC46Stdlib5Lists4List7map_extC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00I35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp4base?list_elem_of_InC47Corelib4Init5Logic5proj1K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01C35stdpp8fin_maps;map_to_listI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI47Corelib4Init5Logic2or00C47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib5Lists4List:in_app_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC59OSSVerify5KrLib4Spec6MI_Inv9ir_groupsC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Inv8ir_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ir_brkregC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_LedgerFIn_map_to_list_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic5proj2C46Stdlib5Lists4List6in_mapC46Stdlib7Sorting;Permutation?Permutation_symC59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Inv7ir_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z3divI47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop?or_iff_morphismI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses?iff_equivalenceC46Stdlib5Lists4List8map_consK47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec6Malloc;iv_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger;forallb_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger;lranges_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=is_errno_formC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib4Spec9MI_Ledger>ranges_free_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv=lbrk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib5Lists4List8nil_consI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_insertC35stdpp4base6insertC35stdpp8fin_mapsBmap_to_list_insertC59OSSVerify5KrLib4Spec9MI_WFree2;perm_filterC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6ir_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith4Znat3N2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6MI_KitAlookup_new_regionC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbK59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notc59OSSVerify5KrLib4Spec9MI_Ledger9ng_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger8ng_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger=mmap_ok_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree2;round_up_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succc59OSSVerify5KrLib4Spec9MI_Ledger7ng_someC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEs_next_rid_new_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_LedgerCranges_free_regionsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation02C46Stdlib7Sorting;Permutation@Permutation_reflc59OSSVerify5KrLib4Spec9MI_LedgerCregions_insert_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib7Sorting;PermutationAPermutation_transC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger;ng_frontierC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Ledger7ng_keepC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres27inv_M_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_M_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_L_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres2:group_ok_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext2<group_ok_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27inv_S_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Ext29inv_S_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minK59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z8inj_succI59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_map_to_list_regions st rid r : In (rid, r) (map_to_list (s_regions st)) <-> s_regions st !! rid = Some r.
Proof.
  split.
  - intros H. apply elem_of_map_to_list. apply list_elem_of_In. exact H.
  - intros H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact H.
Qed.

Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.

Lemma lranges_iff x : In x (lranges L) <-> In x (live_ranges st).
Proof.
  unfold lranges, live_ranges. rewrite (proj1 (ir_resv _ _ _ IR)). rewrite !in_app_iff. split.
  - intros [H|[H|[H|H]]]; [left; exact H| right| right| right].
    + apply in_map_iff in H as ([b l] & <- & Hg). cbn.
      pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hg) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
      cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
    + apply in_map_iff in H as ([[b l] kk] & <- & Hm). cbn.
      pose proof (Permutation_in _ (ir_metas _ _ _ IR) Hm) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
      cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
    + destruct (ld_brkreg L) as [[b l]|] eqn:EB; [| destruct H]. destruct H as [<-|[]].
      destruct (proj1 (ir_brkreg _ _ _ IR b l) EB) as (rid & r & Hr & Hk & <- & <-).
      apply in_map_iff. exists (rid, r). split; [| apply In_map_to_list_regions; exact Hr].
      cbn. unfold region_live_range. rewrite Hk. reflexivity.
  - intros [H|H]; [left; exact H| right].
    apply in_map_iff in H as ([rid r] & <- & Hin). cbn. apply In_map_to_list_regions in Hin.
    unfold region_live_range. destruct (r_kind r) eqn:Hk.
    + right. right. rewrite (proj2 (ir_brkreg _ _ _ IR (r_base r) (r_len r))); [left; reflexivity| exists rid, r; auto].
    + right. left.
      assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1)) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_metas _ _ _ IR)) Hm) as Hm'.
      apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
    + left.
      assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR)) Hm) as Hm'.
      apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
Qed.

Lemma forallb_ext {A} (f : A -> bool) l1 l2 : (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
  intros H. destruct (forallb f l1) eqn:E1; destruct (forallb f l2) eqn:E2; try reflexivity.
  - rewrite forallb_forall in E1. assert (E2' : forallb f l2 = true) by (apply forallb_forall; intros x Hx; apply E1; apply H; exact Hx). congruence.
  - rewrite forallb_forall in E2. assert (E1' : forallb f l1 = true) by (apply forallb_forall; intros x Hx; apply E2; apply H; exact Hx). congruence.
Qed.

Lemma ranges_free_eq a n : ranges_free (lranges L) a n = ranges_free (live_ranges st) a n.
Proof. unfold ranges_free. apply forallb_ext. apply lranges_iff. Qed.

Lemma mmap_answer_ok_eq len r : mmap_answer_ok (ld_atop L) (lranges L) len r = mmap_answer_ok (s_atop st) (live_ranges st) len r.
Proof. unfold mmap_answer_ok. rewrite ranges_free_eq, (proj1 (proj2 (ir_resv _ _ _ IR))). reflexivity. Qed.

Lemma brk_pages_ok_eq lo len : lbrk_pages_ok L lo len = brk_pages_ok st lo len.
Proof. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq, (proj1 (proj2 (ir_resv _ _ _ IR))). reflexivity. Qed.

(* [comment removed for export] *)
Lemma ranges_free_regions a n rid r : ranges_free (live_ranges st) a n = true -> s_regions st !! rid = Some r ->
  let '(b, l) := region_live_range r in a + n <= b \/ b + l <= a.
Proof.
  intros H Hr. unfold ranges_free in H. rewrite forallb_forall in H.
  specialize (H (region_live_range r)). destruct (region_live_range r) as [b l] eqn:E.
  assert (Hin : In (b, l) (live_ranges st)).
  { unfold live_ranges. apply in_app_iff. right. apply in_map_iff. exists (rid, r). rewrite <- E. split; [reflexivity| apply In_map_to_list_regions; exact Hr]. }
  specialize (H Hin). cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H| apply Z.leb_le in H]; lia.
Qed.
End RANGES.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_ok_facts atop live len r :
  mmap_answer_ok atop live len r = true -> is_err r = false ->
  0 < r /\ r mod PGSZ = 0 /\ r + round_up_pg len <= atop /\ ranges_free live r (round_up_pg len) = true.
Proof.
  unfold mmap_answer_ok, is_errno_form, is_err. intros H E.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
  - apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma regions_insert_perm (st : mstate) rid r (F : N * region -> bool) :
  s_regions st !! rid = None ->
  Permutation (List.filter F (map_to_list (<[rid := r]> (s_regions st)))) (List.filter F ((rid, r) :: map_to_list (s_regions st))).
Proof. intros H. apply perm_filter. apply map_to_list_insert. exact H. Qed.

Section NEW_GROUP_REGION.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r len : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = None.
Hypothesis HOK : mmap_answer_ok (s_atop st) (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HLEN : 0 < len < LEN_MAX.
Let rid := s_next_rid st.
Let st' := fst (new_region RKGroup r len st).
Let L' := KInv.set_groups ((r, len) :: ld_groups L) L.
Let X' := xorph X (Some rid).

Lemma ng_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma ng_lookup q : s_regions st' !! q = if (q =? rid)%N then Some (mkRegion RKGroup r len) else s_regions st !! q.
Proof. unfold st'. apply lookup_new_region. Qed.
Lemma ng_keep q rq : s_regions st !! q = Some rq -> s_regions st' !! q = Some rq.
Proof. intros H. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite ng_fresh in H; discriminate| exact H]. Qed.
Lemma ng_some q rq : s_regions st' !! q = Some rq -> (q = rid /\ rq = mkRegion RKGroup r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma ng_frontier q rq : frontier st' q rq = frontier st q rq.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ledger ()) ["NEW_GROUP_REGION"] "h01qh12rqp;3p;2g00\lj31Tg00ZGj20Tg00AcR0g00BAR1g00k\p,2stf1R2f0R331'0X11X00P2P3O2W1W0o"). Qed.

Theorem INVL_new_group_region : INVL X' st' L' BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (mmap_ok_facts _ _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
  pose proof (round_up_ge len) as RU.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[new_region st' frontier region_live_range round_up_pg Z.mul Z.pow Z.add filter].
    + intros q rq Hq. unfold st'. rewrite s_next_rid_new_region. apply ng_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
      split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros [K|K]; discriminate.
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply ng_some in H1 as [[-> ->]|[N1 H1]]; apply ng_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D.
        destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D.
        destruct (region_live_range r1) as [b1 l1]. cbn. lia.
    + exact ir_resv.
    + unfold L'. cbn. eapply Permutation_trans; [apply perm_skip; exact ir_groups|].
      fold rid.
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
      cbn. apply Permutation_refl.
    + unfold L'. cbn. eapply Permutation_trans; [exact ir_metas|].
      fold rid.
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
      cbn. erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn. rewrite ng_frontier. reflexivity.
    + intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_metalen q rq Hq K).
    + intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_brkfront q rq Hq K).
    + destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
      right. exists q, rq. split; [apply ng_keep; exact Hq| auto].
    + intros b l. unfold L'. cbn. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
      * split; [apply ng_keep; exact Hq| auto].
      * apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
    + intros q1 q2 r1 r2 H1 H2 K1 K2. apply ng_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply ng_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
      exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + unfold L'. cbn. revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply ng_keep; exact Hq| auto].
    + destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
      intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply ng_keep; exact Hq| auto].
    + intros q Hq. unfold X' in Hq. cbn in Hq. inversion Hq. subst q. exists (mkRegion RKGroup r len).
      split; [rewrite ng_lookup, N.eqb_refl; reflexivity|]. split; [reflexivity|].
      intros b Hb. change (s_groups st') with (s_groups st). destruct (s_groups st !! b) as [h|] eqn:E; [| reflexivity]. exfalso.
      destruct (ig_region _ _ _ IG _ _ E) as (rq & Hrq & _). rewrite Hb in Hrq. fold rid in Hrq. rewrite ng_fresh in Hrq. discriminate.
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite ng_frontier. split; [apply ng_keep; exact Hq| auto].
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
  - apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
      * intros q rq Hq K E. apply ng_keep. exact Hq.
      * apply (group_ok_X X); [reflexivity|]. exact (G1 m b ai Hb).
    + exact G2.
    + exact G3.
    + intros q rq Hq K Ho. apply ng_some in Hq as [[-> ->]|[NE Hq]].
      * exfalso. apply Ho. reflexivity.
      * apply (G4 q rq Hq K). rewrite HO. discriminate.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply ng_keep; exact Hq| exact K].
  - apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
Qed.
End NEW_GROUP_REGION.
