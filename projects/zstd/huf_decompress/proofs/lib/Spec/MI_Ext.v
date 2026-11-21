(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (28 recorded proofs replaced by written proofs (ctrl_eq_refl, ctrl_eq_sym, ctrl_eq_trans and 25 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Ext () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4base4fmapC35stdpp4base6LookupC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base5EmptyI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit<strip_fieldsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl;strip_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext=ctrl_eq_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9zero_hdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl?strip_zero_hdrsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@strip_enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrlAstrip_nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffK47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupc59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit>get_shadow_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6linkedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:removelastC46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:linked_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec6MI_Ext@linked_ext_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext<frontier_extC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transK59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext8gcnt_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext9usage_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext<get_head_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00c59OSSVerify5KrLib4Spec6MI_Ext=dll_ext_metasC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib4Spec6MI_Ext>live_group_extC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4unit01C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveI59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext=group_ok_ctrlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leI59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext8ce_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext9known_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext;unknown_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_R_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_A_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_M_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_L_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_G_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext:inv_S_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Ext;inv_SH_ctrlC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ctrl_eq (st st' : mstate) : Prop := mkCE {
  ce_ctx : s_ctx st' = s_ctx st;
  ce_regions : s_regions st' = s_regions st;
  ce_next_rid : s_next_rid st' = s_next_rid st;
  ce_metas : s_metas st' = s_metas st;
  ce_areas : s_areas st' = s_areas st;
  ce_groups : s_groups st' = s_groups st;
  ce_slots : s_slots st' = s_slots st;
  ce_secret : s_secret st' = s_secret st;
  ce_reserved : s_reserved st' = s_reserved st;
  ce_atop : s_atop st' = s_atop st   (* [comment removed for export] *)
}.

Lemma ctrl_eq_refl st : ctrl_eq st st.
Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_sym st st' : ctrl_eq st st' -> ctrl_eq st' st.
Proof. intros []; constructor; symmetry; assumption. Qed.
Lemma ctrl_eq_trans a b c : ctrl_eq a b -> ctrl_eq b c -> ctrl_eq a c.
Proof. intros [] []; constructor; congruence. Qed.

Lemma ctrl_eq_strip st st' : strip st' = strip st -> ctrl_eq st st'.
Proof. intros H. pose proof (strip_fields st) as A. pose proof (strip_fields st') as B. constructor; intuition congruence. Qed.

(* [comment removed for export] *)
Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h02sth11tp;2p;1p;4p;6p;<g00Sbj2ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g00I?R1f1R2f0R3/A2g00HH%@2'0P1g00I]R4g00J6R5g00JTC1%?2'0%82,01g002PR6P1P4g00KMR7g00KkR8C7R9P1P4P5P7P8g00LDE4R8g00LbC1%52'0P6P9P8g00MYC1%62'0P6P9P8g00NPC1%32'0P6P9P81267C1%92'0%>2,071277#:%;2'0%<2,07M<=X11X00P2P3O2W1W0o"). Qed.
Lemma ctrl_eq_wr8 st p v : ctrl_eq st (wr8 p v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01ph12sth21vp;3p;1p;2p;4p;6p;<g00T[j3ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g002PR1g00KMR2f2R3f1R4f0R5;A3g00HH%@3'0g00I?R6g00I]R7g00J6R8g00JTC1%?3'0%83,06P1P6P7P2g00KkR9C7R:P6P7P8P2P9g00LDE4R9g00LbC1%53'0P1P:P9g00MYC1%63'0P1P:P9g00NPC1%33'0P1P:P91212C1%93'0%>3,021222#:%;3'0%<3,02M<=X22X01X10P3P4P5O3W2W0W1o"). Qed.
Lemma ctrl_eq_wr16 st p v : ctrl_eq st (wr16 p v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01ph12sth21vp;3p;1p;2p;4p;6p;<g00UOj3ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g002PR1g00KMR2f2R3f1R4f0R5;A3g00HH%@3'0g00I?R6g00I]R7g00J6R8g00JTC1%?3'0%83,06P1P6P7P2g00KkR9C7R:P6P7P8P2P9g00LDE4R9g00LbC1%53'0P1P:P9g00MYC1%63'0P1P:P9g00NPC1%33'0P1P:P91212C1%93'0%>3,021222#:%;3'0%<3,02M<=X22X01X10P3P4P5O3W2W0W1o"). Qed.
Lemma ctrl_eq_wr32 st p v : ctrl_eq st (wr32 p v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01ph12sth21vp;3p;1p;2p;4p;6p;<g00VDj3ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g002PR1g00KMR2f2R3f1R4f0R5;A3g00HH%@3'0g00I?R6g00I]R7g00J6R8g00JTC1%?3'0%83,06P1P6P7P2g00KkR9C7R:P6P7P8P2P9g00LDE4R9g00LbC1%53'0P1P:P9g00MYC1%63'0P1P:P9g00NPC1%33'0P1P:P91212C1%93'0%>3,021222#:%;3'0%<3,02M<=X22X01X10P3P4P5O3W2W0W1o"). Qed.
Lemma ctrl_eq_havoc st p n : ctrl_eq st (havoc p n st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01nh11ph22stp;3g00W9j32Tg00Woj31Tg00Xoj30Tg00GOR0g002PR1g00KMR2f2R3f1R4f0R5;23A145330X02X11X20P3P4P5O3W0W1W2o"). Qed.
Lemma ctrl_eq_hdr_havoc st b : ctrl_eq st (hdr_havoc b st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01bh12stp;2p;1p;4p;6p;<g00Ymj2ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g002PR1f1R2f0R3/A2g00HH%@2'0g00I?R4g00I]R5g00J6R6g00JTC1%?2'0%82,04P1P4P5g00KMR7g00KkR8C7R9P4P5P6P7P8g00LDE4R8g00LbC1%52'0P1P9P8g00MYC1%62'0P1P9P8g00NPC1%32'0P1P9P81217C1%92'0%>2,071277#:%;2'0%<2,07M<=X01X10P2P3O2W0W1o"). Qed.
Lemma ctrl_eq_upd_shadow st rid f : ctrl_eq st (upd_shadow rid f st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01fh13ridh22stp;3p;1p;2p;4p;6p;<g00Zgj3ATg00;_j1@Tg003Ej20Tg00::j41Tg00<Uj1?Tg00=Oj18Tg00>Jj47Tg00>hj64Tg00?Ij15Tg00@Aj16Tg00A9j13Tg00B2j22Tg00BRj19Tg00CJj1>Tg00DCj1:Tg00Dcj1;Tg00E^j1<Tg00FUl<=Tg00GOR0g00I?R1g00[bR2P2[R2f2R3f1R4f0R5;A3g00HH%@3'0P1g00I]R6g00J6R7g00JTC1%?3'0%83,01g002PR8P1P6g00KMR9g00KkR:C7R;P1P6P7P9P:g00LDE4R:g00LbC1%53'0P8P;P:g00MYC1%63'0P8P;P:g00NPC1%33'0P8P;P:1289C1%93'0%>3,091299#:%;3'0%<3,09M<=X02X11X20P3P4P5O3W0W1W2o"). Qed.
Lemma ctrl_eq_zero_hdrs st p size i cnt : ctrl_eq st (zero_hdrs p size i cnt st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h03cnth11ih21ph34sizeh42stp;5p;3g00\[j52Tg00]Uj51Tg00Xoj30Tg00GOR0g002PR1g00KMR2g00^YR3f4R4f3R5f2R6f1R7f0R8P4D2P5P6P7P8P4D130X03X12X32X21X40P4P5P6P7P8O5W0X12W3W2W4o"). Qed.
Lemma ctrl_eq_set_size st p e n b : ctrl_eq st (set_size p e n b st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01bh11eh21nh31ph42stp;5p;3g00_8j52Tg00`1j51Tg00Xoj30Tg00GOR0g002PR1g00KMR2f4R3f3R4f2R5f1R6f0R7P3D2P4P5P6P7P3D130X02X22X11X31X40P3P4P5P6P7O5X02W2X11W3W4o"). Qed.
Lemma ctrl_eq_enframe_at st g idx n off : ctrl_eq st (fst (enframe_at st g idx n off)).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h01gh13idxh21nh33offh42stp;5p;3g00a4j53Tg006Ij32Tg00aoj50Tg00Xoj31Tg00GOR0g002PR1g00KMR2f4R3P3f3R4f2R5f1R6f0R7D39201P3P4P5P6P7D031X32X22X12X01X40P3P4P5P6P7O5X32X22W1W0W4o"). Qed.
Lemma ctrl_eq_nest_layout st g idx j size cnt : ctrl_eq st (nest_layout st g idx j size cnt).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Ext ()) [] "h03cnth11gh23idxh31jh44sizeh52stp;6p;3g00c4j62Tg00d0j61Tg00Xoj30Tg00GOR0g002PR1g00KMR2f5R3P3f4R4f3R5f2R6f1R7f0R8E2P3P4P5P6P7P8E130X02X42X32X22X11X50P3P4P5P6P7P8O6X02X42X32W2W1W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VIEWS.
Variables st st' : mstate.

Lemma MR_ext : s_metas st' = s_metas st -> forall x, MR st' x = MR st x.
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
Lemma hosts_ext : s_groups st' = s_groups st -> forall b m, hosts st' b m <-> hosts st b m.
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
Lemma live_group_ext : s_groups st' = s_groups st -> forall m, live_group st' m <-> live_group st m.
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
Lemma frontier_ext : c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) -> forall rid r, frontier st' rid r = frontier st rid r.
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
Lemma gcnt_ext : s_groups st' = s_groups st -> s_metas st' = s_metas st -> forall sc, gcnt st' sc = gcnt st sc.
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
Lemma get_head_ext : s_ctx st' = s_ctx st -> forall h, get_head st' h = get_head st h.
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.
Lemma active_ext : c_active (s_ctx st') = c_active (s_ctx st) -> forall sc, active st' sc = active st sc.
Proof. intros H sc. unfold active, ctx. rewrite H. reflexivity. Qed.
Lemma usage_ext : c_usage (s_ctx st') = c_usage (s_ctx st) -> forall sc, usage st' sc = usage st sc.
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.
Lemma get_shadow_ext' : s_shadow st' = s_shadow st -> forall rid, get_shadow st' rid = get_shadow st rid.
Proof. intros H rid. apply get_shadow_ext. exact H. Qed.
Lemma known_ext : s_shadow st' = s_shadow st -> forall p v, known st' p v <-> known st p v.
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma unknown_ext : s_shadow st' = s_shadow st -> forall p, unknown st' p <-> unknown st p.
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma linked_ext_metas : s_metas st' = s_metas st -> forall l, linked st l -> linked st' l.
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
Lemma dll_ext_metas : s_metas st' = s_metas st -> forall l, dll st l -> dll st' l.
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE. Let HT := ce_atop _ _ CE.

Lemma inv_R_ctrl : inv_R X st L -> inv_R X st' L.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HT, ?HC, ?HG; try assumption.
  - (* [comment removed for export] *)
    eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r H1 H2. rewrite FR. eauto.
Qed.

Lemma inv_A_ctrl : inv_A st -> inv_A st'.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
  destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
  - intros a ar H. destruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
  - intros sc Hsc. rewrite US, GC. auto.
Qed.

Lemma inv_M_ctrl : inv_M X st LS -> inv_M X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

Lemma inv_L_ctrl : inv_L st LS -> inv_L st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (get_head_ext st st' HC) as HE.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ctrl m b ai : group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_G_ctrl : inv_G X st LS -> inv_G X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [G1 G2 G3 G4 G5]; constructor.
  - intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
  - intros b ai H. rewrite HG in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
  - intros rid r H1 H2 H3. rewrite HR in H1. destruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
  - intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
Qed.

Lemma inv_S_ctrl : inv_S X st BL -> inv_S X st' BL.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End CTRL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_SH_set_tick st BL t : (s_tick st <= t)%N -> inv_SH st BL -> inv_SH (set_tick t st) BL.
Proof.
  intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
  intros rid sh H. destruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
  - intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
  - intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
  - intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_ctrl st st' BL : ctrl_eq st st' -> s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros CE SH TK I.
  pose proof (MR_ext st st' (ce_metas _ _ CE)) as ME. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
  destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
  - intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
  - intros b m i Hb Hi. rewrite ME in Hi |- *. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
  - intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
  - intros b m p i Hb Hml Hs. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_view st st' BL :
  s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> s_regions st' = s_regions st ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  (forall x, gbase (MR st' x) = gbase (MR st x)) ->
  (forall x, get_stride (MR st' x) = get_stride (MR st x)) ->
  (forall x, m_last_idx (MR st' x) = m_last_idx (MR st x)) ->
  (forall x, m_maplen (MR st' x) = m_maplen (MR st x)) ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros SH TK HR HG HS VB VS VL VM I.
  assert (VSS : forall x i, sstart (MR st' x) i = sstart (MR st x) i) by (intros; unfold sstart; rewrite VB, VS; reflexivity).
  assert (VC : forall x, cnt_of (MR st' x) = cnt_of (MR st x)) by (intros; unfold cnt_of; rewrite VL; reflexivity).
  pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
  destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
  - intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
  - intros b m i Hb Hi. rewrite VC in Hi. rewrite VSS. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
  - intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
  - intros b m p i Hb Hml Hs. rewrite VM in Hml. rewrite HS in Hs. rewrite !VB.
    destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !VS, !VB.
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma INVL_ctrl_same X st st' L BL LS :
  ctrl_eq st st' -> s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  INVL X st L BL LS -> INVL X st' L BL LS.
Proof.
  intros CE SH TK (IR & IA & IM & IL & IG & IS & ISH).
  split; [apply (inv_R_ctrl X st st'); assumption|].
  split; [apply (inv_A_ctrl st st'); assumption|].
  split; [apply (inv_M_ctrl X st st'); assumption|].
  split; [apply (inv_L_ctrl st st'); assumption|].
  split; [apply (inv_G_ctrl X st st'); assumption|].
  split; [apply (inv_S_ctrl X st st'); assumption|].
  apply (inv_SH_ctrl st st'); assumption.
Qed.
