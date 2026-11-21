(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (16 recorded proofs replaced by written proofs (known_out, unknown_out, not_inT_lo and 13 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Shadow MI_Pres1.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Pres2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes3appC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8map_consI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list9NoDup_nilC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InI35stdpp4base5NoDup00c59OSSVerify5KrLib4Spec8MI_Pres23inTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres2:not_inT_loC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec7MI_Geom8sep_hdr0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib4Spec8MI_Pres2:not_inT_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib4Spec8MI_Pres2;not_inT_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres29known_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8sep_ghdrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr01c59OSSVerify5KrLib4Spec8MI_Pres2;unknown_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec7MI_Geom6sep_h3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec7MI_Geom7sep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres2:group_ok_XC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~C35stdpp4base7elem_ofC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveI59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres2?bl_remove_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes9MorphismsDiff_impl_subrelationC45stdpp>list_relations4list9NoDup_appK35stdpp4base<list_elem_of02K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres27inv_M_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres27inv_G_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres2;inv_SH_inclC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres2>inv_SH_write_TC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres27inv_R_XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_R_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_A_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_M_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_L_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_G_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_S_ctrlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalencec59OSSVerify5KrLib4Spec8MI_Pres2=blk_shadow_okC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop@not_iff_morphismc59OSSVerify5KrLib4Spec8MI_Pres2;inv_SH_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_pendC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Definition inT (rid : N) (lo hi : Z) (q : aptr) : Prop := fst q = rid /\ lo <= snd q < hi.

Section WRITE_T.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo hi q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Local Notation R := (MR st).

Lemma known_out q v : ~ inT (fst bm) lo hi q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
Lemma unknown_out q : ~ inT (fst bm) lo hi q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.

Lemma not_inT_lo q : snd q < lo -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [H1 _]]. lia. Qed.
Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. lia. Qed.
Lemma not_inT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo hi q.
Proof. intros H [H1 _]. exact (H H1). Qed.

Theorem inv_SH_write_T : inv_SH st' BL.
Proof.
  pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
  - intros rid sh H. rewrite HR. eapply DOM. exact H.
  - intros rid sh H. rewrite TK. eapply TKS. exact H.
  - (* [comment removed for export] *)
    intros b2 m2 i2 Hb2 Hi2. apply HE in Hb2. rewrite ME in Hi2 |- *.
    apply known_out; [| exact (D3 b2 m2 i2 Hb2 Hi2)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    unfold cnt_of in Hi2.
    destruct (aptr_eq_dec m2 m) as [Em|NEm]; [destruct (Z.eq_dec i2 i) as [Ei|NEi]|].
    + subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_intror NEi)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_introl NEm)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 o Hb2 Ho. apply HE in Hb2. apply unknown_out; [| exact (D4 b2 m2 o Hb2 Ho)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 Hb2 Ef) as [A|A];
      [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 p2 i2 Hb2 Hml Hs. apply HE in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp2 Hp2] & Hi2 & Eb2).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp2) in Eb2.
    assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo hi (fst b2, snd b2 - d)).
    { intros d Hd. subst b2. cbn [fst snd].
      destruct (N.eq_dec (fst bp2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      assert (NE : p2 <> m \/ i2 <> i).
      { destruct (aptr_eq_dec p2 m) as [->|]; [right| left; assumption]. intros ->.
        pose proof (hosts_inj _ _ _ IM _ _ _ Hp2 Hm). subst bp2. destruct Hb2 as [ai2 Hb2]. rewrite Hb2 in NH. discriminate. }
      destruct (sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH p2 bp2 i2 Hp2 Ef Hi2 NE) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    split; [exists v3; split; [apply known_out; [apply (OUT 3); lia| exact K3]| auto]|].
    split; [apply known_out; [apply (OUT 2); lia| exact K2]|].
    split; [apply known_out; [apply (OUT 1); lia| exact K1]| exact Q].
  - (* [comment removed for export] *)
    intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
    destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
    pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
    assert (NH2 : s_groups st !! (fst b2, sstart (R m2) i2) = None).
    { destruct Hb2 as [ai2 Hb2']. pose proof (is_part _ _ _ IS _ _ _ _ Hb2' Hi2) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai2 Hb2')) in P.
      unfold one5 in P. destruct (s_groups st !! (fst b2, sstart (R m2) i2)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst b2, sstart (R m2) i2) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst b2, sstart (R m2) i2) <> None) by congruence. tauto. }
    assert (NE : m2 <> m \/ i2 <> i).
    { destruct (aptr_eq_dec m2 m) as [->|]; [right| left; assumption]. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2. exact (NB k Hk Ek). }
    assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo hi (fst (bslot k), o)).
    { intros o Ho. rewrite Ek. cbn [fst].
      destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 NE NH2) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
    rewrite sstart_succ in OUT. unfold UNIT, IB in *.
    split; [apply known_out; [apply OUT; lia| exact A1]|].
    split; [apply known_out; [apply OUT; lia| exact A2]|].
    split; [apply known_out; [apply OUT; lia| exact A3]|].
    split; [apply known_out; [apply OUT; lia| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
      repeat split; try (apply known_out; [apply OUT; lia| assumption]). exact B6.
    + split; [intros Hr; apply known_out; [apply OUT; lia| apply A7; exact Hr]|].
      intros a Ha. apply unknown_out; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
  intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
  intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
  exists l1 l2, BL = l1 ++ k :: l2 /\ bl_remove (bslot k) BL = l1 ++ l2 /\ ~ In (bslot k) (map bslot l1) /\ ~ In (bslot k) (map bslot l2).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn in ND. apply NoDup_cons in ND as [N1 N2].
  destruct Hin as [<-|Hin].
  - exists [], BL. cbn. rewrite aptr_eqb_refl. repeat split; auto. intros H. apply N1. apply list_elem_of_In. exact H.
  - destruct (IH N2 Hin) as (l1 & l2 & E1 & E2 & M1 & M2).
    assert (NE : bslot b <> bslot k).
    { intros E. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin. }
    exists (b :: l1), l2. cbn. rewrite (aptr_eqb_neq (bslot b) (bslot k)) by exact NE. rewrite E1, E2 at 1. rewrite <- E1.
    repeat split; auto. cbn. intros [H|H]; [exact (NE H)| exact (M1 H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMOVE_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Let X' := mkX (x_idle X) (x_zomb X) (Some (bslot k)) (x_orph X) (x_fresh X).
Let BL' := bl_remove (bslot k) BL.
(* [comment removed for export] *)
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! (bslot k) = Some (m, i) ->
  forall q, ~ inT (fst (bslot k)) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Theorem INVL_remove_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  assert (SUB : forall k', In k' BL' -> In k' BL /\ bslot k' <> bslot k).
  { intros k' H. subst BL'. rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
    - apply in_app_iff. cbn. tauto.
    - intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H. }
  (* [comment removed for export] *)
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite NP in P.
      assert (MEMk : In (slot_start' (MR st m2) i2) (map bslot BL) <->
                     In (slot_start' (MR st m2) i2) (map bslot BL') \/ slot_start' (MR st m2) i2 = bslot k).
      { subst BL'. rewrite EBL' , EBL. rewrite !map_app. cbn. rewrite !in_app_iff. cbn. intuition congruence. }
      assert (NOTk : In (slot_start' (MR st m2) i2) (map bslot BL') -> slot_start' (MR st m2) i2 <> bslot k).
      { intros H E. subst BL'. rewrite EBL' in H. rewrite map_app, in_app_iff in H. rewrite E in H. tauto. }
      unfold one5 in P |- *.
      assert (D : @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2)) <-> slot_start' (MR st m2) i2 = bslot k) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (U' := In (slot_start' (MR st m2) i2) (map bslot BL')) in *.
      set (E := slot_start' (MR st m2) i2 = bslot k) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := None = Some (slot_start' (MR st m2) i2)) in *.
      fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. tauto.
    - intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
    - subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
      apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
      apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
    - intros k' Hk'. apply S6. apply SUB. exact Hk'. }
  assert (ISH' : inv_SH st' BL').
  { eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try eassumption.
    - apply (inv_SH_incl st BL). { intros k' H. apply SUB. exact H. } exact ISH.
    - (* [comment removed for export] *)
      destruct Hm as [ai Hm']. pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')) in P. unfold one5 in P.
      destruct (s_groups st !! (fst bm, sstart (MR st m) i)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst bm, sstart (MR st m) i) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst bm, sstart (MR st m) i) <> None) by congruence. tauto.
    - intros k' Hk' E. destruct (SUB k' Hk') as [_ NE]. apply NE. rewrite E, Ek. reflexivity.
    - intros q Hq. apply (RD m i Hs). rewrite Ek. exact Hq. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.

Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  subst BL'. rewrite EBL', EBL. rewrite !in_app_iff. cbn. split.
  - intros H. split; [tauto|]. intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
  - intros [[H|[<-|H]] NE]; [tauto| congruence| tauto].
Qed.
End REMOVE_BLOCK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk_shadow_ok (st : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
  let rid := fst (bslot k) in
  let p := snd (bslot k) + UNIT * boff k in
  let e := snd (bslot k) + get_stride (MR st m) - IB in
  let res := e - p - bsize k in
  let q := (p - snd (gbase (MR st m)) - UNIT) / UNIT in
  known st (rid, p - 4) 0
  /\ known st (rid, p - 3) (i + 32 * Z.min res 5)
  /\ known st (rid, p - 2) (byte_of q 0) /\ known st (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
  /\ (5 <= res -> known st (rid, e - 4) (byte_of res 0) /\ known st (rid, e - 3) (byte_of res 1)
                /\ known st (rid, e - 2) (byte_of res 2) /\ known st (rid, e - 1) (byte_of res 3)
                /\ known st (rid, e - 5) 0 /\ res < 2^32)
  /\ (0 < res -> known st (rid, e - res) 0)
  /\ (forall a, p <= a < p + bsize k -> unknown st (rid, a)).

Lemma inv_SH_cons st BL k m i :
  inv_SH st BL -> s_slots st !! (bslot k) = Some (m, i) -> blk_shadow_ok st k m i -> inv_SH st (k :: BL).
Proof.
  intros I Hs Hk. destruct I; constructor; try assumption.
  intros k' m' i' [<-|Hk'] Hs'.
  - rewrite Hs in Hs'. inversion Hs'. subst. exact Hk.
  - apply ish_blk; assumption.
Qed.

Section ADD_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
  forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
  0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

Theorem INVL_add_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).
  (* [comment removed for export] *)
  destruct Hm as [ai Hm'].
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
  assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
  assert (NH : s_groups st !! c = None).
  { destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite HP in P. subst BL'.
      assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
      unfold one5 in P |- *. rewrite EQm.
      assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      assert (NU' : c = slot_start' (MR st m2) i2 -> ~ In (slot_start' (MR st m2) i2) (map bslot BL)) by (intros <-; exact NU).
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (E := c = slot_start' (MR st m2) i2) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := @eq (option aptr) None (Some (slot_start' (MR st m2) i2))) in *.
      clearbody U E A F Hh P5 Q5. tauto.
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_T X st st' BL LS IM IG IS); try eassumption.
      + exists ai. exact Hm'.
      + rewrite <- Ek. exact NH.
      + intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
      + intros q Hq. apply (RD m i eq_refl). rewrite Ek. exact Hq.
    - rewrite (ce_slots _ _ CE). exact Hs.
    - exact SHK. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.
End ADD_BLOCK.
