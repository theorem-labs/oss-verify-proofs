(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (28 recorded proofs replaced by written proofs (cell_read_wr8, wr8_tables, hosts_sh and 25 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_free_K () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list;list_filterC35stdpp4base;RelDecisionC45stdpp;list_basics4list9app_inj_1C35stdpp4gmap;gmap_lookupC35stdpp4base6FilterC35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init5Logic2eq00C56Stdlib6NArith6BinNat1N3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbK59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC59OSSVerify5KrLib6Malloc9MallocRepBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRepCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc9MallocRepDget_shadow_wr8_otherC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes8list_indI46Stdlib5Lists4List6Exists00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffC59OSSVerify5KrLib6Malloc=MallocFacts_B5hostsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupc59OSSVerify5KrLib6Malloc8F_free_K8hosts_shC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc=MallocFacts_B5is_gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib6Malloc8F_free_K4PROTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B9hdr_knownC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I59OSSVerify5KrLib6MallocAMallocFacts_Bpres4KINV00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9ki_gmetasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_sltsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B8gmeta_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7go_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Malloc=MallocFacts_B9sstart_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7go_nestC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or01c59OSSVerify5KrLib6Malloc8F_free_K<hdr_known_shC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc=MallocFacts_B8gmeta_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ki_linksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9links_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ki_headsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8heads_lxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres6ki_homC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8homog_lxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_grpsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B9ci_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_ginjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B<ci_group_injC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K8is_gm_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_slttC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B>ci_slots_totalC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres6ki_unkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B;ci_ghdr_unkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres5ki_h0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc=MallocFacts_B7ci_hdr0C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallI59OSSVerify5KrLib6Malloc=MallocFacts_B6blk_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_blksC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib6Malloc8F_free_K7conc_shC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc=MallocFacts_B6blk_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ki_nodupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres5ki_cxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres4kctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ki_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8usage_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres5ki_bkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B6ci_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6MallocAMallocFacts_Bpres4KINV01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Malloc=MallocFacts_B9slot_freeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K6hdr_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib6Malloc8F_free_K=cell_read_wr8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses8or_morphc59OSSVerify5KrLib6Malloc8F_free_K@hdr_st_cell_readC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Malloc;MallocKit_B7free_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_KAhdr_st_known_backC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ZINV_extC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B4CINV00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_ticksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B9blk_clear00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7ci_bclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7ci_blksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7bk_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib6Malloc8F_free_K=hdr_st_tablesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K?ticks_ok_hdr_stC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Malloc=MallocFacts_B9go_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B9go_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B6go_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_lC56Stdlib6ZArith6BinInt1Z7mul_modK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib6Malloc8F_free_KFhdr_st_cell_read_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K;KINV_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib7Numbers7BinNums1N01C45stdpp;list_basics4listClist_elem_of_filterC35stdpp4base7elem_ofC35stdpp4base6filterI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC35stdpp4base8DecisionC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib4Init5Logic7and_indC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_Symmetricc59OSSVerify5KrLib6Malloc8F_free_K=In_filter_iffC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;filter_consI46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup01C35stdpp4base6decideC47Corelib4Init5Logic9False_indK46Stdlib5Lists4List5NoDup02I47Corelib4Init5Logic4True00C46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decI59OSSVerify5KrLib6Malloc=MallocFacts_B:ci_links_t00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B:ci_heads_t00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_homogC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_KANoDup_list_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K?map_filter_slotC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6MallocAMallocFacts_Bpres4LPRE00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6MallocAMallocFacts_Bpres4LPRE01C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K9conc_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5oconcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8F_free_K7pw_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_mptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B6ng_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres3amcC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma cell_read_wr8 st p v rid o :
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) rid) o =
  if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

Lemma wr8_tables st p v :
  s_regions (wr8 p v st) = s_regions st /\ s_areas (wr8 p v st) = s_areas st /\ s_groups (wr8 p v st) = s_groups st
  /\ s_slots (wr8 p v st) = s_slots st /\ s_reserved (wr8 p v st) = s_reserved st /\ s_ctx (wr8 p v st) = s_ctx st
  /\ s_tick (wr8 p v st) = s_tick st /\ (forall q, get_meta_rec (wr8 p v st) q = get_meta_rec st q).
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
  (exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
  \/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
  \/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
        /\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.

Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

Lemma hdr_known_sh p b1 i1 rid :
  fst p = rid -> (forall k, 1 <= k <= 3 -> PROT st LB rid (snd p - k)) ->
  hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof.
  intros <- HP (v3 & lo & hi & H3 & I3 & H2 & H1 & E). exists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. destruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. exists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

Lemma hdr_st_tables st pf :
  s_regions (hdr_st st pf) = s_regions st /\ s_areas (hdr_st st pf) = s_areas st /\ s_groups (hdr_st st pf) = s_groups st
  /\ s_slots (hdr_st st pf) = s_slots st /\ s_reserved (hdr_st st pf) = s_reserved st /\ s_ctx (hdr_st st pf) = s_ctx st
  /\ s_tick (hdr_st st pf) = s_tick st /\ (forall q, get_meta_rec (hdr_st st pf) q = get_meta_rec st q)
  /\ s_metas (hdr_st st pf) = s_metas st /\ s_next_rid (hdr_st st pf) = s_next_rid st.
Proof. repeat split; reflexivity. Qed.

Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
  cell_read (get_shadow (hdr_st st pf) rid) o =
    if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
    then Known (if o =? snd pf - 3 then 255 else 0)
    else cell_read (get_shadow st rid) o.
Proof.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_cell_read_other st pf rid o : ticks_ok st ->
  (rid <> fst pf \/ o < snd pf - 3 \/ snd pf <= o) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_known_back st pf rid o v : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = Known v -> exists w, cell_read (get_shadow st rid) o = Known w.
Proof.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.

(* [comment removed for export] *)
Lemma free_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> free_fp (hdr_st st pf) lo sp' a -> free_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r :
  CINV st LB -> In blk LB -> KINV st LB' c ->
  (forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk) ->
  fst pf = fst (blk_slot blk) -> (s_regions st) !! (fst pf) = Some r -> r_base r + snd pf = blk_addr blk -> snd pf mod 16 = 0 ->
  KINV (hdr_st st pf) LB' c.
Proof.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - destruct HP as (b & gh & Hb & Fb & Ho).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - destruct HP as (b & g & i & HB & Fb & Hi & ->).
    pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - destruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
  map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

Lemma LPRE_intro st LB c g p i (blk : block) :
  ci_slots st -> hosts st p g -> (s_slots st) !! (blk_slot blk) = Some (g, i) ->
  ~ slot_free (get_meta_rec st g) i -> (s_groups st) !! (blk_slot blk) = None -> c <= m_sizeclass (get_meta_rec st g) ->
  LPRE st (filter (fun b => negb (aptr_eqb (blk_slot b) (blk_slot blk))) LB) c g p i.
Proof.
  intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma drop_regions : s_regions st' = delete rid (s_regions st).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_K ()) ["CANSEC1"; "DROP"] "p;4p;1p;5p;2g00<Mj45Tg00?Hj44Tg03cSj40Tg00Ubj11Tg03coj53Tg00M9j22Tg00OWR0g00_DR1g00_]R2g00`;R3C5R4P0P4P0P3P4P0P1P2P3C4C0p,3ridp,2st#1D3'2o"). Qed.
Lemma drop_shadow : s_shadow st' = delete rid (s_shadow st).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_K ()) ["CANSEC1"; "DROP"] "p;4p;1p;5p;2g00<Mj45Tg00?Hj44Tg03cSj40Tg03dCj11Tg03coj53Tg00M9j22Tg00OWR0g00_DR1g00_]R2g00TIR3C5R4P0P4P0P3P4P0P1P2P3C4C0p,3ridp,2st#1D3'2o"). Qed.
Lemma conc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma pw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite conc_drop by exact H. reflexivity. Qed.
Lemma get_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rec_drop q : get_meta_rec st' q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_K ()) ["CANSEC1"; "DROP"] "h01qp;2g00]lj21Tg00M9j20Tg002UR0g00dPp,2stf0R1'1'0X00P1O1W0o"). Qed.

Lemma meta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !pw_drop by assumption. reflexivity.
Qed.

Lemma ctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !pw_drop by assumption. reflexivity.
Qed.
Lemma actives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply pw_drop. apply PA.
Qed.
Lemma ctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (conc_drop (brid, boff)) by exact PB. reflexivity.
Qed.
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ci_mptrs_frame st st2 : ci_mptrs st -> amc (ctx st2) = amc (ctx st) -> s_areas st2 = s_areas st -> s_regions st2 = s_regions st ->
  ci_mptrs st2.
Proof.
  intros (M1 & M2 & M3 & M4 & M5) EC EA ER.
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

End CANSEC1.
