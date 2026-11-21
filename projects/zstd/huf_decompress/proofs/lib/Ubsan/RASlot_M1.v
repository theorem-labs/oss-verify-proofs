(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (rec_st', rta_slot_ok, rhk1_ok); rhk1_ok is zstd/simple_decompress's proof with this binary's image end). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W9 RASlot_M0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_M1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsCeq_rewrite_relationC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_mfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_A8MFACTS_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W97gmf_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W97gmf_grpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_geomC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Malloc9Malloc_fp>lowbit_testbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib6Malloc8ASlot_W07tr_bitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_masksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_masksC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc=MallocFacts_A=mf_free_clearC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Malloc=MallocFacts_A7mf_hdr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_lfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS=lf_bit_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9mf_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_AAmf_slots_completeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Malloc8ASlot_W09tr_mrangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_fast;lowbit_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W96gmf_mwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS5mw_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc8ASlot_W08tr_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib6Malloc8ASlot_W09tr_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib6Malloc8ASlot_W08tr_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BBmeta_slot_put_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc7ASlot_I9ENTRY_REL00C1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC47Corelib4Init5Logic3iffI59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3orbK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countablec59OSSVerify5KrLib5Ubsan9RASlot_M17rec_st'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W16as_grpC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan8RASlot_I9ras_post2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RASlot_W96rta_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib5Ubsan@RAllocSlot_iface<RAS_STACK_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RASlot_M1;rta_slot_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMalloc_fpArmeta_chunk_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTreeArpres_except_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_BArmeta_slot_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2geC59OSSVerify5KrLib5Ubsan:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc7ASlot_I7as_inv200C1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib5Ubsan;RMallocTreeErpres_except_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_A=rauxv_ok_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_M0=ticks_ok_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_AAticks_ok_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W09tr_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Malloc8ASlot_W07tr_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W0;tr_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp4mrel01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W06tr_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W09tr_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W9?active_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I8ret_spanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc7ASlot_I7as_inv201C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A6mf_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8fact_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_fast:ctz32_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W14as_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat3N2Z6inj_leI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib5Ubsan9RASlot_M1:rerrno_litC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Ubsan4UImg:RAUXV_CELLC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

Lemma rta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  (* [comment removed for export] *)
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
  assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  destruct (FM g b Hmem) as (FM1 & FM2 & _).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
    exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed.
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rerrno_lit : errno_addr tp = 0x3b7fc.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_M1 ()) ["CANSEC1"; "LEVEL"] "h02Hah13ERRh22HKh33idxh43ms'h52s'h63st1h75ATOPRh87__arithh94__ffh:7__sat12h;7__sat13h<7__sat14h=7__sat15h>8__varmaph?5__with@2tphA1zp;1p;2p;3p;4p;Op;7p;6p;8p,1RR0p4p300R1p10000p4p710p8P1p1000Sp4p710p8P1g02LeR2p4p7210p8P1p1001]R3p4p7210p8P1P3p4p710p8P1p1009Jp4p710p8P1p1002Qp4p710p8P1p102Mbp4p710p8g00C9j10Tg01X?j1VTg02N]j1PTg02O@j2ITg02Ofj2;Tg00TJj11Tg01S@j1RTg00ZIj28Tg02PPj1OTg00l=j1ETg0241j3KTg02QEj4JTg02R;lOHTP2j7WTg00C^j14Tg00DYj39Tg00E3j2FTg02S8j1UTg02T6j1TTg00eSj2>Tg00Uij2BTg00k1j2GTg00bmj27Tg00D<j2ATg00kYj3@Tg00l]j1NTg01>^j1MTg00m=j1LTg00m[j1QTg00nFj2?Tg01mZj4CTg01X]j3STg01oMj7`Tg00onj2_Tg010Pj2^Tg011<j3]Tg011[j4\Tg02Tlj2XTg006Cj6Yj8ZTg01nEj7[Tf0R2#0#0#0#0p=<%02#0p=6%12#0p=3%12#1#1#1p=2%12#1p==%02#0#0#0#0#0#0#0p=:g026NR1/>2p=5f1R3g02<bR4g02=AR5P5g02=aR6P2g02>hF[p=Dg00HOR7#0R8#<R9#0R:#VR;#PR<g02Uh,I;R=g02VbR>p,1mR?1;;2%18#6#1#6#RR@'8g02WWRAp,4errv#O%EA3KRACJg02XLRBg00I4RCg02YERDg02Z>REp,2rcRFp,2raRGp,2spRHp,2gpRIf5p,2s0RJp,2s1RKp,2s2RLp,2s3RMp,2s4RNp,2s5ROp,2s6RPp,2s7RQp,2s8RRp,2s9RSp,3s10RTp,3s11RUp,1FRVp,2fcRWp,1oRXP?p,3st0RYp,2stRZp,1sR[p,2loR\p,2scR]p,3reqR^f3R_f2R`P3P2MOHPFP0PXp,1kf4P_O2P`p,1QP3FWR0[]4]5]3]61;;`/8@%17#3#1#3#1#2#2#6#4Ra59C]2]1X@<P>P?1;;=/8@R>PACJPFPGPHPIP=PJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP?PYPZP[P\P]P^P_P`P3P2MOHP0[^4E^5D^3C^6BPC%17#3#=#3#6#3#3#<#4RB182@=9CaXAC1FCa1I;B,;;%UF%=7#2#2#2R7#0#1#=#2#3#6#<#:#:#4%TFRF'>%27#2#3#6#<#:#:#4,>F'B%48R8%49R9'G1718RF%591A89R7,71[[%58R@g02H>RDA@893UW0%57\D^0@%4:R:,G8%5:1A8:R7,71[\FA@8:3VDX0@%57\D^0@g02ANR@#E%N@%MC%LC%QCR@P4P5P5P6PC1?C1g02>A1?CBR5CC,D@PCP5g02?H1?C8=SC;CC,D@F`1_@6P2P`g02:mR@g02;MR6'F1^2`=9@6dA]C13C\b9b>b?%5B17B7'BP2b8b:b;b<b=b7,XBEYA9C>aeW2W1p,2tpp,2TPp,3ERRp,2HKGZo"). Qed.

Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
  rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
  fold st' in Hr', SO, STR, FSA.
  (* [comment removed for export] *)
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
  assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
      exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x5d000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - atop_facts. lia.
    - exact (Hc X).
    - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold ras_post2.
  exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
  split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold RCTX in X. atop_facts. lia.
             + destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). atop_facts. lia.
             + destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). atop_facts. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). atop_facts. lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
    - destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
    - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { (* [comment removed for export] *) constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
  split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. exists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.
End CANSEC1.
