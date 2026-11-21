(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (30 recorded proofs replaced by written proofs (rrepfoot_area, rrepfoot_group, rrepfoot_known and 27 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocKit_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_B () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp8fin_mapsBlookup_delete_SomeI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C46Stdlib5Lists4List:firstn_nilC35stdpp4gmapBgmap_partial_alterK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B?rbytes_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B8rrepfootC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B9ivs_avoidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc;MallocKit_B;munch_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B?rrw_cells_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffc59OSSVerify5KrLib5Ubsan<RMallocKit_B<rrepfoot_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7comparec59OSSVerify5KrLib5Ubsan<RMallocKit_B=ru64arr_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B<ru8arr_agreeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B>rrepfoot_mlockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B;rrepfoot_nlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B=rrepfoot_pgszC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B<rrepfoot_gotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B>rrepfoot_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B=rrepfoot_areaC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B>rrepfoot_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib5Ubsan<RMallocKit_B>rrepfoot_knownC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses3injK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_ctx_extC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC47Corelib4Init5Logic6eq_symK46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib6Malloc;MallocKit_B@get_meta_rec_putC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N7eqb_neqC47Corelib4Init5Logic5proj2C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib5Ubsan:RMallocRep=rarea_rep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep>rgroup_rep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep?rshadow_rep_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib5Ubsan:RMallocRepErregions_wf_restaticsC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B?rmrep_set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B<del_slots_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B;actives_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u64arr_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B:usages_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B<bouncess_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr:u8arr_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib7Classes?RelationClasses>iff_TransitiveC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepBrwr_at_bytes_existC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc59OSSVerify5KrLib5Ubsan<RMallocKit_B>rbytes_at_consC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnI47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib5Bytes6le_valC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib3Lib5Bytes<load8_le_valC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z2geK46Stdlib9micromega=RingMicromega3Op204c59OSSVerify5KrLib5Ubsan<RMallocKit_B8rfree_fpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B?rfree_fp_regionC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc;MallocKit_B@outside_of_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTreeErpres_except_of_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B;ivs_coveredC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B>ivs_covered_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_BFrpres_except_of_munch'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B;rctxW_avoidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B>actives_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=usages_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BAunmap_seqs_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B?bouncess_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan<RMallocKit_B@rmrep_ctx_frame'C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition rrepfoot (st : mstate) (a : Z) : Prop :=
  (RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
  \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001ip4p710p8g002@R0p4p70R1p10035p4p710R2p8P1p1003Qp4p710R3p8P1p1003op4p710R4p8P1p1004MR5p4p710R6p8P1P5p4p7210R5p8P1g004fR7p4p710p8P1p1005?R8p4p710p8P1p1005Wp4p710p8P1p1005np4p710p8P1p1006Ep4p710p8P1p1006]R9p4p710p8P1p10074R:p4p710p8P1p1007Pp4p710p8P1p1007ip4p73110R;p8P1g008;R1p4p710R<p8p1008Op4p70R=P2p8P=p1009Dp4p710p8P=p1009bp4p7210p8P=P4p8P=P7p4p741110R2p8P=P1p4p7210p8P=P1p4p73110R>p8P=p100:?p4p7<111111111110p8P3P6p8P3P5p8p100:cR=p4p73101R?p100;=R@p4p73110p8P?p100;VRAp4p73110p8P?p100<2p4p710p8P?p100<ERBp4p7201p8P?p100<Wp4p7201p8P?P>p8P?p100<iR>p4p73110p8P?p100==RCp4p73110p8P?p100=Wp4p7201p8P=p4p710R?P@p4p710p8P?PAp4p710p8P?P6p8P?P5p8P?P<p8P?P>p4p710p8P?PCp4p710p8g00=jRCp4p710R?P3p8P?P6p8P?P5p8P?P;p8PCp4p741110R;P:p4p73101p8p100>>p4p710P4p8P2P=p4p7511100R4p8P4P2p8P8p4p741110R8P=p4p76111100R2p8P2P8p8p100>]p4p741110R8P=p4p771111100R2p8P2P8p8P9p4p741110R9P=p4p7:1111111100R=p8P=P9p8PBp4p7200RBP;p8P;PBp8g00?=j1:Tg00?bj15Tg00@Gj16Tg00@ej2;Tg00ABj29Tg00A^j1>Tg00B@j4ETg00B^j6DTPCj4=TP7j4<Tg00C?j1QTP1j6@Tg00D7j2?Tg00DYj38Tg00E3j2PTg00Ehj2BTg00FDj22Tg00F_j23Tg00G9j1NTg00H2j1MTg00Hlj1LTg00Icj1FTg00JZj1GTg00KPj1HTg00LLj2ITg00MGj2JTg00Mdj2KTg00N^j1CTg00OXj24Tg00P2j3OTf0R1#5#5p=1f2R7f1RC'B/21p=01;C1,97p=719C1,27p=Ag00PLRBg00QER;g00QcR9g00R]R=#:#:#5#:#5#1#1#6,;9R8,9170119C8909Cg00SBR9%1=R8#697C970Cg00T>R9%6=97C970Cg00U?R9%58R=#6R297C970Cg00V9R9%>9P0P9P0g00W0R4g00WNR:P;g00WgR?CER5P4P:g00X@R6P;P?g00X^EDR?P9C=P0P5P?P9C<PCf4R3#QE@1?91381P3CR>f3R<'BRA%5=#1#1#1#1#6,;>7A<'2X39'3X20,30g00Y<R9%>9P0P9P0P5P?P9C=P0P5P?P9C<PC%N3E@1?9138%:8#6,;>9AA<'2X59'3X40,30g00Z3R0%>0P4P0P4P:P6P0C=P4P:P6P0C<P7f5R6#ME@1?0C38g00Zl%LCg00[d38%FCR:%GC#H973:703g00\\1I671J3:'K%C138'2'2'2X8;,3;X60'3X74,34g00]VR4A7C4270Cg00^TR4A7C4270C'4'4'4'4'4'4'4;O1UX0;X1BPCP1O2X0;X1BPCP1O2W0W1o"). Qed.
Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3g00@Gj17Tg00@ej2:Tg00ABj29Tg00?=j1;Tg00?bj16Tg00A^j1=Tg00B@j4FTg00B^j6ETg00=jj4>Tg004fj4<Tg00C?j1RTg008;j6@Tg00D7j2?Tg00DYj38Tg00E3j2QTg00Ehj2BTg00FDj23Tg00F_j21Tg00G9j1PTg00H2j1OTg00Hlj1NTg00Icj1LTg00JZj1KTg00KPj1GTg00LLj2HTg00MGj2ITg00Mdj2JTg00N^j1DTg00OXj24Tg00P2j3MTg00_Tj3CTf0R0#6#6p=2f2R1f1R2'B/30p=01:20,91p=51920,31p=Ag00PLR3g00QER4g00SBR5g00R]R6#2R7#7,:5R8,90700g00QcR9%;6#;#6#;#6#2#2#7952970219289052R5g00T>R8%769528702g00U?R8%67R6#7R99528702g002@R8g00V9R:%=:P8P:P8g00W0R;g00WNR<P4g00WgR=CFR>P;P<g00X@R?P4P=g00X^EER=P:C>P8P>P=P:C<P2f4R@#RE@1?:0381Q@2RAf3RB'BRC%66#2#2#2#2#7,:A7AB'3X3:'1X28'1g00Y<R:%=:P8P:P8P>P=P:C>P8P>P=P:C<P2%P@E@1?:038%;7#7,:A9ACB'3X5:'1X48,18g00Z3R8%=8P;P8P;P<P?P8C>P;P<P?P8C<P1f5R?#OE@1?8238g00Zl%N2g00[d38%L2R<%K2#G95@<70@g00\\1H?11I@<'J%D038'3'3'3X84,14X68'1X7;,1;g00]VR;A52;9702g00^TR;A52;9702'4'4'4'4'4'4R;'4AM5;03CUX04X13P2P0O2X04X13P2P0O2W0W1o"). Qed.
Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3g00@Gj17Tg00@ej2:Tg00ABj29Tg00?=j1;Tg00?bj16Tg00A^j1=Tg00B@j4FTg00B^j6ETg00=jj4>Tg004fj4<Tg00C?j1RTg008;j6@Tg00D7j2?Tg00DYj38Tg00E3j2QTg00Ehj2CTg00FDj22Tg00F_j23Tg00G9j1PTg00H2j1OTg00Hlj1NTg00Icj1LTg00JZj1KTg00KPj1GTg00LLj2HTg00MGj2ITg00Mdj2JTg00N^j1DTg00OXj24Tg00P2j3MTg00_Tj3ATf2R0f1R1'Cf0R2'2p=0%62#6p=11:12,90p=51912,20p=Bg00PLR3g00QER4g00T>R5g00R]R6#7,:5R7,92702g00QcR8%;6#;#6#;#6#1#1#79518701g00SBR8%16R6#79518701R819179051R5g00U?R7%66R9#7R:9517701g002@R7g00V9R;%=;P7P;P7g00W0R<g00WNR=P4g00WgR>CFR?P<P=g00X@R@P4P>g00X^EER>P;C>P7P?P>P;C<P1f4RA#RE@1?;2381QA1RBf3RC'CRD%69#1#1#1#1#7,:B7BC'2X3;'3X27'3g00Y<R;%=;P7P;P7P?P>P;C>P7P?P>P;C<P1%PAE@1?;238%;6#7,:B9BDC'2X5;'3X47,37g00Z3R7%=7P<P7P<P=P@P7C>P<P=P@P7C<P0f5R@#OE@1?7138g00Zl%N1g00[d38%L1R=%K1#G95A=70Ag00\\1H@01IA='J%D238'2'2'2X84,34X67'3X7<,3<g00]VR<A51<:701g00^TR<A51<:701'4'4'4'4'4R<'4R:'4AM5<29A8:3AUX04X13P1P2O2X04X13P1P2O2W0W1o"). Qed.
Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3g00?bj17Tg00@Gj16Tg00@ej29Tg00ABj2;Tg00?=j1:Tg00A^j1>Tg00B@j4FTg00B^j6ETg00=jj4=Tg004fj4<Tg00C?j1RTg008;j6ATg00D7j2@Tg00DYj38Tg00E3j2QTg00Ehj2CTg00FDj21Tg00F_j22Tg00G9j1PTg00H2j1OTg00Hlj1NTg00Icj1LTg00JZj1KTg00KPj1GTg00LLj2HTg00MGj2ITg00Mdj2JTg00N^j1DTg00OXj24Tg00P2j3MTg00_Tj3?Tf0R0#7#7p=3f2R1f1R2'C/10p=01920,;1p=51;20,11p=Bg00PLR3g00QER4g00U?R5g00R]R6#3R7#7R8#6R9,95R:,;0700g00QcR;%:6#:#7#:#7#3#3#6952;702g00SBR;%67952;702R;g00T>R<%66952<702R<1;2:9052R5g002@R:g00V9R6%>6P:P6P:g00W0R=g00WNR>P4g00WgR?CFR@P=P>g00X@RAP4P?g00X^EER?P6C=P:P@P?P6C<P2f4RB#REA1@60381QB2RCf3RD'CRE%78#3#3#3#3#6,9C7BD'1X36'2X2:'2g00Y<R6%>6P:P6P:P@P?P6C=P:P@P?P6C<P2%PBEA1@6038%:7#6,9C9BED'1X56'2X4:,2:g00Z3R:%>:P=P:P=P>PAP:C=P=P>PAP:C<P1f5RA#OEA1@:238g00Zl%N2g00[d38%L2R>%K2#G95B>70Bg00\\1HA11IB>'J%D038'1'1'1X84,24X6:'2X7=,2=g00]VR=A52=9702g00^TR=A52=9702'4'4'4'4R='4R9'4R:'4AM5=09?<99?;:3?UX04X13P2P0O2X04X13P2P0O2W0W1o"). Qed.
Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
Lemma rrepfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> rrepfoot st a.
Proof. intros; do 6 right; left. exists rid, r, v. auto. Qed.
Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3g00?bj18Tg00@Gj17Tg00@ej2:Tg00ABj2<Tg00?=j1;Tg00A^j1?Tg00B@j4FTg00B^j6ETg00=jj4>Tg004fj4=Tg00C?j1RTg008;j6ATg00D7j2@Tg00DYj39Tg00E3j2QTg00Ehj2CTg00FDj25Tg00F_j21Tg00G9j1PTg00H2j1OTg00Hlj1NTg00Icj1LTg00JZj1KTg00KPj1GTg00LLj2HTg00MGj2ITg00Mdj2JTg00N^j1DTg00OXj24Tg00P2j3MTg00_Tj32Tf0R0#8#8p=3f2R1f1R2'C/50p=01:20,<1p=61<20,51p=Bg00PLR3g00QER4g00]VR5g00R]R6#3R7#8R8#7R9,:5R:,<0700g00QcR;%;6#;#8#;#8#3#3#7962;702g00SBR;%77962;702R;g00T>R<%76962<702R<g00U?R6A6269702R6g002@R=g00V9R>%?>P=P>P=g00W0R?g00WNR@P4g00WgRACFRBP?P@g00X@RCP4PAg00X^EERAP>C>P=PBPAP>C=P2f4RD#REA1@>0391QD2REf3RF'CRG%88#3#3#3#3#7,:E7BF'5X3>'1X2='1R>g00Y<R8%?8P=P8P=PBPAP8C>P=PBPAP8C=P2%PDEA1@8039%;7#7,:E9BGF'5X58'1X4=,1=R=g00Z3R8%?8P?P8P?P@PCP8C>P?P@PCP8C=P1f5RC#OEA1@8239g00Zl%N2g00[d39%L2R@%K2#G96D@70Dg00\\1HC11ID@'J%D039'5'5'5X84,14X68'1X7?,1?R?1<2:9052R5g00^TR:A62:9702R:'4R9'4R8'4R@'4RD'4RC'4R1'4AM5:092?992=892>@926D92<C92;132UX04X13P2P0O2X04X13P2P0O2W0W1o"). Qed.
Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;1p;2p;4p;6p;3g00?bj18Tg00@Gj17Tg00@ej2:Tg00ABj2<Tg00?=j1;Tg00A^j1?Tg00B@j4FTg00B^j6ETg00=jj4>Tg004fj4=Tg00C?j1QTg008;j6ATg00D7j2@Tg00DYj39Tg00E3j2PTg00Ehj2CTg00FDj25Tg00F_j22Tg00G9j1OTg00H2j1NTg00Hlj1MTg00Icj1LTg00JZj1KTg00KPj1GTg00LLj2HTg00MGj2ITg00Mdj2JTg00N^j1DTg00OXj24Tg00_Tj30Tf0R0#8#8p=3f2R1f1R2'C/50p=11:20,<1p=61<20,51p=Bg00PLR3g00QER4g00^TR5g00R]R6#3R7#8R8#7R9,:5R:,<0710g00QcR;%;6#;#8#;#8#3#3#7962;712g00SBR;%77962;712R;g00T>R<%76962<712R<g00U?R6A6269712R6g002@R=g00V9R>%?>P=P>P=g00W0R?g00WNR@P4g00WgRACFRBP?P@g00X@RCP4PAg00X^EERAP>C>P=PBPAP>C=P2f4RD#QEA1@>0391PD2REf3RF'CRG%88#3#3#3#3#7,:E7BF'5X3>'2X2='2R>g00Y<R8%?8P=P8P=PBPAP8C>P=PBPAP8C=P2%ODEA1@8039%;7#7,:E9BGF'5X58'2X4=,2=R=g00Z3R8%?8P?P8P?P@PCP8C>P?P@PCP8C=P1f5RC#NEA1@8239g00Zl%M2g00[d39%L2R@%K2#G96D@71Dg00\\1HC11ID@'J%D039'5'5'5X84,24X68'2X7?,2?R?g00]VR8A6289712R81<2:9152R5'4R:'4R9'4R@'4RD'4RC'4R1'4A085090?:90=990>@906D90<C90;130UX04X13P2P0O2X04X13P2P0O2W0W1o"). Qed.

Lemma rbytes_at_agree : forall m m' A bs,
  bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rrw_cells_agree : forall m m' A cs,
  rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono usegs m m' -> rw_cells usegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_transport; eauto.
Qed.

Lemma ru64arr_agree : forall m m' A ws,
  u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono usegs m m' -> u64arr usegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
  eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

Lemma ru8arr_agree : forall m m' A bs,
  u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono usegs m m' -> u8arr usegs m' A bs.
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_unowned : forall st m m' W,
  rmrep st m -> munch W m m' -> wmono usegs m m' -> ivs_avoid W (rrepfoot st) -> rmrep st m'.
Proof.
  intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (TC : forall A cs, rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells usegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound usegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound usegs m _ _ C2) as B2. pose proof (u64arr_bound usegs m _ _ C3) as B3.
    pose proof (u8arr_bound usegs m _ _ C4) as B4. pose proof (u8arr_bound usegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      pose proof Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma rmrep_put_meta_frame : forall st m m' g mr',
  rmrep st m -> meta_slot st g ->
  munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st g) (meta_cells st mr') ->
  rmrep (put_meta g mr' st) m'.
Proof.
  intros st m m' g mr' MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
  pose proof (round_up_pg_ge (r_len ra)) as RU.
  (* [comment removed for export] *)
  assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
  assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  assert (TC : forall A cs, rw_cells usegs m A cs ->
            (A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells usegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. unfold RCTX in *.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | cbn; lia].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
    + apply TC; [exact C6 | cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros a' ar' Ha'. cbn in Ha'.
    destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    destruct (decide (a' = a)) as [->|NEa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'.
      destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
      split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k' Hk'. rewrite Hmc, get_meta_rec_put.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
      * apply TC; [exact PD| cbn; lia].
    + assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
      destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
      * apply TC; [exact PD| cbn; lia].
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
    destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
    destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [|exact I].
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
    rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_ctx_frame' : forall st st' m m',
  rmrep st m -> munch [(RCTX, RCTX + 928)] m m' -> wmono usegs m m' ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_statics st' = s_statics st ->
  rmrep_ctx st' m' -> rmrep st' m'.
Proof.
  intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
  assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
  assert (TC : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells usegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  unfold RCTX in *.
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - exact (rregions_wf_restatics _ _ ER EA EG ERs WF).
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
    destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len ra)).
    destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
    + apply TC; [exact A1| cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
    + apply TC; [exact A3| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len rb)).
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
    destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof.
  intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
    eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof.
  intros st m v (WF & CX & GL & AR & GR & SH).
  assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 80 + 8 * sc) ->
  ov_read_bytes usegs m a 8 = Some (le8 (pw st (active st sc))).
Proof.
  intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
  eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 464 + 8 * sc) ->
  ov_read_bytes usegs m a 8 = Some (le8 (wz (usage st sc))).
Proof.
  intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
  eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa (RCTX + 880 + i) ->
  ov_read_bytes usegs m a 1 = Some [b8 (bounces st i)].
Proof.
  intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
  eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.

Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa (RCTX + 912) ->
  ov_read_bytes usegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof.
  intros st m a (_ & (_ & _ & _ & _ & _ & C6) & _) ->.
  apply (rw_cells_read_at usegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.

Lemma rmrep_fmh_read : forall st m a, rmrep st m -> a = wa (RCTX + 16) ->
  ov_read_bytes usegs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof.
  intros st m a (_ & (C1 & _) & _) ->.
  apply (rw_cells_read_at usegs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rbytes_at_cons : forall m a b bs, bytes_at usegs m a (b :: bs) <-> bytes_at usegs m a [b] /\ bytes_at usegs m (a + 1) bs.
Proof.
  intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app usegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.

Lemma rmrep_group_word8 : forall st m b gh,
  rmrep st m -> (s_groups st) !! b = Some gh ->
  exists bs : list byte, ov_read_bytes usegs m (wa (conc st b + 8)) 8 = Some bs /\ length bs = 8%nat
                   /\ (bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs))) mod 32 = g_active_idx gh.
Proof.
  intros st m b gh MR Hb. pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
  destruct (GR b gh Hb) as (w8 & R & Hw8).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof WF as (_ & WR & _). destruct (WR (fst b) r Hr) as (_ & _ & _ & RC2 & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  atop_facts. pose proof (round_up_pg_ge (r_len r)).
  destruct (rwr_at_bytes_exist m (conc st b + 9) 7) as (bs & Lbs & Bbs).
  { eapply wr_at_sub; [exact HWr| rewrite Cb; lia | rewrite Cb; lia]. }
  { lia. }
  { rewrite Cb. lia. }
  assert (B8 : bytes_at usegs m (conc st b + 8) [w8]).
  { destruct R as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
    apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
    replace (conc st b + Z.of_nat 8) with (conc st b + 8) in HB by lia.
    first [ apply bytes_at_app in HB; destruct HB as [HB _]; exact HB | exact HB ]. }
  assert (B : bytes_at usegs m (conc st b + 8) (w8 :: bs)).
  { apply rbytes_at_cons. split; [exact B8|]. replace (conc st b + 8 + 1) with (conc st b + 9) by lia. exact Bbs. }
  exists (w8 :: bs).
  assert (L8 : length (w8 :: bs) = 8%nat) by (cbn; lia).
  split; [|split; [exact L8|]].
  - rewrite <- (Z.add_0_r (conc st b + 8)). rewrite (bytes_at_read usegs m _ _ 0 8 B); [|lia|rewrite L8; cbn; lia].
    cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite L8; lia). reflexivity.
  - rewrite load8_le_val by exact L8. cbn [map le_val]. rewrite <- Hw8.
    change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
    set (L := le_val (map bv_unsigned bs)). replace (256 * L) with ((8 * L) * 32) by lia.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmeta_slot_bounds : forall st m g, rmrep st m -> meta_slot st g ->
  0 < conc st g /\ conc st g + 40 <= ATOP /\ (conc st g + 40 <= 0x10000 \/ 0x5d000 <= conc st g) /\ conc st g mod 4 = 0
  /\ conc st g mod 4096 >= 24.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "p'0h01Hh11rh24__x1h34__x2h44__x3h54__x4h64__x5h72arh82H1h92H7h:4__p1h;4__x6h<4__x7h=4__x8h>1ah?1kh@7__arithhA4__ffhB8__varmaphC5__withD3H13hE4__x9hF1bhG2ghhH2r1hI2r2hJ3ridhK4rid1hL4rid2hM2H0hN3H10hO3H11hP2H2hQ2H3hR2H4hS2H5hT2H6hU2H8hV2H9hW2_HhX6__sat3hY6__sat4hZ1zh[3H12h\3H14h]3H15h^3H16h_3H17h`3_H0ha6__sat2hb2a0hc1ghd5ATOPRhe2Cahf2D1hg2D2hh2Eghi2HGhj2Hahk2Hkhl3Hrahm2MRhn2NKho3RB0hp4RBALhq3RBChr2RFhs3Sa0ht3Sa1hu3SaLhv2WFhw2WRhx3_H1hy3_H2hz1eh{1mh|1oh}2rah~2sti001xp%0p&0p&1p;1p;3p;2p;4p;6p;7p;8g00?bj15Tg00`ck10eTg00aAk10aTg00A^k10MTg01O;k30iTg02eMk21@Tg00B@k416Tg00B^k612Tg00=jk40RTg004fk40PTg02Dcj2]Tg00F_R0j2vTg00E3j26Tg00?=j1DTg00@ej20Tg01ZQk113Tg00@Gj1aTg00C?j1uTg01P6k20OTg01Q7k30[Tg01R6k20rTg01S9k30pTg01T:k20nTg01U<k20mTg01Y3k20lTg00H2j1KTg00Icj11Tg00JZj1GTg00KPj1OTg00DYj37Tg01\Cj1bTg01\\k10WTg01]Wk218Tg00FDR1j23Tg00G9k10FTg00D7k20UTg02fLk611Tg01Z1j22Tg00Ehj2;Tg00Hlk101Tg02h`k30}Tg00hdk20>Tg02gLk20{Tg00`Ik40zTg003ok60=Tg02gak40yTg01_mk10xTg02ihk10vTg01G>j2oTg01G[j1@Tg02L2k20<Tg02KIk20\Tg00jJk10tTg00adk10sTg00kfk11UTg00lDk11TTg00lok20qTg00mRk20oTg00n`k11STg010Ik21RTg010kk21QTg011Wk31LTg0126k41KTg00ABj2ATg02kek30jk20LTg02lVk200Tg034=j2>Tg02m7k209Tg02m^k208Tg02nEk207Tg02nkj2}Tg02oQk203Tg027Zk20hTg033>k11FTg033\k21ETg01`kk11DTg00n5k406Tg04@Tk20VTg00_nk40HTg008;k60BTg00OXk20GTg01[Gk30fTg01^7k31?Tg01^Tk31>Tg02L[k31ATg02^4j3_Tg02MDk21=Tg02N0k30ZTg00jjk21<Tg00kHk41;Tg013Mk70JTg02\8k61:Tg00oek71HTg00oBk31ITg01Hok31JTg0141k80XTg03LMk31NTg03=Wk217Tg03M6k61OTg03Kik71PTf0R2#5#5p>0Kg002@R3g00V9R4f3R5f2R6f1R7%u2J0Bp=|20U42p>02g014UR8/;61A72'3p=?g02cg/o2p=yg02_A/02p=xA7372,36p=lA7567/32p=\%52#5#5#ap=f%52#5#5#5p>0T%D2#Dp>10%D2#5p>0S%52#5#5#5#5#5#5#5p=c%52#ap>0|g00QER9f4R:/25;78126700V2'3p=9f7R;,A8f6R<f5R=';1;:51;67+0G/32'3'3p=:P3P4P:P5P6P7J0B=7=2p>0`1;82p=81A72,36p>0D1]729736p>0]1372,36p=<g00Z3R>00U2p>0:g00W0R?P>P:P5P6P7J0B=7=2p==1A82p=L1272=798p=U1067/;2p=Fg02`lR@@0f72p>1Cg01:bRAg01;BRB772,37p>1B1;87/32p=i%G2#Op=I%G7#O,06/;2p=Q1;6700G2p>19P<P=P:P5P6P7J0B=7;2p=gB1??92p=dB1>?92p=4g00ZlRC&012g00[dRD37p>151;72,36p>141267=798/32p>051v>2p=Y1056/;7/32p=eP?P>P5P6P7P2J0Bp>0E1667=792p=W10=:/;51267=798/32'3p=X&017=7CD#b/32p>0~&015=7CD#b1A86A7978/32'3'3p=p%17/02p>0d1A851267=798/32'3p>0@1256=798&017=7CD#b/32'3p>0cA7C2D#bp>0bB0f@72=7ABp=^%52#Dp>0?1;561;72+0Gp=V1;:51;67+0G/32p=T%O2,07p>0QA7972p=s%D2#D#D#Dp=q1;67/32p>0w1o72,06p>0_1072,06p>0u126700V2p>0^20\92p=EB1A972p=`A_9729_96p>0;A_972g02da+1=p=hg018hR@@0Z72p>0N21<92p=jP9P6P7P2H1;p=JP9P7g01:;P2H06p={P7g0164RDg016SRCPCg0173REP2g017SRFK0Jp>0420o92p=PP6PDPCPCPEP9P7g019TRGP2H06PFK0Jp=BP7PDPCPCPEP2J1:p>0YP6PDPCPCPEP7P2K1Hp=nB1I972p=C20q92p=SB1J972p=zP:PDPCPCPEP5P6P7PDPCPCPEP2PFK0JL0Xp=[P<PDPCPCPEP=P:P5PDPCPCPEP6P7P2L0XL0Xp=HA7A2Bp>1M1067/02p>0kP9P7PGP2H06p>1GA7928p=R1o67/029795p=m1;28p=~B1N972p=NA_972p=wA_9729_969_959_9:p=rA_9670172p=ZB0Z@72:0Z@6p=kP6PDPCPCPEP9P7g01MbRGP2H06PFK0Jp>0CP7PDPCPCPEP2J1Op>0gP9P7PGP2H06p=tP6PDPCPCPEP7P2K1Pp>0A10729796p>0I10:51o72,06'0p=Mg00PLg00R]RD#5RG#5RF#5RH#5RI$0KRJ$0e$0a&0eH$0a$0M[p,2rcRK@0i6721@57P0P3&0M4RLP3P?g00WNRMP9g00WgRNH16ROP?PMg00X@RPP9PNg00X^J12RNP4H0RRQP3POPNP4H0PRRP6P;C|&027RSg02c0RT9?22RU%y2#xRV,]6RW7l=C\X?9,v9X74,v4X>316=5RX%DGRY#fRZ,0XR[&13KR\P[&0KJ$0TRJ#5#fR[%5D$10$0S$0S#c#fR]PXPX%aFR^PX%aJRJ%DDRX#5S00#5R_$0|R`D9G:P2PLPQPRP6f9RaC|PSAlU;WC\X?9,v9X74,v4P0P4PLPQPRP5f:RWC|PSf8Rb1]5V5lUC\X?9,v9X7416a;Rc10cZRdP\PdP[P]PcPcP^PcPJP`D9G:P2PLPQPRP=f<RcC|PS1]=V9lUWC\X?9,v9P0P9PLPQPRP<f=RSC|&026f;Rd1]<V5lUC\X?916SdRe10eZRfP\PfP[P]PePeP^PePJP`D9G:P2PLPQPRPbf?ReC|&02:1]bV9lUSC\P1PLPQPRPaf@RU#u&02=J0`A?77Tf>S01%y7#x,]a3lfARV/6eRf10fZRgP\PgP[P]PfPfP^PfPJP`D9G:P2PLPQPRPdfBS02#u&02;J0`%8:S03@0D:T%y:#x,]c7lVP1A?==TQ02%y=#x80]SfERffCS04'6Rg10gZRhP\PhP[P]PgPgP^PgPJP`D9G:P2A?;;T%yb#x:0]fUPffHRTfGS0560iKP1fIRg-0OKB0[KgT20rKTB0pKgT20ngT20mgT3<3<fJS06/6TRh10hZRiP\PiP[P]PhPhP^PhPJP`D9G:P2fKRh-0OKfLRi>0[Kh20rKhB0pKih20nih20mih3<3<P7fMRj-0OKP1fN-0lK&0M>RkP?PMPPP>H0RRlP?PMPPP>H0PRPP7fPRM#K&0:2RmE=%17Rn#LS071UnJS08%G7Ro%OoS09=Fn\S0:Q09-1Cn+1B'i3<S0;[^1>^J?PkPlPPP5fRRo#KRp&0:6S0<E=PkPlPPP6fSRq#KRr&0:7RsE=A7?=5#b%1=Rt%I=S0='0S0>&0W5%15&0W=7Q5419[S0?[[^I>^L?^H>^K?218?9RuPLPuP4PQPRP7%uM&022S0@GgPkPlPP%d5S0APpPmE=Rp%45Rv#8Rw%I2Rx9FvJ&152Ry#bS0B&0W2%12Rz/0v414:05vJ3<R{'3X1>#Y[^74]>g00Y<R|&0M|S0CPuP|P3POPNP|H0RS0DP3POPNP|H0PS0EP7&0FM20U|2RNGgPv%aIS0FPxQ0F,UvCe9<ywRy,3pX1>#Y[]G^Fu'33<fORp/6jRw10wZRvP\PvP[P]PwPwP^PwPJP`D9G:P220lKMPkPlPPP7PrPmE=Q0;[^1>^J?PkPlPPP5fURr#KRwQ0<E=PkPlPPP6fVRv#KRIPsE=Q0?[[^I>^L?^H>^K?PLPuP4PQPRP7%uqQ0@GgPkPlPPQ0APwPmE=Rw/3{X1>#Y[^74^>uQ0CPuP|Q0DQ0EP7&0FqPNGg13wyX1>#Y[^G|^Fu'33<P1PkPlPPP7fTRw#KPmE=Q0;[^1>^J?PkPlPPP5PIQ0<E=PkPlPPP6fWRO#KS0GPsE=Q0?[[^I>^L?^H>^K?PLPuP4PQPRP7%uwQ0@GgPkPlPPQ0APIPmE=R}/3{X1>#Y[^74^>uQ0CPuP|Q0DQ0EP7&0FwPNGg13}yX1>#Y[^G|^Fu3<fQR},6qR~10~ZS0HP\Q0HP[P]P~P~P^P~PJP`D9G:P2PkPlPPP7PIPmE=Q0;[^1>^J?PkPlPPP5fYRI#KS0;Q0<E=PkPlPPP6fZR~#KS0<PsE=Q0?[[^I>^L?^H>^K?PLPuP4PQPRP7%uOQ0@GgPkPlPPQ0AQ0;PmE=RR/3{X1>#Y[^74^>uQ0CPuP|Q0DQ0EP7&0FOPNGg13RyX1>#Y[^G|^Fu3<PKPvPpPhPWQ04J11PkPlPP%dMQ0GH0EPm%4MRu,0z9WOM%8uPuPJPxPuPJQ0B%LzAFzx\:05zJ3<RuEX3<C\X1>#YP0P>PkPlPP%d}fXR0#KH0EPm%4}R|,0z9W0}%8|P|PJPxP|PJPuEX3<C\X1>160vR|10|ZRRP\PRP[P]P|P|P^P|PJP`D9G:P2PkPlPP%dqQ0<H0EPm%4qR|,0z9W~q%8|P|PJPxP|PJPuEX3<C\P1PkPlPP%dwf[Ru#KPsE=%4wRs,0n9Wuw%8sPsPJQ09PsPJQ07Q08Q0:3<-0~7EX3<f\Rs/6~Rn10nZR|P\P|P[P]PnPnP^PnPJP`D9G:P2PkPlPP%dvf]Rn#K&0:5E=f^R|%1:Rx%4ORq'07WO%8qPqPJ%I:ROPqPJP:Px12xJAFxO\CpEX3<P1f_RO%40Rx,0t7W0PxPJQ0=PxPJP=Pt12tJQ0>/;\CpEX,ixf`Rx/6|Rt10tZRqP\PqP[P]PtPtP^PtPJP`D9G:P2faRt%4~-0d;7W~%4uRqPqPJ%IbRzPqPJPb%1bRq12qJAFqz\CpEX'iP1%4sRq#8PqPJ%IaRzPqPJPa%1aRq12qJAFqz\CpEXfdRqfbRz'6RR10RZRyP\PyP[P]PRPRP^PRPJP`D9G:P2%4|#8%4ORRPJ%IcRyPRPJPc%1cRR12RJAFRy\CpEXP1%4xRR%ISRy7FJPRPJPS%1SRSPSPJAFSy\H0@H0cfhRSffRy'6RR10RZRNP\PNP[P]PRPRP^PRPJP`D9G:P2%4z%Ie7FJfcRR#4PJPU%1URNPNPJAQNU\H0@H0cP1%4q/UJPV%1VRq12qJAQqV\CpflRqfjRV'6RN10NZRUP\PUP[P]PNPNP^PNPJP`D9G:P2%4y/UJfDRN%1NRU12UJAQUN\CpP1&01f$0b%1fRUPUPJAQUf\H0@fpRUfnR{'6RQ10QZRLP\PLP[P]PQPQP^PQPJP`D9G:P2Q05$01$0b%1TRQPQPJAQQT\H0@P1%1gRQ#LAQQg\:05QJftS05frS0>'6RQ10QZRgP\PgP[P]PQPQP^PQPJP`D9G:P2%1h#L%1iRhAQhi\805JP1%1jRh/UJAQhj\fxS0=fvS0:'6Rh10hZRiP\PiP[P]PhPhP^PhPJP`D9G:P2%1p/UJ%1M?QM\PvQ05#dP}PjO3%1}RjPjPJ%G}R}Pj%O}R}P\1^j}Ce'iH0@P1%1oR}#L%GoRoP}%OoRoP\1^}oCe'i:05}Jf}f{S08'6R}10}ZRoP\PoP[P]P}P}P^P}PJP`D9G:P2%1w#L%1rRw%GrRrPw%OrRrP\1^wrCe'i805JP1%1vRr/UJ%GvRvPr%OvRvP\1^rvCe'ip+01BS07p+01@S09'6Rv10vZRrP\PrP[P]PvPvP^PvPJP`D9G:P2%10/UJ%GIR0%1IRI%O0R0P\1^I0Ce'iP1%G~R0#8%1~R~%O0R0P\1^~0Cep+01FR0p+01DS0<'6R~10~ZRIP\PIP[P]P~P~P^P~PJP`D9G:P2%Gs#8%1nRs%InRnP\1^snCeP1%1|Rn%I|Rs;F\1^nsp+01JS0Bp+01HS0G'6Rs10sZRnP\PnP[P]PsPsP^PsPJP`D9G:P2%1x?Qx\%1t%It'^%1zRt%IzRx<0}210txRxP[%DF$0K#c#fRsPtPxPs&0?D$0?$0K#c#fRnPtPxPn&0?D$0?$0S#c#fR~PtPxP~P]PtCVDTDTDTP1%1RR1%GR+0QRtP[PsP1CVPtPsPnP1PtPnP~P1PtP~P]P1CVDTDTp+01OS04p+01MS0E'6R1101ZRtP\PtP[P]P1P1P^P1PJP`D9G:P2feR1#1Rt%G1+0QP[PsPtCV%1yRt%Gy+0QRyPsPnPtPyPnP~PtPyP~P]PtCVDTDTP3p+01KRtp+01C#y#xRy']R1p+01SRxp+01LS0D,6xQ0<#y#x'0RI7W2Xc3P9p+01RRv/6t/0yRr1s2IXZ920>9r16v1PvPtPyPkfgS0C$0:Ry20{>2X|kP>&0:S=7kmZ00>Q0C20>kyH0zPlPP%dt%KvH0EPRJ0=H0yJ0=p+01PRPfyRlJ0=AWvPr&0xK%DXS0;#q#q#qRK#5#q#q$0T#c#c#f%DK#q#q$0T#c#c#f,;\80w\fi#GRK$0v%OK,;KP9p+01US0Ap+01NS0@'6S0?B0_`Z0R0'0%L2RK102ZRr/;\PrP[P]P2P2P^P2PJP`D9DT3<XZ9P9Q0@#4Rr-0dVRVp+01GRy,oZ:0u2`Rk10kZRmP\PmP[P]PkPkP^PkPJP`D9G:XZ910V0RV#L10VZR0/;\RkP0P[P]PVCVR01UV^S0HB0^VJ`S0I'3Rm'3RS'3p-0R1g01MCRI#@Rw#@R}#@Ro#ES0J%E}R}20<9ZS0K%EwRw'`20\9IRI40;'h&0t@Rj+0NRM&0s@S0L%j6%j5R@7J7&1U9S0M&1T9Rh20q98Ri20o9DRQ'{-04hS0N&1SCRCPh%PGRG9BhiS0OPCPh%PXRX9BhiS0P20Yh=5nhPCPh1CQG%S`S0Q%SZS0R/zX'C'CRg,{iD[FH21RhES0SP2P620>AB21Q26$1MdB1L987H1KS0TbAbBbCX29X39X49W:%86S0UQ03/3=B0_`Z=S03:0k5:RB#L[[\K^29^39^49^:1P2%D_$0?#aRK,AyPyQ04#4RAfkS0V#1REPpPOf~RpO7b@PkPSPMQ0L%j:S0W%j=S0X7J6?J7@Q0MPhQ00#PR@,CQ%PFRF5BhPCPh%SJRM,CGS0Y=Bh@PCPh20Yh;%SKS0Z,{X-04hS0[5nhPCPhQ0R,CgS0\01GFD[FHQ0SQ0TbAbBbCX29X39X49X59X69X:1AF2:5AF6J=B0D;:KAFBZ<[[[^29^39^49^59^69^:1P2%8yQ0V#IP\PyPAPEQ06PuPpO9b@P0PmB0jrJ|%8JRr12AJ#8[20LEJ%8Efm#1RE/2JR|#8\r[%1qRq000J%RJRm#bR0PEPJ1>EJP|Cm[209EJ%LJR|%1{S06/2JR{#8S0]@0D{J[Q06008J1AJ8R{foS0^#1S0_/2JRp,AJ%~p'3[Q0_007J%1US0`/>J#R\mQ0`/}Jfq#1RU/2J/sU\mg03N8Rp203UJRyePyp+01V#4S0a000Jp+01WS0b#4RyPJ1>yJ12yJCm\0209yJp+01X#4Ry/2JRB??BJ\|208yJp+01Y#4Ry/2JRB,AJ%~B'3\{207yJp+01Z#4Ry/>J#R\m1}yJp+01[S0c#4Ry/2J/sy\mPp203yJRyePyP:g02bJS0d20h8J+0>P|eS0eO1S0fp+01\#4S0g/2JRy??yJPdQ0eO1S0h%1l/2JRl??lJ&1FD-1E9RD%@oRo#@Rl#@Ry#@S0i#@RB#@S0j#@RX#@RS#@Rk#@RT#@RL#ES0k'NS0l%ETS0m,ND%EBRB,NDS0n%EyRy,ND/wI40;%aY-0<9S0o%EoRo'`S0p20<9J/`IS0q%@LRL#@#E%ELRL%EkRk%EXRX1wByS0rDr'h5ZI3ZRT%ESRS%ElS0s/woRl'w,hkR?Q0kQ0m1wyw80;B%aH-0<9/`I1NDLQ0lPXQ0j#ERL,NDS0jQ0i#ES0i,NDS0lQ0KQ0J'`80;yDr'h3Z1wLl,hkS0kQ0k1wXl,hS;kj9kTT3k9kTT9k??9kTT7k?7kTQ0L&1D9RT%jbS0k7JbQ0X7J6Q0W%j;S0t?J<T7J57J7Q0MPhPhB0ChMi-0ghR?PCPh%P_S0W,zMS0u/C@,tGD[PCPhPhP?PCPh%DY#P,zMQ0;#PR_'C,tQD[PCPh%PYRY,CQRl%SsS0v5Bh%SnS0w=BhQ60AhQ0w9Bhl%S~S0w=BhQ60AhQ0w9Bhl%S]S0w=BhQ60Ah5nh5nhPCPh%S[S0x9BhlQ0v=BhQ60AhPCPhB0Ch_iS0vPCPhQ0NPCPhB0Ch@iPCPhQ0Y=BhYPCPhQ0OPCPhQ0PQ0[5nhPCQ0\Q0x5BhQ0w=Bhg60AhFHFHFHFHFHQ0SQ0TbAbBbCX29X39X49X59X69X;9X<9X=9g03PbS0w\mRg1oJbR@>0I6=[B0I6@;\g106=R@PsPnP6P@PnP~P6P@P~P]P6CVDTDT105<P[PsP5CV%RaRs%L=%RWR~AFbJW%8aA?ddKPWPdP`PZPcDMRc/0ZP[P]PcCV[[[[[[[[[[^29^39^49^59^69^;9^<9^=9P2p+01_Rc#4R@/>JQ08#1Rn/>J12nJ12@JRlQ08#IQ0bP@PnPbQ01PNPfPuPOQ0CQ0VQ0^Q04OBb@b8b9Q0=#1RuQ0gP`PZp+01TRNDMRn/0ZP[P]PnCVebObNbVbUb9bTbSbRbQbPb8bMbXbYQ0HQ0I20LV^%8VS0I%8^Pq%4PRPP`PZQ0GDMRn/2^#8[[B0jAJOS0G12PJ#8\rS0H20LqJS0g%8qQ0]\r[S0]PEp+01QS0=#4P`PZp+01IDMRE000^%R^Rq#bQ06%4vP`PZQ0BDMRvP^1>v^12v^Cm[209v^%L^S0BQ0_%4xP`PZPtDMRt/2^RP??P^[208t^1A^8Q0`%4NP`PZQ0DDMRN/2^RP,A^%~P'3[207N^PUQ0A#4P`PZQ0EDMRU/>^#R\q1}U^Q0>#1Q0aP`PZQ0@DMRP/2^/sP\qPp203P^RAePAfs#1000JS0@Q05#1RAPJ1>AJ12AJCm\0S05209AJS0afu#1RA/2JRO??OJ\|S0>208AJS0EQ0:#1RA/2JRO,AJ%~O'3\{S0:207AJS0Dfw#1RA/>J#R\mS0`1}AJS0_12uJ/su\mS06Pp203uJRueS04Pup+01]RA#4000JS0Vp+01^#4ROPJ1>OJ12OJCm\0S01209OJS08A?llJ\|S0x208@JS0\p+01`#4R@/2JRl,AJ%~l'3\{S0[207@JS0Pp+01a#4R@/>J#R\mS0Y1}@JS0Np+01b#4R@/2J/s@\mS0yPp203@JR@eS0zP@Q0fp+01c#4Rl/2JRO??OJS0{Q0hp+01A#1/2JRO??OJS0|Q02Q0d20h8^+0>Q0BeO1Q07#1p+01e#4P`PZPADMRA/2^R8??8^Q0nQ0lQ0sPoQ0J,NDS0J1NDwDrPBQ0s,NDS0sPoP}PwDr1hwI5ZL3Z00NjQ0L%j<Q0t7J5%ja9JTa7J6Q0k9JT:Q0X7Ja7J7S0XQ0MPhPhP?PCPhQ0;#5#P,zM/C_,tYD[S0;PCPhPhP?PCPhQ00#D#P,zM%PHRH'C,tFD[RMPCPhABhiQR_%S^RT,{Q-04h5nhPCPhPhB0ChTi-0ghPCPh1CFYQ0QQ0R/zG'C'CRYQ0W,zT/CQ'tD[PCPhB0ChHiRHPCPh1{iF-04hRFPCPhQ0vPCPh1tQiD[FHFHFHQ0SQ0TbAbBbCX29X39X49X59X69X;9X<9X=9XE91oJaRi>0I:=\gR=B0I:i;\gRiQ0U@0D6^Q0w\qQ03:0k<;R<P^PWP:Cm[%L;Rq%R;\~[\s[[[[^29^39^49^59^69^;9^<9^=9^E9P2p+01g#4R;/>JRTQ0<#1R5/>JRoP5P;P`PZPcDMRB/>^125JR812;JROP;P5Pc12B^PaPeP7PfPRQ0CQ0^O@b@b8b9bDQ09#1PlP`PZQ0cDMRl/U^eb_b^b]b\bDb[bObNbVbUb9bTbSbRbQbPb8bMbabXbY20LVJQ0I12nJ#8\r[Q0GQ0HQ0gQ0]200EJPvPJ1>vJ12vJCm\0209vJ12tJRv??vJ\|208tJ12NJRt,AJ%~t'3\{207NJ1>UJ#R\m1}UJ12PJ/sP\mPp203PJRPePPQ0@Q05Q0aQ0>Q0EQ0:Q0DQ0`Q0_Q06Q04PuQ0VQ01Q08Q0xQ0\Q0[Q0PQ0YQ0NQ0yQ0zP@Q0fQ0{Q0hQ0|Q02Q0eO112AJRA??AJQ0jQ0nPyQ0sQ0JPIDrQ0o/`}Q0pQ0qPkPSPXQ0jQ0rDrQ0F-0<9/`}Q0K/`IQ0mPkPS1NDXQ0i80;LDr'h3Z5Zw5ZI3Z00NjQ0LQ0XQ0MPhQ0;PCPhPMPCPh20Yhd9nh_PCPhPhP?PCPhQ0u/CQ,tYD[PCPhPHPCPhPFPCPhQ0vPCPhQ0OQ0Z,{G-04h5nhPCP9PQg04A0Q0QH06-04hFHFHFHFHQ0SQ0TbAbBbCX29X39X49X59X69X;9X<9X=9XE9X:1Q0U/3dP<PJPWP:Cm\gA?bbK20Vb`[\~\q\s[[\i\=^29^39^49^59^69^;9^<9^=9^E9^:1P212BJR1/AJPTPo1>BJP8POP;P5PcP1PaPeP7PfPRQ0CQ0^Q0bOBb@b8b9bDB0^lJ`eb_b^b]b\bDb[bObNbVbUb9bTbSbRbQbPb8bMbabXbYH0HH0HH0HH0HQ0?PzJ0=Q0A/6xP6J0=b0bdQ0=,6xRx10xZRZP\PZP[P]PxPxP^PxPJP`D9G:ebiWgWfP7P2O2n2001000000121000000bbWrWyP7P2O2n2001000000121000000W0WxP7P2O2n2001000000121000000W0W`P7P2O2n2001000000121000000W0WWP7P2O2n2001000000121000000bbWqWpP7P2O2n2001000000121000000W0WoP7P2O2n2001000000121000000W0WnP7P2O2n2001000000121000000W0WuP7P2O2n2001000000121000000W0WtP7P2O2n2001000000121000000W0WsP7P2O2n2001000000121000000W0WeP7P2O2n2001000000121000000W0WlP7P2O2n2001000000121000000W0X}>P7P2O2n2001000000121100000bzW`WwP7P2O2n2011000000121000000W0WWP7P2O2n2011000000121000000b0WWWvP7P2O2n2001000000121000000b0WhWkP7P2O2n2001000000121000000W0WjP7P2O2n2001000000121000000W0X?9P7P2O2n2001000000121100000W0X74P7P2O2n2001000000121100000W0X>3P7P2O2n2001000000121100000W0WmXc3W{W~o"). Qed.

Lemma rgroup_bounds : forall st m b gh, rmrep st m -> (s_groups st) !! b = Some gh ->
  0 <= conc st b /\ conc st b + 16 <= ATOP /\ (conc st b + 16 <= 0x10000 \/ 0x5d000 <= conc st b) /\ conc st b mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_B ()) ["CANSEC1"] "p'0h01rh11Hh24__x1h34__x2h44__x3h54__x4h61ah71bh82ghh92H1h:2H7h;7__arithh<4__ffh=8__varmaph>5__with?4__x5h@4__x6hA4__x7hB2arhC2r1hD2r2hE3ridhF4rid1hG4rid2hH2_HhI2H0hJ3H10hK3H11hL3H13hM2H2hN2H3hO2H4hP2H5hQ2H6hR2H8hS2H9hT3_H0hU6__sat3hV6__sat4hW4__x8hX5ATOPRhY2CbhZ2D1h[2D2h\3H12h]3H14h^3H15h_3H16h`3H17ha2Hbhb2Hrhc2Krhd2MRhe3RALhf3RB0hg3RBChh2RFhi3Sb0hj3Sb1hk3SbAhl2WFhm2WRhn3_H1ho6__sat2hp1ehq1mhr2sths1zi001xp%0p&0p&1p;1p;3p;4p;6p;2p;7p;8g00?bj15Tg00`ck10LTg00aAk10FTg00A^k100Tg01O;k30STg00B@k40nTg00B^k60lTg00=jk40<Tg004fk40;Tg00G9j1vTg00D7j2dTg01P6k20DTg01Q7k30VTg01R6k20TTg01S9k30PTg01T:k20WTg01U<k20NTg00E3j29Tg00@Gj1XTg00@ej21Tg01ZQk10jTg00?=j1?Tg01Y3k20GTg00H2j1HTg00Icj10Tg00JZj1GTg00KPj1RTg00DYj3ATg01\Ck106Tg01\\k10BTg01]Wk20yTg00C?k105Tg00Hlj1aTg00FDR0j23Tg03F>k60mTg00Ehj28Tg02h`k30kTg01_mk10iTg02ihk10gTg01G[j1DTg02KIk20KTg00jJk10fTg00adk10dTg01`kk10cTg00kfk10bTg00lDk10aTg00lok20JTg00mRk20ITg00n`k10`Tg010Ik20_Tg00hdk209Tg010kk20^Tg011Wk30\Tg0126k40[Tg02kek30Zk20ETg01Z1j24Tg02lVj2tTg034=j2>Tg02m7j2sTg02m^j2rTg00ABj2BTg02nEj2qTg02nkj2}Tg02oQj2uTg027Zk20XTg033>k114Tg033\k212Tg02L2k211Tg02L[k310Tg03=Wk201Tg01Hok302Tg00_nk40@Tg003ok60xTg008;k60RTg00OXk204Tg01[Gk30QTg01^7k30wTg01^Tk30OTg00F_R1k20vTg02^4j3hTg02MDk20uTg02N0k30CTg00jjk20tTg00kHk40sTg00n5j4|Tg013Mj7{Tg00oBk30rTg0141j8zTg01G>k20qTg03LMk30pTg03M6k60}Tg03Kik70~Tg00oek70oTf0R2#5#5p>08f7R3f6R4f5R5f4R6f3R7f2R8f1R9J0R;A2p=[1392,38p=;%52#5#5#5p=]%?2#?p>0=%?2#5p=m%52#5#5#5#5#5#5#5p=`g00QER:1492g014UR;3Ap=618;3184518671889+04/32'3'3p==g00W0R<g00Z3R=P6P7P8P9J0R=A52p=<1B;2p=K1189/82p=Eg02`lR>@0Q92p>0Yg01:bR?g01;BR@7A2,39p>1518;9/32p>13%G2#Rp=:18890042p>0|B0w<:2p=gB0O<:2p=218;2p=7g00Zlg00[d7A2p=b1892,38p=o1489=A:;/32p=Y20v=2p=Z1178/89/32p=N11929A:8p=f1B;71189/82'3p>0A18;61178/89/32'3p=V1456=A:;1B;71189/82'3'3p=_1B;9/32p>0MB0Q>92=A?@p=U18781892+04p=M18671889+04/32p=W%R2,19p>0?%?2#?#?#?p=n1889/32p>0h%09/12p>0320K:2p=FAh:92p=^g02da-0u2p=\g018hR>@0C92p>0e20t:2p=iP:P8P9P2H0sp=CP:P9g01:;P2C|p>0:P9g0164RAg016SRBPBg0173RCP2g017SRDF{p>0H20I:2p=IP8PAPBPBPCP:P9g019TREP2C|PDF{p=@B0r:92p=JP4PAPBPBPCP5P6P7PAPBPBPCP8P9P2GzGzp=eAA?2@p>0]P:P9PEP2C|p=k20J:2p=jP6PAPBPBPCP7PAPBPBPCP8PDF{P9P2Gzp=TAA:2;p=O20q89/129A:7p=P18;81B92'3p=QAA:92p=~B0p:92p=LAh:929h:89h:79h:6p=lAh:929h:8p>07B0C>92:0C>8p=SP8PAPBPBPCP:P9g01MbREP2C|PDF{p=wP9PAPBPBPCP2J0}p>0UP:P9PEP2C|p=cP6PAPBPBPCP7P8P9PAPBPBPCP2PDF{Gzp=yP8PAPBPBPCP9P2K0~p=xP8PAPBPBPCP9P2K0op>0>P7PAPBPBPCP8P9P2Gzp>0{B0O<:2,19p=p1B92,38p>0zg00PLg00R]RA#5RD#5RE#5RF#5RG$08RH$0L$0F&0LF$0F$00[g002@RIg00Y<RJp,2rcRK@0S78&00JRLPIPJPIP<g00WNRMP:g00WgRNH0nROP<PMg00X@RPP:PNg00X^J0lRNPJH0<RQPIPOPNPJH0;RRP8%v61dJ9G[P9B0SK56P020DK4B0VK4520TK5B0PK4520W4520N453;3;1935RS%XGRG,1SRT&0jKRUPT&08H#]RH#]#XRT%5A$0=#m#?#]#`#XRVPS16SGG=P2f8RS-0DKf9RW>0VKS20TKSB0PKWS20WWS20NWS3;3;P9f:RX-0DKP0f;RY-0GK&00=RZP<PMPPP=H0<R[P<PMPPP=H0;RPP9f=RM#H1d=2R\E<%09R]#KR^%XHRH,6]%G9R_%R_R_=E]UR`20Y]_+15+133;Ra[^0=^E<PZP[PPP7f?S00#HRb1d=8RcE<PZP[PPP8f@Rd#HRe1d=9RfE<AA<57$06%05Rg%:5Rh'1Ri&0B7%07%:7&0B53E40|[Rj[[^D=^G<^C=^F<20y<:Rkg00V9Rl&00lRmPkPlPIPOPNPlH0<RnPIPOPNPlH0;RNP9&05M1dl2ROG[PZP[PP%g7RIPbP\E<Rb%27Ro#7Rp%:2Rq9EoH%a2#bRr$06&0B2%02Rs/1o3o9YoH3;Rt'3X0=#Z[]B]6PLPkPJPQPRP9%vM1dJ2RuG[PoPGPq16oGCN9;rpRp,3bX0=#Z[^8J^7k'33;f<Rb/9XRo11oGRvPUPvPTPVPo16oGG=P220GKMPZP[PPP9PeP\E<Pa[^0=^E<PZP[PPP7fBRe#HRoPcE<PZP[PPP8fCRv#HRwPfE<Pj[[^D=^G<^C=^F<PmPkPlPnPNP9&05dPOG[PZP[PPPIPoP\E<Ro/3tX0=#Z[^Bl^6kPLPkPJPQPRP9%vdPuG[13opX0=#Z[^8J^7k'33;P0PZP[PPP9fARo#HP\E<Pa[^0=^E<PZP[PPP7PwPcE<PZP[PPP8fDRx#HRyPfE<Pj[[^D=^G<^C=^F<PmPkPlPnPNP9&05oPOG[PZP[PPPIPwP\E<Rz/3tX0=#Z[^Bl^6kPLPkPJPQPRP9%voPuG[13zpX0=#Z[^8J^7k3;f>S01,9dRz11zGR{PUP{PTPVPz16zGG=P2PZP[PPP9PwP\E<Pa[^0=^E<PZP[PPP7fFRa#HRwPcE<PZP[PPP8fGRc#HRzPfE<Pj[[^D=^G<^C=^F<PmPkPlPnPNP9&05xPOG[PZP[PPPIPwP\E<Rw/3tX0=#Z[^Bl^6kPLPkPJPQPRP9%vxPuG[13wpX0=#Z[^8J^7k3;PKPvPoPdPXQ01J0mPZP[PP%gePyP\E<19xe%2eRy7fs%7yPyPGPqPsPsPqPUH0ARk9YyGCN5;r3;X0=#ZP1P=PZP[PP%gvfER1#HP\E<191vRy%2vRJ7fs%7JPJPGPqAYJGkCN5;r3;X0=Py11yGRJPUPJPTPVPy16yGG=P2PZP[PP%g1PzP\E<19c1%21R\7fs%7\P\PGPqAY\GkCN5;r3;P0PZP[PP%gafHRr#HPfE<19ra%2aRf7f]%a9#bPfPfPGP_13^`9YfGDV3;fIRf/9cRc11cGR`PUP`PTPVPc16cGG=P2PZP[PP%grfJRP#H1d=7E<fKR[/9f%06RZ%2fRc3f%a6#bPcPcPG%:6R`PcPGPZPZP`PUE_DV3;P0fLR`/9P%2PRZ7fg%a5#b%7ZPZPGPh18iU-0Mg9YZGCN3;fMRZ/9[Rg11gGRiPUPiPTPVPg16gGG=P2fNRg/9`%03%2`3f%aS#b%2ZRi#7PiPG%:SRhPiPG%0SRiPiPhPUE_CN3;P0%aW#b%2gRhPhPG%:WRiPhPG%0WRhPhPiPUE_DVfQRifO'9Rh11hGRcPUPcPTPVPh16hGG=P2%aY#b%2iRhPhPG%:bRcPhPG%0bRbPbPcPUE_DVP0fRRc#2Rb#7PbPG%:MRhPbPG%0MRMPMPhPUE_CNfURhfS'9RM11MGRbPUPbPTPVPM16MGG=P2fTRM#2#7%2hRbPG%:dR^PbPG%0dRdPdP^PUE_CNP0fVR^#2Rd%:oRb7EGPdPG%0oRoPoPbPUE_fYRbfW'9Ro11oGRdPUPdPTPVPo16oGG=P2fXRo#2%:v7EG%2bPG%0xRdPd%:xPUE_P0fZRd#2/6G%01R_P_%:1PUH0Af]R_f['9R]11]GR\PUP\PTPVP]16]GG=P2f\R]#2/6G%0rR\P\%:rPUH0AP0%0fRr#K%:f=ErUfaRrf_R\'9Rk11kGRqPUPqPTPVPk16kGG=P2%0[#K%0`%:`;EUPcfbR`#gPZPfO3%0ZR[%GZRZP[%RZRZPU1U[ZDV9Y[H+0MP0%0gR[#K%GgRgP[%RgRgPU1U[gDV9Y[HffR[fdRg'9RZ11ZGRkPUPkPTPVPZ16ZGG=P2fP#0#K%0iRZ%GiRkPZ%RkRkPU1UZkDV7YHP0%0cRk/6H%GcRZPk%RZRZPU1UkZDVfjRZfhRk'9Rq11qGRsPUPsPTPVPq16qGG=P2%0M/6H%GhRM%0hRq%RMRMPU1UqMDVP0%G^RM#7%0^Rq%RMRMPU1UqMCNfnRMflRq'9Rs11sGRzPUPzPTPVPs16sGG=P2%Go#7%0bRo%:bRsPU1UosCNP0%0dRs%:dRo;EU1UsofrS02fpS03'9Ro11oGRsPUPsPTPVPo16oGG=P2%0]%:];EU%0_%:_'Uf^R]#0Ro%:]Rs<0k211osRsPT%?ES04#5#]#`#XRzPoPsPz%5A#m#m#]#`#XRyPoPsPy%5A#m$0=#]#`#XRJPoPsPJPVPoCMDWDWDWP0%0\R0%G\+0?R\PTPzP0CMP\PzPyP0P\PyPJP0P\PJPVP0CMDWDWfwfu'9R0110GR\PUP\PTPVP0160GG=P2%0rR0%Gr+0?PTPzP0CM%0`R0%G`+0?RrPzPyP0PrPyPJP0PrPJPVP0CMDWDW&0iK%?ARK#?S05#n#n#nR0#5#?$0=#n#m$08#]#`#`#X%n0#n#m$08#]#`#`#X,8U80hU%GgRg$0g%Rg,8gP:fefzRg#2R0+03RrP2112GR\PUP\PTPVP2162GG=Xs:%7r11rGR\/8URoP\PTPVPrCMR\16rGRr'3Rs'3g01MCRw#DRp#DRu#FRR%FpRp20K:wRw'^S06'^#\&0f>RQ+0eRL&0d>R>%i8Rl&0c:Rt7C9&0b:RI&0a:RO20J:;RN20I:ARn+0:-0HOS07&0`BRBPO%IDRm9@ONS08PB1JnmR<9@ONFe20_OCRCP2P8209?@20^28$0]dB0\:;9H0[R@b<b=b>X2:X3:%K2%78S091187R?#7[[^2:^3:P2f{S0:#2Rj%0[R{PPP^O4b;PoPsPLP>%i6?C7t9Cl9PIPOPO%?DRD#IRl,Jn%IKRL'kPBPOPO%jGRs,JmS0;/klPB1J<sS0<=@OLDTDTPCP@b<b=b>X2:X3:X4:X5:AE278AE8G6AE?G6[[^2:^3:^4:^5:P2%:[PUPjP{PfPcO6b;P\PrB0Z0GhS0=%7GR014jG#7[S0>20E{HS0?%7{%7H%0kRk/4HR{#7[[S0@fg#0S0A/tH%OHRj$06S0BPkPH1>kHP{CP[1skH%KHR{fi#0Rh/4HRr?QrH[1rhH1BH;S0C%0ZRZ/4HRr,BH?or;[1qZHfk#0Rr/>H#O\j1}rH%0qRq/4H/~q\jg03N8R\1uqHRcePcp+01C#2S0D/tG%OGRc$06Rfp+01D#2RUPG1>UG14UGCP[1sUG%KGRUp+01E#2R?/4GRo?QoG[1r?G1BG;R?p+01F#2Ro/4GR^,BG?o^;[1qoGp+01G#2Ro/>G#O\c1}oGp+01H#2Ro/4G/~o\cP\1uoGRoePoP6g02bJRo20X;G+09PUeS0EO1S0Fp+01I#2S0G/4GR^?Q^GPY20X;H-09oP{eO1S0Hft#0/4HRo?QoH&14A-12:RA%DuRu#DRo#DRY#DR^#DRP#DS0I#DR|#DS0J#DR}#DR~#FS0K'LS0L%F}S0M,LA%F^S0N,LA%FoRo,LAS0OPwDl211:G>10:wS0P%D~#FR~Q0K%F|R|%FPRP%FYRY%FuRu407Dl#\+011^uRRw,^PR^,^|#\S0QQ0J#FR}@07|w#\Q0KQ0MQ0NPoPpDlQ0P1LA~Q0LQ0I#FR~1LAPS0I1LAY<07oDl#\+01RoB07|~w#\R~Q0Q1^}^#\R^AS~~Q9S~~9So^3S9S~~7S~3S3SP>%i7%i3S0Q?C3t7C8%i4?C6tS0L%i5S0P7C37C9PIPOPOAwOsN-0UOS0KPBPO%5D#I:02:sS0J/Jl,cmDyPBPOPO%jHRm=wON-0UOS0RPBPOQ04#I:02:mQ05#IS05'J,cnDyPBPO%IERE,JnR~%jzR^5@O%jyRo=@On5xOA@O~o%jJRo=@On5xOA@O~o%jVRo=@On5xO60>O60>OPBPO%jTRw9@O~A@O^n5xOPBPOPOQ05/cNPBPOQ07PBPOAwOlNPBPOPOQ0;/kEPBPOQ08PBQ0<=@OwA@Oo<5xOH0{DTFeDTFeFePCP@b<b=b>X2:X3:X4:X5:X?:X@:XA:g03PbRo\cR<P8PGP3P6CP[Po\jRoP8PHP3P4CP[1186RwPzPyP8PwPyPJP8PwPJPVP8CMDWDW1175PTPzP7CM%OS%K5%OWRzAESGW%7W11WXRJ/1GPTPVPJCM[[[[[[[[[^2:^3:^4:^5:^?:^@:^A:P2p+01L#2RJ/>GfvRw#0Ry/>H14yH14JGRl%:wPJPyPSQ01PvPxPiPdP]P`P[O@b;b9b:fs#0R]Q0G'1Rd/1GPTPVPdCMebKbJbSbRb:bQbPbObNbMb9bIbUbVQ0=Q0>Q0?Q0@Q0Af|Rd'pRV00EG%7Vf~RV,phRh/4GRT#7\0[f},pk/tGPhPG1>hGPTCP\f1shGp+01@,pZRZ/4GRh?QhG\U1rZGp+01A,prRr/4GRZ,BG?oZ;\?1qrGp+01B,pqRq/>G#O\c1}qGfmQ0D+03Rq/4G/~q\cP\1uqGRqePq%0M/tHQ0Bfo#0RqPH1>qH14qHCP[1sqHQ03#0Rq/4HRr?QrH\{1rqHQ0Cfq#0Rq/4HR{,BH?o{;[1qqHQ02#0Rq/>H#O\j1}qH14]H/~]\jP\1u]HR]eP]p+01J#2/tGp+01K#2R]PG1>]G14]GCP\f1s]GAQllG\U1rJGp+01M#2RJ/4GRU,BG?oU;\?1qJGp+01N#2RJ/>G#O\c1}JGp+01O#2RJ/4G/~J\cP\1uJGRJePJQ0Fp+01P#2RJ/4GR\?Q\GQ0HQ0:#0/4HR\?Q\HPeQ0EO1p+01R#2-03d/4GRe?QeG1LA}1LA|PPQ0NQ0O1LAR'^DlQ0MP}Q0IPY1^upDlQ06#\+01+01Ru?SuQP>Q0P%iS7C7Q0L7CSQ0Q?CSt9Ct87C9PIPOPOQ0KPBPO%5KRK#5#I:02:s%IKRK'J,cEDyPBPOPOQ0RPBPO%?D#I:02:m%IFRF'J,cLDyPBPOA@ONnRm20:ns-0HO60>OPBPOPOQ0KPBPO1JLERDQ0J/Jn'cDyPBPOPOPO1kNDPBPOPO1kNsPBPmDTDTPBPOAwOFNPBPOPO20:NLPBPOPO1cKNPBPOPO1kNEPBAwOnNDTDTDTFeFeFePCP@b<b=b>X2:X3:X4:X5:X?:X@:XA:XW:P7PGPSP6CP\<P7PHPSP4CP\oQ09@0z8G1154R5PGPWP6CP\<%75%74\0[%K3%OX%7XPz[[[\z[[[[[^2:^3:^4:^5:^?:^@:^A:^W:P2p+01T#2R:/>G%0VRV/>H11V:Rz/>G14VH14:GP:PV14zGPWQ00P9P1PaPbP`P[PMOAb;b9b:bL203gJ/6Geb`b_b^b]bLb\bKbJbSbRb:bQbPbObNbMb9bIbobUbVH0@H0@H0@19dgP_J0xb1bXW[WZP9P2O2n2001000000121000000b6WhWnP9P2O2n2001000000121000000W1WTP9P2O2n2001000000121000000W1WeP9P2O2n2001000000121000000W1WHP9P2O2n2001000000121000000b6WgWfP9P2O2n2001000000121000000W1WkP9P2O2n2001000000121000000W1WjP9P2O2n2001000000121000000W1WiP9P2O2n2001000000121000000W1WcP9P2O2n2001000000121000000W1WYP9P2O2n2001000000121000000W1WbP9P2O2n2001000000121000000W1X0=P9P2O2n2001000000121100000bpWTWmP9P2O2n2011000000121000000W1WHP9P2O2n2011000000121000000b1WHWlP9P2O2n2001000000121000000b1WaWdW8W7WqWro"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  (lo <= a < sp
   \/ RCTX <= a < RCTX + 928
   \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
Lemma rfree_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> rfree_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

Lemma rfree_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
  conc st q <= a < conc st q + 40 -> rfree_fp st lo sp a.
Proof.
  intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.

(* [comment removed for export] *)
Lemma rfree_fp_mono : forall st st' lo sp sp' a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
  (forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
  sp' <= sp ->
  rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
  - right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

Lemma rpres_except_of_munch' : forall C W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
  rpres_except C m m'.
Proof.
  intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
  intros a _ HC. eapply outside_of_cover; eauto.
Qed.

Lemma rpres_except_of_munch_cov : forall C W m m',
  munch W m m' -> wmono usegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono usegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_statics st' = s_statics st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

Lemma rctxW_avoid : forall A n, (A + n <= RCTX \/ RCTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
  0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
  intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

Lemma rmrep_ctx_frameW :
  (rw_cells usegs m' RCTX (rctx_head_cells st') \/ (rctx_head_cells st' = rctx_head_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 80 <= lo \/ hi <= RCTX)) ->
  (u64arr usegs m' (RCTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> RCTX + 464 <= lo \/ hi <= RCTX + 80)) ->
  (u64arr usegs m' (RCTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> RCTX + 848 <= lo \/ hi <= RCTX + 464)) ->
  (u8arr usegs m' (RCTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> RCTX + 880 <= lo \/ hi <= RCTX + 848)) ->
  (u8arr usegs m' (RCTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> RCTX + 912 <= lo \/ hi <= RCTX + 880)) ->
  (rw_cells usegs m' (RCTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 928 <= lo \/ hi <= RCTX + 912)) ->
  rmrep st' m'.
Proof.
  intros H1 H2 H3 H4 H5 H6.
  pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
  assert (CX' : rmrep_ctx st' m').
  { unfold rmrep_ctx. split; [|split; [|split; [|split; [|split]]]].
    - destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
  eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
  clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.

(* [comment removed for export] *)
Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rmrep st' m'.
End CANSEC1.
