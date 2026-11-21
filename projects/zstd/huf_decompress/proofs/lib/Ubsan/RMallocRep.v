(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (40 recorded proofs replaced by written proofs (rctx_head_cells_tl, rstatics_same, rregions_wf_reserved and 37 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocRep.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Export UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocRep () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp4base6LookupI35stdpp9countable9Countable00C35stdpp4base;RelDecisionI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Ubsan4UImg>ubsan_reservedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib6Malloc9MallocRep>ctx_head_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega6VarMap1t03C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep=RSIZE_CLASSESC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRepCrsize_classes_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep@rsize_classes_roC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2ex01C47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8f_equal2C35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnK46Stdlib9micromega=RingMicromega5Psatz06C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep5rsecwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_rC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes3orbC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib5Ubsan:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5wr_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc9MallocRep:lr_lo_nbrkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep<rwr_in_imageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep?rmrep_ctx_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_ctx_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRepCrmrep_globals_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5Ubsan:RMallocRep<rwr_in_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep?rarea_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep=rarea_rep_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat3N2Z9is_nonnegc59OSSVerify5KrLib5Ubsan:RMallocRep@rgroup_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep>rgroup_rep_extC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Malloc9MallocRepBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemCbytes_at_write_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepDget_shadow_wr8_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRepArshadow_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep?rshadow_rep_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7wr8_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib3Mem7wa_succC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9le2_splitC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib6Malloc9MallocRep@get_meta_rec_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C56Stdlib6NArith6BinNat1N7eqb_neqC47Corelib4Init5Logic5proj2C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRepArmrep_meta_store4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepBactives_set_activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib6Malloc9MallocRep9shadow_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8sh_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>shadow_le_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep>rshadow_rep_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC35stdpp4base5emptyC35stdpp8fin_maps<lookup_emptyC56Stdlib6NArith6BinNat1N7compareC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison03C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepDsh_ticks_of_ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>havoc_pages_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>havoc_units_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep?shadow_le_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMallocRep@rmrep_upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep=hav_unit_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6W_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep?W_high_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImgAref_wview_overlayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg?ref_mrd_overlayC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition RCTX : Z := 0x5bba8.
Definition RMLOCK : Z := 0x5bba0.
Definition RLIBC : Z := 0x5bb30.
Definition RNEED_LOCKS : Z := 0x5bb33.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSIZE_CLASSES : Z := 0x1065c.
Definition RDEBRUIJN : Z := 0x10540.
Definition RSMALL_CNT : Z := 0x106bc.
Definition RMED_CNT : Z := 0x106d7.
Definition RGOT_SSP : Z := 0x2a528.      (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0x5bb10.    (* [comment removed for export] *)
Definition RATP : Z := 0x3b8a0.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x3b7fc.        (* [comment removed for export] *)

Definition rget_meta_entry : Z := 0x21e40.
Definition rmalloc_entry : Z := 0x22600.      (* [comment removed for export] *)
Definition rfree_entry : Z := 0x21c74.        (* [comment removed for export] *)
Definition ralloc_meta_entry : Z := 0x22328.
Definition ralloc_slot_entry : Z := 0x22970.
Definition renframe_entry : Z := 0x23214.
Definition rnontrivial_free_entry : Z := 0x21f50.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlock_entry : Z := 0x290b8.
Definition runlock_entry : Z := 0x29340.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ref_reserved : list (Z * Z) := [(0x10000, 0x2000); (0x12000, 0x18000); (0x2a000, 0x1000); (0x2b000, 0x32000)].

Lemma ref_reserved_plain : ref_reserved = ubsan_reserved.
Proof.
reflexivity. Qed.

Lemma reservedZ_ref : reservedZ usegs = ref_reserved.
Proof.
vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition rsecw : word := wz (SECRET * c_init_done (ctx st)).
Definition rctx_head_cells : list cell :=
  let c := ctx st in
  [C8 rsecw; C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
   C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
   C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
   C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].
Lemma rctx_head_cells_tl : tl rctx_head_cells = tl (ctx_head_cells st).
Proof. reflexivity. Qed.


Definition rmrep_ctx : Prop :=
  rw_cells usegs m RCTX rctx_head_cells
  /\ u64arr usegs m (RCTX + 80) (actives st)
  /\ u64arr usegs m (RCTX + 464) (usages st)
  /\ u8arr usegs m (RCTX + 848) (unmap_seqs st)
  /\ u8arr usegs m (RCTX + 880) (bouncess st)
  /\ rw_cells usegs m (RCTX + 912) (ctx_tail_cells st).

Definition rmrep_globals : Prop :=
  rw_cells usegs m RMLOCK [C4 (wz 0)]
  /\ rw_cells usegs m RNEED_LOCKS [C1 (b8 0)]
  /\ rw_cells usegs m RPAGE_SIZE [C8 (wz 4096)]
  /\ rw_cells usegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
  /\ rw_cells usegs m RSSP_GUARD [C8 CAN].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rarea_rep (a : aptr) (ar : area) : Prop :=
  rw_cells usegs m (conc st a) [C8 (wz SECRET); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
  /\ (forall k, 0 <= k < NSLOTS ->
        rw_cells usegs m (conc st a + AREA_HDR + META_SIZE * k)
                 (meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
  /\ rw_cells usegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition rmrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.

(* [comment removed for export] *)
Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
  exists w8 : byte,
    rw_cells usegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
    /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition rmrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.

(* [comment removed for export] *)
Definition rshadow_rep (rid : N) (r : region) : Prop :=
  wr_at usegs m (r_base r) (round_up_pg (r_len r))
  /\ forall o v, 0 <= o < round_up_pg (r_len r) ->
       cell_read (get_shadow st rid) o = Known v ->
       bytes_at usegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition rmrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstatics : Prop :=
  s_reserved st = ref_reserved /\ s_atop st = ATOP /\ s_secret st = 0.

Lemma rstatics_reserved : rstatics -> s_reserved st = ref_reserved.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g003ij27Tg004Ij16Tg00JSj11Tg00:?j30Tg00KNj15Tg00LEj12Tg00M;j13Tg00N4R0j24Tg00NOP0g005CR1/71#6p,2stR2#1g00<S30R3%52p,2rc#2501R4%32g00OM501R1'4R2P3f0R5P0P4P1P3P5f5X31X24f1R4P5O2n2001000000120000000X02X13P4P5O2n2001000000120000000W0o"). Qed.
Lemma rstatics_atop : rstatics -> s_atop st = ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g003ij27Tg004Ij16Tg00JSj11Tg00:?j30Tg00KNj15Tg00LEj12Tg00M;j13Tg00N4R0j24Tg00NOP0g005CR1/71#6p,2stR2#1g00<S30R3%52p,2rc#2501R4%32g00OM501R1'4R2P4f0R5P0P4P1P4P5f1R0X31X14P0P5O2n2001000000120000000X02X23P0P5O2n2001000000120000000W0o"). Qed.
Lemma rstatics_secret : rstatics -> s_secret st = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g003ij27Tg004Ij16Tg00JSj11Tg00:?j30Tg00KNj15Tg00LEj12Tg00M;j13Tg00N4R0j24Tg00NOP0g005CR1/71#6p,2stR2#1g00<S30R3%52p,2rc#2501R4%32g00OM501R1'4R2P1f0R5P0P4P1P1P5P5X11X34f1R4P5O2n2001000000120000000X02X23P4P5O2n2001000000120000000W0o"). Qed.

Definition rregions_wf : Prop :=
  rstatics
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= ATOP
        /\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true)
  /\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
        r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
  (* [comment removed for export] *)
  /\ (forall a ar, (s_areas st) !! a = Some ar ->
        exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
                  /\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
  /\ (forall b gh, (s_groups st) !! b = Some gh ->
        exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

Definition rmrep : Prop :=
  rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.

End MREP.

Lemma rstatics_same : forall st st', s_reserved st' = s_reserved st -> s_atop st' = s_atop st -> s_secret st' = s_secret st ->
  rstatics st -> rstatics st'.
Proof. intros st st' E1 E2 E3 (H1 & H2 & H3). unfold rstatics. rewrite E1, E2, E3. auto. Qed.
Lemma rregions_wf_reserved : forall st, rregions_wf st -> s_reserved st = ref_reserved.
Proof. intros st ((H & _) & _). exact H. Qed.
Lemma rregions_wf_atop : forall st, rregions_wf st -> s_atop st = ATOP.
Proof. intros st ((_ & H & _) & _). exact H. Qed.

(* [comment removed for export] *)
Definition s_statics (st : mstate) : Z * Z * list (Z * Z) := (s_atop st, s_secret st, s_reserved st).
Lemma rregions_wf_restatics : forall st st',
  s_regions st' = s_regions st -> s_areas st' = s_areas st -> s_groups st' = s_groups st -> s_statics st' = s_statics st ->
  rregions_wf st -> rregions_wf st'.
Proof.
  intros st st' ER EA EG EST (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG.
  split; [|split; [exact WR|split; [exact DJ|split; [exact WA|exact WG]]]].
  unfold s_statics in EST. destruct RS as (R1 & R2 & R3). unfold rstatics.
  inversion EST. rewrite R1, R2, R3 in *. auto.
Qed.

(* [comment removed for export] *)
Definition rmrep_W (st : mstate) : list (Z * Z) :=
  (RCTX, RCTX + 928)
  :: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

(* [comment removed for export] *)
Lemma rmrep_shadow_read : forall st m rid r o v,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v ->
  ov_read_bytes usegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256.
Proof.
  intros st m rid r o v (WF & _ & _ & _ & _ & SH) Hr Hk Ho Hc.
  destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read usegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rmrep_shadow_read2 : forall st m rid r o v0 v1,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o -> o + 2 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v0 ->
  cell_read (get_shadow st rid) (o + 1) = Known v1 ->
  ov_read_bytes usegs m (wa (r_base r + o)) 2 = Some [b8 v0; b8 v1] /\ 0 <= v0 < 256 /\ 0 <= v1 < 256.
Proof.
  intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
  pose proof MR as (WF & _ & _ & _ & _ & SH).
  destruct (SH rid r Hr Hk) as [HW HB].
  destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
  split; [|split; assumption].
  assert (B : bytes_at usegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
  { apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read usegs m _ _ 0 2 B); [lia|cbn; lia].
Qed.


(* [comment removed for export] *)
Definition rsize_classes_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RSIZE_CLASSES 96 with Some bs => bs | None => [] end).

Lemma rsize_classes_ro : forall m, mem_inv usegs m -> ro_cells usegs m RSIZE_CLASSES [CB 96 rsize_classes_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RSIZE_CLASSES; lia | unfold RSIZE_CLASSES; cbn; lia]. Qed.

Lemma rsize_classes_read : forall m sc, mem_inv usegs m -> 0 <= sc < 48 ->
  ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))).
Proof.
  intros m sc MI Hsc.
  destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read usegs m RSIZE_CLASSES rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
  assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.


Lemma rmrep_meta_chunk : forall st m g,
  rmrep st m -> meta_slot st g ->
  rw_cells usegs m (conc st g) (meta_cells st (get_meta_rec st g)).
Proof.
  intros st m g MR (a & ar & k & Ha & Hk & ->).
  pose proof MR as (WF & _ & _ & AR & _ & _).
  destruct (AR a ar Ha) as (_ & SL & _).
  destruct WF as (_ & _ & _ & WA & _). destruct (WA a ar Ha) as (r & Hr & _).
  rewrite conc_aadd by (rewrite Hr; eauto).
  replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed.

Lemma rmrep_group_read : forall st m b gh,
  rmrep st m -> (s_groups st) !! b = Some gh ->
  ov_read_bytes usegs m (wa (conc st b)) 8 = Some (le8 (pw st (g_meta gh)))
  /\ exists w8 : byte, ov_read_bytes usegs m (wa (conc st b + 8)) 1 = Some [w8] /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Proof.
  intros st m b gh MR Hb. pose proof MR as (_ & _ & _ & _ & GR & _).
  destruct (GR b gh Hb) as (w8 & RW & Hw8). split.
  - rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at usegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
  - exists w8. split; [|exact Hw8].
    apply (rw_cells_read_at usegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.

Lemma rmrep_area_check_read : forall st m a ar,
  rmrep st m -> (s_areas st) !! a = Some ar ->
  ov_read_bytes usegs m (wa (conc st a)) 8 = Some (le8 (wz SECRET)).
Proof.
  intros st m a ar MR Ha. pose proof MR as (_ & _ & _ & AR & _ & _).
  destruct (AR a ar Ha) as (HD & _ & _).
  rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at usegs m _ _ 0 (C8 (wz SECRET)) 8 _ HD); reflexivity.
Qed.

Lemma rmrep_ctx_secret_read : forall st m,
  rmrep st m -> ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (rsecw st)).
Proof.
  intros st m (_ & (HD & _) & _).
  rewrite <- (Z.add_0_r RCTX). apply (rw_cells_read_at usegs m _ _ 0 (C8 (rsecw st)) 8 _ HD); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rsecw_init : forall st, c_init_done (ctx st) = 1 -> rsecw st = wz SECRET.
Proof. intros st H. unfold rsecw. rewrite H, Z.mul_1_r. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rreserved_disjoint : forall b n, ranges_free ref_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x12000 <= b) /\ ((b + n <= 0x12000 \/ 0x2a000 <= b)
  /\ (b + n <= 0x2a000 \/ 0x2b000 <= b) /\ (b + n <= 0x2b000 \/ 0x5d000 <= b)).
Proof.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H.
lia.
Qed.

Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  b + n <= 0x10000 \/ 0x5d000 <= b.
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H).
lia. Qed.

Lemma rwr_in_image : forall st rid a len,
  rregions_wf st -> wr_in st rid a len ->
  ((a + len <= 0x2a000 \/ 0x2b000 <= a) /\ (a + len <= 0x2b000 \/ 0x5d000 <= a)) /\ 0 <= a /\ a + len <= 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h01rh11Hh21ah33ridh42arh51bh62ghh72r1h82r2h94rid1h:4rid2h;2_Hh<2Hah=4__p1h>6__sat5h?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE2a0hF5ATOPRhG2B0hH2BChI2D2hJ2H0hK2H1hL2H2hM2H3hN2HrhO2L0hP2RFhQ2WRhR3_H0hS7__arithhT4__ffhU6__sat4hV8__varmaphW5__withX3lenhY2sti001xp&0p;1p;4p;2p;3p;6p;7p;8g00Q?k10QTg00NOj1wTg00R@j1fTg00E@j4gTg00?Dj4jTg00Rbj1;Tg00S\j2YTg00T>j12Tg006_j14Tg007Dj1?Tg00V1j1@Tg00WCj1BTg00X?j23Tg00LEk10NTg00:?j3LTg00YXj1oTg00Z1j1NTg003ik205Tg00[Fk404Tg00[dk603Tg00\Ej1bTg00]Qj3}Tg00]nj3{Tg00^Kj1yTg00Vgj20Tg00N4R0j21Tg00_Bj1cTg02aIj4kTg007bj1<Tg01V\k20PTg02bDk10MTg02`Ak30JTg02cBk10ITg02dFk10GTg02eDk20FTg02elk30ETg02fPk20DTg004ij2rTg0114j1=Tg01`Zj2qTg008Gk10@Tg004Ik10?Tg019ij2dTg012Ek10=Tg01QYj4eTg012ck10<Tg013Ak10;Tg01:Gj2WTg01;Nk10:Tg01<0j3nTg01GGk606Tg013lj2lTg014Oj4mTg00i7k108Tg01V9k309Tg015:k202Tg015\k201Tg016Hk300Tg016gk40ATg00]=j6sTg00U5j2~Tg00UQk20CTg00X\j3tTg00Zlj2STg00`;R1j2|Tg01nLj3_Tg01bkk20HTg008gj3`Tg01E3j7uTg01:jj7zTg01Gkk70LTg01<Sj8xTf5R2g00`UR3g00a3R4f4R5f3R6f2R7f1R8Esf0R93Lp=5g00OMR:/~9p=R%49#4p=]%49#4#4#4p=Kg005CR;20C89;L:p=O1067g00bcR<g00<SR=?t89g00cCR>3L'1p>0K10:8/19p=^1189,17p=9%@9#B,38p=F%@9#Bp=G1378/09p=U1078/S9p=[f7R?f6R@P2P5P6P7P8Es;L9p=M10:9p=61|49p=Q1367/08/19p=:%<9#4p=T%49#4#4#4#4#4#4#4p=J%<9#<p=i10@2/S5/1610:71089'1'1p>0O1089,17p=a1056/S7/18/19p=v1078/19p=h10671089'Sp=810?@1025'S/1610:71089'1'1p=EAt=89=L<>p=D%<9#<#<#<p=X10561078'S/19p=P1q;9p=>A_;89p=CA_;89g022T+0Hp=AA_;899_;7p=pg01O8R=A`=899`=79`=67`5p=HP7g01IIRAg01IhRBPBg01JHRCP;P8g01OdP9Cmg01JhRDFup=71l;9p=ZP7PAPBPBPCP8P9Fzp=\P7PAPBPBPCP8P9K0Lp=VP8PAPBPBPCP9PDFup>07P6PAPBPBPCP7P8P9Gxp=IAL<9>p>0>1067/S8/19p>0Bg00PF&0Q6P0%w5%f4RDP3g00alREg00bERFP4CgRGP3PEPFP4CjRHP8%;@1Y49RIE5%28RJ#Rg00;9RK#4RL#4RM#]RN#]RO#]#KRP#?RQ,OJ%@8RR%BRRR,3JRSp,2rcRT$0NRUPJPRH0K'^39RR[^04^33PDPGPHP6f8RJ#;RV1Y47RWE5PDPGPHP7f9RX#;RY1Y48RZE5AL326#o%22/F2R[%N6%26%G6%N2R\3U3[[R][[^84^:3^74^932053;R^g00ccR_%f_R`P^P_g00=URaP3PEP;g00dZRbH04RcP3PEPFP;Pbg00e3J03RbP_CgRFPaPcPbP_CjREP8%b@1Y_9RdGMPDPGPHA}3;6RePVPIE5RVA{3;6Rf#6Rg%G9Rh9UfQ1OfQg00eQ%y9g00fI3LRi#o%N9Rj%29Rk/3f'03939Rl'1X04#Q[]4]2g00gARm%fmRnP^PmPaPcPbPmCgRoPaPcPbPmCjRbP8%c@1Ym9RcGMPf%?NRNPh1OfNC:99igRi,1VX04#Q[]6^5^'139P2P5P6P7Ck1356RV%4K#T#T#K#J#?Rg%4K#T#i#K#J#?RN/05Rf%4K#i#T#<#K#J#?Ra/05Rp9[VNP5PV%?LRV%?ORq+0PRrK0O[P9%w@PDPGPHP8PYPIE5PR[^04^33PDPGPHP6f;RY#;RsPWE5PDPGPHP7f<Rt#;RuPZE5P][[^84^:3^74^93P`P^P_PFPEP8%bXPdGMPDPGPHPePsPIE5Rs/1lX04#Q[^4_^2^PnP^PmPoPbP8%cXPcGM11siX04#Q[^6m^5^'139P0PDPGPHP8f:Rs#;PIE5PR[^04^33PDPGPHP6PuPWE5PDPGPHP7f=Rv#;PZE5P][[^84^:3^74^93P`P^P_PFPEP8%bsPdGMPDPGPHPePuPIE5Rw/1lX04#Q[^4_^2^PnP^PmPoPbP8%csPcGM11wiX04#Q[^6m^5^39PXPJP?P@Ck13J?RwPg10NJRx10aJRy9[wN%6JRz?awrDv[P9PDPGPHP8PuPIE5PR[^04^33PDPGPHP6f?RR#;RuPWE5PDPGPHP7f@RW#;RwPZE5P][[^84^:3^74^93P`P^P_PFPEP8%bvPdGMPDPGPHPePuPIE5Ru/1lX04#Q[^4_^2^PnP^PmPoPbP8%cvPcGM11uiX04#Q[^6m^5^39PtPYPsPXCkP1P4PDPGPHPvf>R1#;PIE510jt13tYR^13khRk%6Y3h39X04P^PgPNPtP^PNPaPtC8PtP^PrGEP9PDPGPHPRPwPIE510j1P1PvPk%6vC:39P0PDPGPHPWfARk#;PZE5%N8PRP1PS%61C:7hR13WRRRPgPNPWPRPNPaPWC8PWPRPrGEP9PDPGPHfBRHfCRG#;1Y46E5%N5PHPk%25/F5%6kC:7hHP010\GPGPHP[%6HC:fDR[/3GRGPgPNP[PGPNPaP[C8P[PGPrGEP9%N?fERG'0fFR\PG%2J/FJ%6GC:P0fGRD%2X/FX7U\%6\fHRR/3DRDPgPNPRPDPNPaPRC8PRPDPrGEP9fIRD%2Y/FY7UR%6DPHfLRSPvPXO3%2vRZ#R1OZQ%@vRjPZ%BjRjPU1DZjC:'^39P0%21Rj#R1OjQ%@1R1#6Pj%B1R1PU1Dj1C:39fMR1/3SRjPgPNP1PjPNPaP1C8P1PjPrGEP9%2W#R%2kRW/OQ%@kRk#6PW%BkRkPU1DWkC:39P0%2HRk/OQ%@HRHPk%BHRHPU1DkHC:'^fQRHfPRk'3RWPgPNPHPWPNPaPHC8PHPWPrGEP9%2[/OQ%@GRQ%2GRG%BQRQPU1DGQC:'^P0%@\RQ#6%2\R\%BQRQPU1D\QC:fURQfTR\'3RGPgPNPQPGPNPaPQC8PQPGPrGEP9%@R#6%2DRR%GDRGPU1DRGC:P0fJRG#2RR%GGRG;UU1DRGfYRGfX'3RRPgPNPGPRPNPaPGC8PGPRPrGEP9%2S%GS;UU%21%G1'D&0MT%<KRT#<RS#X#X#XRR#4#<#i#X#T#]#K#J#J#?/0URG%XR#X#T#]#K#J#J#?RR7aUfOR[#2RW%G[R[<0J813W[R[%KP#?RP%TM#K#J#?RHPWP[PHPgPWP[PgPNPWP[PNPaPWC8DPDPDPP0%2kR0/FkRkPPPHP0C8PkPHPgP0PkPgPNP0PkPNPaP0C8DPDPf_R0f^'3RkPgPNP0PkPNPaP0C8P0PkPrGEP9fRRk#2R0/FkPPPHP0C8fSR0#2RP/F0R0PHPgPPP0PgPNPPP0PNPaPPC8DPDP%@\R\$0I%B\,0\&0GQ%2Q%NQ'020FVq%RVRQ%6q%Rr[R\[%6VRPg02g1R0B0EVq8UW<%6r\0^<PP8g02gM20D:V'rPQeO1P\p-0R\g01NYRQ#=RP#=R0#=Rq#=RW#=R[#=Rj#=RZ#=RI#>Rw%>qRq%>PRP'CR^'A%=IRI#=Rt#=#>Rh%>IRI%>0R01q;QRQ'CRm'C'A%>tRt1CPQRQ,CI'ARP%>j%>[/Cm'AR[1Cwm,AhRmPm%>Z/CQ,AtRZP[1AI^R^P^%>WRW/CQ,AtP[PmPmPZP[P[1CwQ,AtApWq09ptI,AhRhPhP[PZPmPmP[PPP^P^P[PZPmPm&0@=DHDHDHDHDHDHDHDH&0?=P;P;1d;5P7&0=;CeP8P;1d;2P61d;@CeCe&0<;&0;;R=1W;MRM1W;TRT57=&0:BRmP=%<L,W;9n;MRZ%ZH57=%ZgR[=7=M5\=A7=Z[%ZNR^=7=M5\=A7=Z^%ZaRa=7=M5\=5V=5V=PmP=P=PAPBPBPCPJJ061W;SRS%ZR57=5V=PmP=A7=ZSPmP=P;1l;:RSg01PKPMCm-07=PmP=1W;LRL97=SPmP=1W;KRK=n;LRL=7=ZPmP=A7=TKPmA7=L[A7=^K5\=A7=L^A7=aK5\=5V=A7=SK%ZV&08O609;97=L5V=5V=CICICICICICICICI202=CP9P71r<>20197$0>dB00;:8H0AbTbVbWX?;X@;XA;XB;XC;XD;W=10671352R2PHPgP5P2PgPfA[2NpH0BDPAaJ?R13@?RR/0J%R?%6@13Xs,0R10X?13JXRXPgPxA[XNyAazXrDv[[[[[[[[^?;^@;^A;^B;^C;^D;^=\P9PGPUfZRU#G%2U%NUfgfhP5P@PYPvPDP1fNPkO?bSb>bUb>bJb1WIW;P8P9O2n2001000000121000000bEbFWPWHP8P9O2n2001000000121000000W1WOP8P9O2n2001000000121000000W1W;P8P9O2n2001000000121000000W1WGP8P9O2n2001000000121000000bEWMWLP8P9O2n2001000000121000000W1WKP8P9O2n2001000000121000000W1WNP8P9O2n2001000000121000000W1X04P8P9O2n2001000000121100000W1WRWQP8P9O2n2011000000121000000W1W;P8P9O2n2011000000121000000W1XX;X2;X33WYo"). Qed.

Lemma rwr_in_other : forall st rid a len rid' r',
  rregions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
  intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

(* [comment removed for export] *)
Lemma rarea_lr_lo : forall st a ar r, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

(* [comment removed for export] *)
Lemma rregions_disjoint_full : forall st rid1 r1 rid2 r2,
  rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
  r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.

Lemma rregions_disjoint_grp : forall st rid1 r1 rid2 r2,
  rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 = RKGroup ->
  r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctx_ext : forall st st' m,
  ctx st' = ctx st -> (forall p, conc st' p = conc st p) -> rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
  intros st st' m Hc Hconc H.
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (E1 : rctx_head_cells st' = rctx_head_cells st) by (unfold rctx_head_cells, rsecw; rewrite Hc, !Hpw; reflexivity).
  assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma rarea_rep_ext : forall st st' m a ar,
  (forall p, conc st' p = conc st p) ->
  (forall k, 0 <= k < NSLOTS -> get_meta_rec st' (aadd a (AREA_HDR + META_SIZE * k)) = get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k))) ->
  rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
  intros st st' m a ar Hconc Hm (H1 & H2 & H3).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold rarea_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

Lemma rgroup_rep_ext : forall st st' m b gh,
  (forall p, conc st' p = conc st p) -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
  intros st st' m b gh Hconc (w8 & H1 & H2).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

Lemma rshadow_rep_ext : forall st st' m rid r,
  get_shadow st' rid = get_shadow st rid -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

(* [comment removed for export] *)
Lemma rmrep_ctx_frame : forall st m a bs rid,
  rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_ctx st m ->
  rmrep_ctx st (write_to_mem m (wa a) bs).
Proof.
  intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5 & H6).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold rmrep_ctx. unfold RCTX in *. split; [|split; [|split; [|split; [|split]]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply u64arr_frame; [exact H2|lia|lia|rewrite L1; cbn; lia].
  - apply u64arr_frame; [exact H3|lia|lia|rewrite L2; cbn; lia].
  - apply u8arr_frame; [exact H4|lia|lia|rewrite L3; cbn; lia].
  - apply u8arr_frame; [exact H5|lia|lia|rewrite L4; cbn; lia].
  - apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed.

Lemma rmrep_globals_frame : forall st m a bs rid,
  rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_globals m ->
  rmrep_globals (write_to_mem m (wa a) bs).
Proof.
  intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  unfold rmrep_globals. unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H2|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H4|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H5|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rarea_rep_frame : forall st m a bs ar0 ar,
  rregions_wf st -> (s_areas st) !! ar0 = Some ar ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st ar0 + 4096 <= a \/ a + Z.of_nat (length bs) <= conc st ar0) ->
  rarea_rep st m ar0 ar -> rarea_rep st (write_to_mem m (wa a) bs) ar0 ar.
Proof.
  intros st m a bs ar0 ar WF Har A0 A1 D (H1 & H2 & H3).
  unfold rarea_rep. split; [|split].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - intros k Hk. apply rw_cells_frame; [apply H2; exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
Qed.

Lemma rgroup_rep_frame : forall st m a bs b gh,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st b + 9 <= a \/ a + Z.of_nat (length bs) <= conc st b) ->
  rgroup_rep st m b gh -> rgroup_rep st (write_to_mem m (wa a) bs) b gh.
Proof.
  intros st m a bs b gh A0 A1 D (w8 & H1 & H2). exists w8. split; [|exact H2].
  apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed.

Lemma rshadow_rep_frame : forall st m a bs rid r,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (r_base r + round_up_pg (r_len r) <= a \/ a + Z.of_nat (length bs) <= r_base r) ->
  rshadow_rep st m rid r -> rshadow_rep st (write_to_mem m (wa a) bs) rid r.
Proof.
  intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
  intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
  apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rarea_conc : forall st a ar, rregions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

Lemma rgroup_conc : forall st b gh, rregions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma rmrep_wr8 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p < round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> ~ (snd b <= snd p < snd b + 9)) ->
  0 <= v < 256 ->
  rmrep (wr8 p v st) (write_to_mem m (wa (r_base r + snd p)) [b8 v]).
Proof.
  intros st m p v r MR TK Hr Hk Ho Hgrp Hv.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof (lr_lo_group r Hk) as LRr.
  assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
  { exists r. cbn. repeat split; auto; lia. }
  destruct (rwr_in_image st _ _ _ WF WI) as (D & A0 & A1). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
  assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    apply rarea_rep_frame; [exact WF|exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
    destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
    + rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
    + destruct (rwr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
    destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
    + rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
    + destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    destruct (N.eq_dec rid (fst p)) as [E|NE].
    + subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
      destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; exact HW|].
      intros o v' Ho' Hc.
      destruct (Z.eq_dec o (snd p)) as [->|NEo].
      * rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
        apply bytes_at_write_same; cbn; lia.
      * rewrite cell_read_wr8_other in Hc by exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|exact Hv'].
        apply bytes_at_write_other; [exact Hb|lia|cbn; lia|cbn; lia].
    + eapply rshadow_rep_ext; [apply get_shadow_wr8_other; exact NE|].
      pose proof (lr_lo_group r' Hk') as LR'.
      apply rshadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
      destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.


Lemma rmrep_wr16 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 2 <= round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 2 <= snd b \/ snd b + 9 <= snd p) ->
  0 <= v < 65536 ->
  rmrep (wr16 p v st) (write_to_mem m (wa (r_base r + snd p)) (le2 (wz v))).
Proof.
  intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
  rewrite le2_split by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
    with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
  rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
  replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
  replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply (rmrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
  - apply rmrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
  - apply ticks_ok_wr8. exact TK.
  - cbn. exact Hr.
  - exact Hk.
  - cbn. lia.
  - intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
  - exact Hd.
Qed.



(* [comment removed for export] *)
Lemma rmrep_meta_store4 : forall st m g (f : meta -> meta) (off : nat) v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  (forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
  (forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
  (off = 24%nat \/ off = 28%nat) ->
  rmrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v))).
Proof.
  intros st m g f off v MR (a & ar & k & Ha & Hk & Eg) Hv Hat Hupd Hoff.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
  { exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [exact Hra|]. rewrite HG, Ca. destruct Hoff; subst; cbn; lia. }
  assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a' ar' Ha'. cbn in Ha'.
    assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
    assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
    destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
    destruct (decide (a' = a)) as [->|NEa].
    + (* [comment removed for export] *)
      rewrite Ha in Ha'. inversion Ha'; subst ar'.
      destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
      split; [|split].
      * apply rw_cells_frame; [exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
      * intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
           rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
           eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
           rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by reflexivity. apply SL. unfold NSLOTS. lia.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
           rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
      * apply rw_cells_frame; [exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
    + (* [comment removed for export] *)
      assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_upd.
        replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
      apply rarea_rep_frame; [exact WF|exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
      rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
      destruct PG as [NE|[E PG]].
      * destruct (rwr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
      * rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    eapply rshadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
    apply rshadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

Lemma rmrep_meta_set_avail : forall st m g v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  rmrep (upd_meta g (m_set_avail v) st) (write_to_mem m (wa (conc st g + 24)) (le4 (wz v))).
Proof.
  intros. change 24 with (Z.of_nat 24).
  apply (rmrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.

Lemma rmrep_meta_set_freed : forall st m g v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  rmrep (upd_meta g (m_set_freed v) st) (write_to_mem m (wa (conc st g + 28)) (le4 (wz v))).
Proof.
  intros. change 28 with (Z.of_nat 28).
  apply (rmrep_meta_store4 st m g (m_set_freed v) 28%nat v); auto; intros; reflexivity.
Qed.


Lemma rmrep_set_active : forall st m sc v,
  rmrep st m -> 0 <= sc < 48 ->
  rmrep (set_active sc v st) (write_to_mem m (wa (RCTX + 80 + 8 * sc)) (le8 (pw st v))).
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h02L0h11Hh21rh34__x1h44__p1h57__arithh61nh74__p2h84cstrh95cstr0h:4__ffh;8__varmaph<5__with=1ai001ah>3ridi013ridh?1bi021bh@2_HhA2arhB2ghhC2r1hD2r2hE4rid1hF4rid2hG5ATOPRhH5cstr1hI5cstr2hJ5cstr3hK3_H0hL4__x2hM4__x3hN4__x4hO1ihP1qhQ1DhR2RFhS2WRhT3_H1hU3_H2hV2a0hW1ehX1lhY1zhZ2ARh[2C1h\2C2h]2C3h^2C4h_2C5h`2C6ha2Cahb2Cbhc2E6hd2G1he2G2hf2G3hg2G4hh2G5hi2GRhj2Hahk2Hbhl5Hconchm3Hk'hn3Hpwho3Hr'hp3Hrahq3Hrbhr3Hschs2L1ht2L2hu2L3hv2L4hw2L8hx2MRhy2SHhz3Sa0h{3Sa1h|3Sb0h}3Sb1h~2WFi031ki041mi053offi062q0i072r'i082rai092rbi0:2sci0;2sti0<1vi0=1xi0>1yi0?1op%0p%1p%2p%3p&0p&1p&2p;1p;2p;4p;3p;8p;:p;6p;5p;<p;7g006_j14Tg00i7k11UTg00iUk11GTg00R@R0k10gTg00j8k20vTg007bj1ITg00U5j2[Tg00Q?k10sTg00k3k20NTg00l2k10BTg00X?j21Tg007Dj1hTg02ICk10VTg02JHj1tTg02L8j1XTg02M4j1ZTg01kgk10wTg02:>k11ZTg008Gk11=Tg02??j4cTg01CFk107Tg02C=k10MTg03SMk12BTg00N4R1j20Tg00m5k20pTg00n6k20cTg00o8k20bTg0254j2fTg04ULj3NTg028Mj2UTg00:?j39k11<Tg00S\k20ETg004ij2jTg01;Nk11MTg0114j1OTg037Dk219Tg01=bj26Tg03MIk21HTg01KgR2j1;Tg035Tk21{Tg03Mhk40hTg03NDk40jTg04VGk11oTg01]nk20STg04W>k10]Tg03>dk11OTg004Ik117Tg03=nk10dTg02;3k11cTg01[Hk21`Tg01V\k21_Tg03?Zk21^Tg00:Yk41]Tg02Odj1uTg017Yk11?Tg04X4k41>Tg038<k21\Tg03:Fk21[Tg03<<k21YTg02Nfk100Tg02GXj1~Tg01dHk21XTg01dkk31WTg01eoj1HTg01`Zk21:Tg01gfk21VTg019ik20eTg012ck12GTg013Ak12FTg013lk218Tg01:Gk20uTg01hRk31TTg015:k22ETg015\k22DTg016Hk32ATg016gk42>Tg00Vgj23Tg014Ok40XTg01V9k32=Tg04Xdk82<Tg03PXm:2;Tg03QQm:1QTg00Okk40oTg04Y]k429Tg00>fk60`Tg00[Fk427Tg00[dk626Tg00E@k411Tg00?Dk410Tg00\Ek11NTg00]=k60PTg024?k223Tg02;nk222Tg03a5k521Tg00T>j12Tg00YXk10~Tg00UQj2vTg00LEk120Tg03BDj4aTg00Rbj1TTg00V1j1:Tg00WCj1KTg00NOk10QTg00Z1k10xTg003ik21~Tg02`Ak30}Tg04Zek31}Tg02bDk11|Tg02cBk11yTg01fTk21wTg01g=k31FTg012Ek11uTg01QYk40|Tg03e[m<1sTg03f`k81rTg00_Bk11ETg03gck51qTg03IMj4_Tg03kTm:1mTg03lZk71lTg01?]k21tTg03JMk40FTg042Ym:1kTg043`k71vTg01ARk10YTg03RIk30UTg02N4k40[Tg02KEk41DTg008gk30WTg026ak11CTg01Fbm<1iTg01eHk41hTg01nLk324Tg01bkk225Tg01E3k70nTg01GGk61gTg01Gkk71fTg01<0k31PTg01<Sk812Tg03Nck11eTg00Zlk209Tg01:jk715Tg03O\m:1dTg00]Qk31bTg00]nk31aTg00^Kk12?Tg00`;S00k22@Tg00X\k314Tf0R3#4#4#4#hp=Lg00OMR4f1R5'3/03p>0Df5R6f4R7+0pf3R8f2R9+0c20b53'0'0p=Q1053,09p=G1U53#~p=Cf7R:f6R;;N620S95,18$0Y>0U73+0vp=Y&0B5/03p>0@g00;^R<P5g02PhR=P3Ccp>0l%I3#4p=]P<P6P7&008H0[P<P9P5%u3Cc'0p>03P<P8P9P5H0[/03p>0AP<P8P9P5H1D/03p>0IP<P9P5P3H1Dp=sP<P9P5%Z3H0[p>1BP<P9P5&003H0[p>0{P<P9P5%u3Ccp>1Ag00I^R>@0W53p>1;P<P5g03U>P3Ccp>0f%43#4p>0>%43#4#4#4p>16&0w5$1C>0W>3p={P<P5g03V?P3Ccp>0ZP<P5g03W9P3Ccp>0:&1C5>0W>3p>1SP<P5g03X7R?P3Ccp>081053,09,08p>0L20c8920b53'0p>1Rg005CR@/j3p==1f95=9@3p=}%O3#O#O#O#O#O#O#Op>0_g01KHRA?953p>04PAP7P8P9P5P3J0`p=8%t3,65p=\%~3,65p>1n%I3#I#4#Ip=l%43#Ip=k&0Y5>0U93p>0aB0W>53:0W>9p>0C20S95,18$0Y>0U73p>0zP<P9P5P3H0[p>0yP<P9P5P3Cc,08p>1@1053,09,08,07p=d20S53,19p=MP<P9P5P3Ccp>0;A9@53p=?PAP@P3P2P5P9P8P7P6P;P:f8R2N<1ip=DA9A78P9P5P3H1hp=F1U53#~,69p=|%;3,34p=E21:@3p>0?B24@53p=Wg022T-253p>0<g01O8RB@0W53p=`P9g01IIRCg01IhRDPDg01JHREP@P5g01OdRFP3H0Xg01JhRGK0np=VP5PCPDPDPEP3J1gp>0tP9PCPDPDPEP5P3K1fp>0=218@3p=^218@3:1P@5p=wB1P@53p=iP8PCPDPDPEP9P5P3L12p=rg00bcS01g00cCRH793p>2C1343p=<P5PCPDPDPEP3PGK0np>13&1e3#;,15p=y13891353+09p=>P:PCPDPDPEP;P6P7PCPDPDPEP8PCPDPDPEP@P9PFP5H0XPGK0nP3K15L12p=z13950093p>0J1195/33p=5P<P3P5P9P8P7P6P;P:P2N:1dp>0KP6PCPDPDPEP7P8P9PCPDPDPEP5P3K15L12p>0r1353-099p>0q1178/391353+09p=gP;P6P7P8P9P5P3H0oH0op>0RP<P8P9&005H0[/03p>2:%I3#Ip>0O%I3#4#4#4p>281189/350093p=qg00`URI@1b@3p>0HPIg00a3RJP7P8P9%T5J0P=963p=bB1aI@3p=@%:3#Kp=B1v53=9@4p=Sg00eQ&2?3g00fI39p=o1[43p=JA9@54/03,09,08p>0m22@J3p=A1v95=9@4/03p=xPIPJP7P8P9P5J0P=963p=7&0~81053,09'0p>061167/381v95=9@4/03'0p=n20S89,17$0Y1U53#~60U6p=Rg00<SRK@1453p>1LQ01?93H,05p>1KP6g00ccRLP7P8P9&1N5J0P=9;3p=mP6g00gARMP7P8P9&1E5J0P=9;3p=p1v95=9@4/03,08p>1JQ01B14K53;9Hp=P13471189/35/03'0p>0513471389Q01B14K53;9H'0'0p>1I1189/35/03p>0\%43#4#4#4#4#4#4#4p>0113:;1367+0913891353+09'0p>0213781395+09/03p=e%K3,15p>0T%I3#I#I#Ip>0G1395/03p>1zP@P5PFP3H0Xp>0kP8PCPDPDPEP9PCPDPDPEP5PGK0nP3K15p>0i1v89=9@41053'0p>0^&0Y91U53#~60U8p>1p1153$0Yp>1jB0U953-0v8p>1xg00PFg00;9RG#4S02#4S03#4RC#4S04#4S05#4RF$1US06$1GRK&1UC$1GRN$0g[g00?oRO20v89%IGS07#4RP#LRQ,[9-0D9P520v67P1&0s;20N;6&0B6P;P6P;P6P;P6EQ3GP6P7P:P;Q02#IS08#4#LS09,1=RR%hCRCP61C:7GYP3&0s2f9RS00N2&0B2PSP2PSP2PSP2EQ3GP1f:S0:00NSQ0:PSQ0:PSQ0:PSEQ-0@SPSP2f;RTQ0:PRPCPS1CT2GYP3f<RU00NTP1f=RV$0V-0lUPUPR%tVPUQ07#IS0;#4RW#]#LS0<,1=S0=%XVPU%IPRP#4#]#LS0>,1=S0?%ZVPU%IP#]#LS0@,1=RPPVPU%4W#]#LS0A,1=R=PVJ03H0AH0IH0If>S0BPVQ0BPVQ0BPVEQ-0@VPVPUf?RWQ0BPRPCPV1CWUGY[P3Q0B&0VW+0lPWPRf@RX#tPWQ0=%XXPWQ0?%ZXPWPPPXPWP=PXJ03H0AH0IH0IP1fARY#t9sXRPXQ0=%XYPXQ0?%ZYPXPPPYPXP=PYJ03H0AH0IfBS0CPYQ0CPYQ0CPYEQ-0@YPYPXfCRZQ0CPRPCPY1CZXGY[P3Q0C%tZ7sRPZQ0=fDR[#XPZQ0?%Z[PZPPP[PZP=P[J03H0AH0IP1Q0=fER\#X5s[P[Q0?%Z\P[PPP\P[P=P\J03H0AfFS0DP\Q0DP\Q0DP\EQ-0@\P\P[fGR]Q0DPRPCP\1C][GY[P3Q0DQ0=%X]3sP]Q0?fHS0E#ZP]PPQ0EP]P=Q0EJ03H0AP1Q0EQ0?fIR^41BQ0EPPP^Q0EP=P^J03fJS0FP^Q0FP^Q0FP^EQ-0@^P^Q0EfKS0GQ0FPRPCP^Q0GQ0E'CGY[P3Q0FQ0?Q0G41BQ0GPPfLS0HQ0GP=Q0HJ03P1Q0HfMR_80{PQ0H@1A=_fNS0IP_Q0IP_Q0IP_EQ-0@_P_Q0HfOS0JQ0IPRPCP_Q0JQ0H'CGY[P3Q0IQ0J80{PQ0JfPR`81A=fQRaP`PaP`PaP`EQ-0@`P1&0BafRS0KPaQ0KPaQ0KPaEQPaP`fSS0LQ0KPRPCPaQ0L/C`GYP3Q0L$0BP1P<fTRbg03TBRc&0w4Rd$1Z&1=>Re+1;S0MCc&074$0M01;eS0N-0fb&0>F$16S0O#hRf/{eRg-0Zb1{?eR?-0:bp,2rcS0P$2B01SeRh-08bH0LfVS0QfUS0RQ0QQ0RQ0QQ0REQQ0RPbfWS0SQ0QPRPCQ0RQ0S/CbGY[P3P<Q0QPcQ0MCcQ0SQ0N+0fQ0S00ZgQ0S00:?Q0S008hH0LP1fXRcQ0N+0f20Zcg20:c?208ch3GfZS0TfYS0UQ0TQ0UQ0TQ0UEQQ0UPcf[S0VQ0TPRPCQ0UQ0V/CcGY[P3Q0TQ0N+0fQ0V00ZgQ0V00:?Q0V008h3GP1f\S0W00ZgQ0W00:?Q0W008h'0f^S0Xf]S0YQ0XQ0YQ0XQ0YEQQ0YQ0Wf_S0ZQ0XPRPCQ0YQ0ZQ0W'CGY[P3Q0X00ZgQ0Z00:?Q0Z008h'0P1f`S0[00:?Q0[008hfbS0\faS0]Q0\Q0]Q0\Q0]EQQ0]Q0[fcS0^Q0\PRPCQ0]Q0^Q0['CGY[P3Q0\00:?Q0^008hfeR?fdS0_P?Q0_P?Q0_EQP1ffRi00p?PiP?PiP?H1RP?Q0_fgS0`PiPRPCP?Q0`Q0_'CGYP3fhS0aQ0`+0pfiRjQ0aPjQ0aH1RP1fjS0b00cjQ0b00bjPjQ0afkS0cQ0bPRPCPjQ0cQ0a'CGYP3flS0dQ0c+0cfmS0eQ0d+0bg00=URkfoS0f/f3Rl#=WPQ0eQ0dQ0f3N?}3l^PkP0PkQ0ffnR0fqRl3N/U31Ul359KP3frRm20Ek3'U,jKXPkP3O1fpRn&1Mk'U,jKn10110?00021010000Z06OQ0e=N0n/U31Un359K^POg01NYRO%OOS0g#OS0h#OS0i#OS0j#OS0k#OS0l#OS0m#ORo$0_$0_$0_Rp$0_$0_Rq+19Rr,6AS0n2043qX6ARsPqPs1jAqQ0n21HqOD8S0oPAPK%;3Rt-1{l,UlXOARuPrH0h,6KPAPKPuPrH0jD81\Kn004qRuePu1Ul0R0$1o21nN0004oQ0f=NnmS0p$0sQ0p%4G#l#l#l#k#LR0Q09'1Ru20SCnS0q'1S0rQ0f,CmS0s60alRv+0NS0t&0BvS0uQ0p00pvS0vQ0p00cvS0wQ0p00bvS0x'0S0y'0S0z'0Rw'0PjQ0tPw&0]mRw$1OS0{g03AIRxPx&17>R>ftRy$0]$0d$07$0MRzQ0mQ0m$1c+1`R{PxP@P3P4Q02#hS0|%hF+1_S0}%hGS0~+1^RFfsR|fvR}5NyS10PIP@P5P3H1]R~'fn0110=0003000020101105/{e40CPxP@P3P4PF1f}~n0110=0003000020101105/{e:0Cz{39P3&0]|$0d$07$0MRz21Sde80C{,j>1{Fe:0Cz{,j>fwRz$0]$0d$07$0M1fz~/{e80C{,j>Z05@X>IP5P3O2n011020003000020101105b?Q0p$0]Rd$0d$07$0MPxP@&1OdP4PFANmlyS11/f~n0110=0003000020101105/{e80C{&0dw$07$0MPxP@Q0{P4PF1fy~n0110=0003000020101105/{e80C{59>eQ0p#u%um59>R{eP{P>%u|S0{P|PuPCPm1CylS12I0zR{&0Vy+0lR~Q11#t9s{RQ0=%Xy5s{RFQ0?%ZyRx60y{RwB0{{PyRdP{P=P3H1@DdXX>&17KR>PK%t|S13&1?l1U|nS14H1>S15P~As{R3PFPwPdP{P=%uyH1@DdXX>Q0nPsQ0oPAPK21\yt$0wXOARsPrH0h,6KPAPKPsPrH0jD8%X|S0o,6K004qRrePr219OpRr,6ARs2043pX6AR>PpP>1jApPs21HpOD8R{PAPNfuRd01[t$07XOARwPrH0h,6NPAPNPwPrH0jD816Nx004pRxePxPsP>P{PAPN21Y}t$07XOAR{PrH0h,6NPAPNP{PrH0jD8&00d,6N004pRrePrAMuCyS0n1U}|Rr#~S1660adS17&0V}S1880;0Q17PK%t}S19&1?yPrH1>7suS1:Q17Q0<,10S1;%X}S1<3sS1=Q17Q0>,10S1>%Z}S1?40yS1@Q17Q0@,10S1A&00}S1B40yS1CQ17Q0A,10S1D%u}S1E40;S1F'0S1G'0S1H'0S1I'0PdP0Q18Q0nQ16PiQ1B,6NS1JPpQ1J#;RrQ05#hR{'?S05&1<AR>&1<@Rs%;5/?t2045321X5341WZ0>AZ0=ARxQ1JPr%=rPpP{%={S1KM9DP3DFS1LQ05%Zz,6NRrPp%;rS1M/?{S1NP>PsPxPrQ1MQ1M#=PpP{Q1KM9DP9DFS1OQ1NfxS1P#X,6KRrPq%;rRw/?QS1QP>PsPxPrPw%=wPqPQ%=QS1RM9DP7DFS1SQ1QfyS1T=|N}RwPo%;wRr/?CS1UP>PsPxPwPr%=rPoPC%=CS1VM9DP:DFS1WQ1UfzS1X,\KRrPq%;rRw/?QS1YP>PsPxPrPw%=wPqPQQ1RM9DPSDFS1ZQ1Yf{S1[Q1P'CS1\,6NRw#HS1]%EwS1^f|Rw#X,6KRr#HS1_%ErS1`f}S1a$00,6NRr#HS1b%ErS1cf~S1d,\KRr#HS1e%ErS1fp+01@Rr#Z,6NRF#HS1g%EFS1hp-0RF21:@OS1iQ1iQ0h$0?S0h'W$0<+1V&1=BS1j'`S1k&17BRB20e@5S1l&2G@RO&2F@R~218@4S1m20u@GS1n5V~S1o20t~8S1p60=~S1q&1MDRDQ1m%^0S1rQ09'wS09%^CS1sQ1n61T@'iS1t5V~Cr22E~EREP3P9Q01/jH22D39$2CdB2A@45H2>R4b:b;b<X3@W4S01%<3S1u/05S1vAMuC5S1w#<[^3@^4FS1xP31[rQS1yPrPwO3b5bJbIbHb9b8b0b0b0b0b0S1zPoAMuCdRH/1tS1{Q0}'3X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pP@Q1ng01PKS1|%^QS1}H0X-13~S1~60=~S1pPDQ1tQ1s'iS20Q0|#^Q0662=@5V~CrPEP4b:b;b<X3@X4FS061[3QS0|,05S21Q1w/1CS22Q0}'3[^3@^4FS23P3%<rS24PrPwO3b5bJbIbHb9b8b0b0b0b0b0Q16,6NS25P7D8S26Po&0Vz,y0PHQ1{P0C>X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1qPDP~P~Q09Q1t20t~7S27GzPEP4b:b;b<X3@X4FX7FQ1vQ1w>0Ju8[^3@^4F^7FP3AMuCrS28?5C0Q1yPrPwO4b5bJbIbHb9b8b0b0b0b0b0Q18,y0Q0nQ0n%;oS18'1S1yP0C>eQ25P7D8N90KQ1:Q1IQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1jPBQ1lPOP@Q1tg01Q2Q1tH0X-13~PEP4b:b;b<X3@AMuC3R0/?0^3@P3PrO1b5bJbIbHb9b8b0b0b0b0b0Q0nQ0n'?P<P}Pu%tzS1IPd1UzyS1:Q0^Pq1[}t-0D}X6A&00z,6NS29PpQ29#;R0/?{S2:P>PsPxQ29P0%=0PpP{Q1KM9DP5DFQ2:Q1P#Z,6NS2:PpQ2:#;S29/?{S2;P>PsPxQ2:Q29Q29#=PpP{Q1KM9DP8DFQ2;Q1T#X,6KS2;PqQ2;#;S1K/?QS29P>PsPxQ2;Q1KQ1K#=PqPQQ1RM9DP6DFQ29Q1X=|NzS29PoQ29#;S1K/?CS2;P>PsPxQ29Q1KQ1K#=PoPCQ1VM9DP2DFQ2;Q1[,\KS2;PqQ2;#;S1K/?QS29P>PsPxQ2;Q1KQ1K#=PqPQQ1RM9DQ0:DFQ29Q1T9|NwS29#HQ29#EQ1a#X,6KS29#HQ29#EQ1d$00,6NS29#HQ29#E1\KrS29#HQ29#Ep+01AS29#Z,6NS1K#HQ1K#EQ1jPBQ1lPOP~Q1oQ1~60=~S1~PDQ1~CrPEP4b:b;b<X3@S1~Q1uQ0|'01[5Q-0D5[^3@S0|P3Q29Q1aO2b5bJbIbHb9b8b0b0b0b0b0Q1I,6KP;D8L2<b1Q1=Q1HP<PdQ1;Q1<Q0nQ16Q0XQ1zQ26PoQ1;%Xz,6K#;7MCPHQ1{Q1;C>X6APqQ1;?MCtPHQ18,1HS1HQ1;C>X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0<'w5V~J0rPEP4b:b;b<X3@X4FX7FQ21Q22Q1;60q8[^3@^4F^7FP3Q1;20SCQQ2835Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1<,6KP9D8Q25P7D8N:2;Q1@Q1GP<PdQ1>Q1?Q0nQ16Q0TQ1zQ26PoQ1>Q1MPHQ1{Q1>DgX6APpQ1>PtPHQ1HQ1>DgX6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0>'w5V~J0rPEP4b:b;b<X3@X4FX7FQ21Q22Q1>60q8[^3@^4F^7FP3Q1>Q2875{Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1?,6NP5D8Q25P7D8N:1QQ1CQ1FP<PdQ1AQ1BQ0nQ16Q0QQ1zQ26PoQ1AP0PHQ1{Q1ADgX6APpQ1APtPHQ1HQ1ADgX6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0@'w5V~J0rPEP4b:b;b<X3@X4FX7FQ21Q22Q1A60q8[^3@^4F^7FP3Q1AQ2875{Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1JP3D8Q25P7D8N:1QPdQ1DQ1EQ0nQ16Q0RQ1zQ26PoQ1D%uz'yPHQ1{Q1DC>X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0A'w5V~J0rPEP4b:b;b<X3@X4FX7FQ21Q22Q1D60q8[^3@^4F^7FP3Q1DQ04#hR{Q2835Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1DQ1E'yQ0nQ1yQ1DC>eQ25P7D8N90KH0oK0RK0RbvbubtAMuClS25Q14#~Rp60amR0&0V|+0lQ159s0RP0Q0=Q0oP0Q0?%Z|P0PPP|Q0{:0;0=H2:H0AH0I3GeANln|R0#tP|PlPn16NpRpPo%;pRn/?CR=P>PsPxPpPn%=nPoPCQ1VM9DP5DFP=1\KyR=Pq%;=Rn/?QRpP>PsPxP=Pn%=nPqPQQ1RM9DP8DFPp1CdmS0{,6NRp#H%EpQ19,6KRp#H%EpQ1~Q0|P3P}P|O2b5b9b8b0b0H29J0`%u0P3J0`bcQ0teQ0uQ0z%4G#l#l#l$0>#LR0Q0M60;v%kG#]$0O#]$0O$0>$0O$0>$0O#hRpQ0N60;vS0z%4G#l#l#]$0O$0>#LRn>0;vgS0t%kG#k$0>#]#]#k#k#LR=%4G#l#l$28#]#LRP/{eS0|60;vS1~B0;vPhS19'0S0?'0S0o'0PlP0Q0MQ0rQ0sQ0FQ0s,6NRvPo%;vRe/?CS0=P>PsPxPvPe%=ePoPCQ1VM9DP3DFS15Q0=Q13,6KS13PqQ13#;Re/?QR<P>PsPxQ13Pe%=ePqPQQ1RM9DP9DFS13P<Q12,6NRe#HS12%EeS141\KdRe#HS1D%EeS1yQ01Q1xP31[dQS0nPdPmO3b5b9b8b0b0S1EPoQ25/1tS24Q0}'3X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ06Q23P3%<dPdPmO3b5b9b8b0b0PvP3D8S28PoQ0M,y0S0MQ25Q24P0C>X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%^0Q03#hRe'wQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vP0PeQ1wP8Cq[^3@^4F^7FP311HCRe/30Q0nPdPmO4b5b9b8b0b0Q0MQ0rQ0rQ18'1S0MP0C>ePvP3D8N90KQ0zQ0oPlPpQ0NQ0rQ0sQ0DQ1EQ28PoQ0N,ypR0Q25Q24PpC>X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%^pQ0~'wQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPpQ0~Q1wP8Cq[^3@^4F^7FP313epQ0nPdPmO4b5b9b8b0b0P0Q0rQ0MPpC>ePvP3D8N90KQ0tQ0?PlPnPgQ0rQ0sQ0CQ1EQ28Po1yngRgQ25Q24PnC>X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%^nQ1s'iQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPnPCQ1wP8Cq[^3@^4F^7FP313enQ0nPdPmO4b5b9b8b0b0PgQ0rQ0MPnC>ePvP3D8N90KQ1~Q19PlP=Q0|Q0rQ0sQ0BQ1EQ28PoQ0|,y=RnQ25Q24P=C>X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%^=Q1s'iQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vP=PCQ1wP8Cq[^3@^4F^7FP313e=Q0nPdPmO4b5b9b8b0b0PnQ0rQ0MP=C>ePvP3D8N90KPlPPPhQ0rQ0sPVQ1EQ28Po1yPhRhQ25Q24PPC>X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%^PQ1s'iQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPPPCQ1wP8Cq[^3@^4F^7FP313ePQ0nPdPmO4b5b9b8b0b0PhQ0rQ0MPPC>ePvP3D8N90KK0RK0RQ0ueQ0vQ0y&0gLS0yPkPLPkPIg00alRvP@g00dZRPH27RhPIPvg00bEReP@PPg00e3J26RPPLH11S0uPkPhPPPLH10S0MP5Q11$1NJ0P20EL3S0r39PdAN|mdS0nPyPuPCP|Q0{I0zS0{P9P5P;Q1ug02Ah,[3'0g03HVg02@5g02@n;M5-237-22z'jUZ03@PdP9P5Q0dP3I21&0gJR|PIPvPePJH11RmPIPvPePJH10Re&0H8S1uP}20EJ3RvEbS1v%23R<%@8R='1S1w9}}8S27%<=S1t%B3S1q95=fS1l1S=fS1k%o3S1y$0~S1D%J<S141v<fQ1qQ0P$20Rn55<S12H0mRg'0DdX2J#AQ00PJP|PmPe&0H7PzPvEbS13%@7S0=,1<9}z7S15Q0=#<S24Q0=Q1q75fQ0=?xfgDdX2JPzQ1:#~:0a}HS1:P7P8CaP3P|PmPe&0H;Q1TPvEbS25Q1T%@;S28,1<7};S1EQ28#<S0|Q28Q1q75fQ28?xfgDdP1P|PmPe&0H:Q1X#TS1920EJ5S1~E7S0?Q1X%25Rg%@:S0t'17}:S0~Q0t#<S0NQ0tPf%:5R<#KS0oQ0tPf%o5S0z%JgS041SgfRHQ0o=5gnS21H06En3GQ1[Q1XPuPCQ1TQ1\I0zS1\P2P:CaP3P|PmPe&0HS%TwS1X20EJ8E7S22Q1aQ0:%27RpQ0:#@S20'13}S1rQ20#<S0AQ20Pf%B7S1pQ20Pf%o7S1h%JpS1g1SpfQ1p=5pnS1fH06En3GP1Q1d%26Rp%@TS1e'17}TS1cQ1e#<S1bQ1e%B6S1`75fQ1e/vf%o6S1_%JpS1^1SpfQ1`,1pRp/3nS1]H06H0mPrQ1dPuPCQ1aPrPwERS1YPUPTCaP3Q29%2:%@V'17}VS1ZQ0B#@S1U#<S1WQ1U%B2S1Q75fQ1U/vf%o2S1S%22R0#JS1N1S0fQ1Q=50nS1OH06H0mP1%@WS05#<S1LQ05Pf%BSS1{Q05Pf%oSS26%2SR0#JS1z1S0fQ1{=50nS16H06Enp+01DS1Jp+01CS1APuPCp+01BS0@Q1JQ29ERS1HPXPWCaP3%@Y#<Q0C#@S1BPf%BUS1FQ1BPf%oU%2UR0#JS1C1S0fQ1F=50nS1?H06EnP1%@ZS1>%BVS0>75fQ1>%oV%2VR0#JS1M1S0fQ0>=50nS1GH067xfp+01HS1@p+01GS1<PuPCp+01FS1;Q1@p+01ES0<ERS1=P[PZCaP3%@\S1I%:WS1o#KS1K75fQ0D#@S2;%oX%2XR0#JS2:1S0f%BXS2<=50nS2=H067xfP1p+01KS2>$0QP|PmPeP5p+01MS2?PvEbQ04Q21Q0o-1Lg+1K-0D<7GHS2@[^2J^>IP|PmPeP8p+01OS2A#TRH20EJ9S2BE7P|PmPeP9p+01PS2C#TR<Q1~E7A9I68$0~&0x8%28%B8&0x63560Jp[S2D[[^DJ^FI^CJ^EI21~I@RpQ0yPpQ0uQ0MP5Q2?Q0rFmP|PmPeQ1uPHPvE7RHQ1tQ1lQ1kQ1D&0x3Q1w'3DdRg'0X2J#A[^AL]=&0gMS1wPpPkPhPPPMH11S1DPkPhPPPMH10S1kP5Q2?20EM3S1lFpQ1yQ1tQ1q95={S2E1S={S2FH0LR=,0HX2J#A[^BM^?pH0Lp+01LS2GQ2>PuPCp+01JS2HQ2Gp+01IS2IERS2JQ0EP]CaQ0@Q2?$0QP|PmPeP5P<PvE7Q2@[^2J^>IP|PmPeP8p+01RS2K#TR<Q2BE7P|PmPeP9p+01SS2L#TRHQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2CQ0rFmP|PmPeQ1uP<PvE7R</0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2CQ1lFp10<=X2J#A[^BM^?pH0LP1P|PmPeP5p+01QS2MPvEbQ2@[^2J^>IS2NP|PmPeP8PHQ2BE7P|PmPeP9p+01TS2O#TS2PQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2MQ0rFmP|PmPeQ1uPHPvE7R</0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2MQ1lFp10<=X2J#A[^BM^?p3GS2QQ2CQ2APuPCp+01NQ2CQ2?ERS2RQ0HQ0GCaP3P|PmPeP5PHPvE7Q2@[^2J^>IP|PmPeP8p+01VS2S#TRHQ2BE7P|PmPeP9p+01WS2T#TS2UQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2OQ0rFmP|PmPeQ1uPHPvE7RH/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2OQ1lFp10H=X2J#A[^BM^?p3GS2VP5Q0J$0HP^P\O3%2^RH#JPHPf%:^R<%K<R<=5HnS2W21LH<+1K+0DH1JP1Q0F#2R<#JQ0F#:RHP<%KHRHPn1P<HS2XI059x<fp+01UR<Q2OQ2L9MuCS2YQ2K,C<S2Z40aPaP`CaP3Q0H#2S2[#J%2_S2\%:_RHQ2\%KHRHPnQ2\/PHI057xfS2]P1Q0I#2S2^/SfS2_Q0I#:RHQ2^%KHRH'1S2`PnQ2^PHI1IS2ap+01YS2bp+01XS2cPuPCQ2TQ2bQ2SERS2dQ0RPbCaP3%2`S2e/Sf%:aRH%2aS2f%KHRH'1S2gPnQ2fPHI1IS2hP1Q0K#:RH#<S2iQ0K#2S2j%KHRHPnQ2j/PHH0\S2kp+01]S2lp+01\PuPCp+01[S2mQ2lp+01ZS2nERS2oQ0UPcCaP3%:b#<Q0R#2RHQ0R#:S2p#KRPPn1PHPH0\S2qP1Q0Q#2S2rQ0Q#:S2s#KS2t'1S2u/3nS2vQ2rQ2t'PS2wp+01aS2xp+01`PuPCp+01_Q2xp+01^ERS2yQ0YQ0WCaP3%2c%:cS2z#K;5nQ0U#2S2{Q0U#BS2|'PS2}Q0T#2S2~Q0T#BS30<0}3Q2~Q30'1S31Q0O#4#LS0OQ03#IS03$0>$01#LRPQ2~Q31PP%kG#k$0>$01#LRHQ2~Q31PH%kG#k#]$01#LRhQ2~Q31Ph%4G$0O#]#]$01#LS32Q2~L02DeDeP1Q0V#2RGQ0V#:+0TR0Q0OPPPGC>P0PPPHPGP0PHPhPGP0PhQ32PGL02Dep+01fS33p+01eS34PuPCp+01dS35Q33p+01cS36ERQ0\Q0]CaP3Q0Y#2S37Q0Y#BS38Q0OPPQ37DgQ0X#2S39Q0X#BS0X'1S3:PPPHQ39Q3:PHPhQ39Q3:PhQ32Q39L02DeS3;p+01iRGp+01hR0p+01gS3<9MuCQ33,CGS3=P?Q0_&0sG20NG0&0B0PGP0PGP0PGP0EQ3GQ3441}Q0^Q0P$1|S0PQ0;$0G$0G$0GS0;#4$0G$0G$16$01$01#LQ0;#I$0G$0G$16$01$01#L,3n81znS0;Q01Q1xP31[GQPGQ33O3b5bGPoAMuC0S3>/1tS3?Q0}'3X6AQ0PQ0;Q06Q23P3%<GPGQ33O3b5bGQ3=,6NS3=PiD8Pop+01jS33/fiS3@PfQ3>Q3?Q3@DgX6AP@Q0Z#2S3@%@?'1P3PfQ3>Q3>Q18'1S3?P3DgXY@Q0Z#:S0Z$1yQ0ZQ0Z#KS3A'3Q0PQ0;p+01kS0Z=|N0S3BPoQ3B#;R0/?CS3CP>PsPxQ3BP0%=0PoPCQ1VM9DQ0aDFQ3Cp+01lS3C,\KS3BPqQ3B#;R0/?QS3DP>PsPxQ3BP0%=0PqPQQ1RM9DQ0bDFQ3Dp+01mR0Q33'CS3D,6NS3B#HQ3B#Ep+01nS3E,\KS3F#HQ3F#EQ0l$0?S0lQ0j$0?S0j21w@CS3FQ0h61F@Q1i'W'WS0h'W$0<S3GQ0m$0?S0mQ0k$0?S0kQ3FQ0i$0?61F@Q0g$0?S0g'WS3F'WS0i'W$0<Q3GQ0lQ0i'W$0<S0iQ1j'`S3H'`'`'`PBP@20e@9S3IP5P@20e@7P8&1u@H0|H0|S3JPOP~20t~;P~P~Q1nQ08-0u@S08'iS3K%^HS3L+0k%^hS3MQ1n5V~S3NH0iP~P~Q3KQ3M+0kQ32#^Q1n5V~S3KH0i60=~60=~S3OPDP~Q02-0u@S02%^fS3P'iQ085V~PDP~Q1mQ025V~S3QPDP~Q1mQ07-0u@S075V~P@Q07Q1|Q1}H0X-13~60=~S1}PDP~P~Q1nQ02'iS1|Q3P'iQ09Q1sQ0761T@'iS09Q09Q1s'iS1sQ1|5V~S07GzCrCrCrPEP4b:b;b<X3@XL@XM@XN@X4F1138S3P13h3S1m80JHQ3PQ32/33S3R80Jh5G7S3PA59f7%<8S3S1[6Q-0D6S3T1176S3UPfAMuC;S3VQ3VQ3U75CS3WCq[[[[^3@^L@^M@^N@^4FP3%2iS3X%BiS3YPPPHQ3XDgQ3YQ3EQ0d#@Q3XP:Q0QQ0TQ0ZO9b5b9b8b0b0bGQ0[#2%@i'1S0TPfQ3>Q3?Q0TDgeb11fG?Q0SJ0`Q3=PiD8Q0fP?Q0_Q0^O3N<1sWQW@P5P3O2n2001000000121000000bVWRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000bVWKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000W@W{P5P3O2n2001000000121000000W1WzP5P3O2n2001000000121000000W1WaP5P3O2n2001000000121000000W1WpP5P3O2n2001000000121000000W1Z08JP5P3O2n200100000012110=000bWL1rWjXALX=kQ0veQ0wQ0xQ1wPkPMQ1DQ1kP5Q11$1EJ0PQ1l39PdQ0nQ0{P9P5P;PdP9P5Q0dP3I1qQ1vQ27Q1yQ1tQ2EQ2FQ14Q12'0S123GDdX2J#AQ00PJQ13Q15Q1yQ24Q0=P{Q1qQ0=P{Q12EnDdX2JPzQ1:P7P8C_P3Q25Q1EQ1yQ0|Q28P{Q1qQ28P{Q12EnDdP1Q0?Q0~Q0zQ0NQ0tQ0o75{Q0tP{Q04Q21H0^DdQ1[Q1\P2P:C_P3Q22Q1rQ1hQ0AQ20Q1p75{Q20P{Q1gQ1fH0^DdP1Q1cQ1_Q1bQ1eP{Q1`Q1eP{Q1^Q1]'0En3GPrQ1YPUPTC_P3Q1ZQ1SQ1WQ1UP{Q1QQ1UP{Q1NQ1O'0En3GP1Q26Q1LQ05Q1{75{Q05/v{Q1zQ16'0H0mQ1JQ1HPXPWC_P3%oTQ1BQ1BP{Q1FQ1BP{Q1CQ1?H0^I05P1Q1>#<Q1>P{Q0>Q1>P{Q1MQ1G'0EnQ1@Q1=P[PZC_P3Q1I#<Q2;P{Q2<Q2;P{Q2:Q2='0EnP1%@]S2=%BYS2:75{Q2=P{%2YS2=#JQ2=Q2:;5nH0^Q2GQ2JQ0EP]C_P3%@^%:ZS2J#KS2:75{Q0F#@P{%2[S0F#JQ0F%B[;5nH0^P1Q2A$0QQ2NQ2Q'0Q2CQ2RQ0HQ0GC_Q1;Q2M$0QP|PmPeP5Q2PPvE7Q2@[^2J^>IQ2V'0P1P|PmPeP5P<PvEbQ2@[^2J^>IP|PmPeP8Q2UQ2BE7P|PmPeP9Q2cQ1~EbQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5P<Q0rFmP|PmPeQ1uQ2UPvE7S2V/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5P<Q1lFpQ2V/0=X2J#A[^BM^?p3GQ2OQ2LPuPCQ2KQ2OQ2MERP`Q0JC_P3P|PmPeP5Q2UPvE7Q2@[^2J^>IP|PmPeP8Q2n#TS2nQ2BE7P|PmPeP9Q2mQ1~EbQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2cQ0rFmP|PmPeQ1uQ2nPvE7S2n/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2cQ1lFpQ2n/0=X2J#A[^BM^?p3GP5Q0L$0HP_P^O3Q2\#JQ2]'0P1Q2^#JQ2_Q2a'0Q2bQ2dQ0RPbC_P3Q2e#JQ2fQ2h7xfP1Q2j/SfQ2iQ2k'0Q2lQ2oQ0UPcC_P3%2b/SfQ2pQ2q+0DP1Q2s#<Q2vQ2w'0Q2xQ2yQ0YQ0WC_P3Q2z#<Q2{Q2|PnQ2}H0\P1Q31/3nQ2~Q30'PQ34Q35PuPCQ36Q34p+01bERQ0]Q0[C_P3Q0W#2Q0W#B;5nQ37Q38'PQ39Q0X<0}3Q3:Q0OPPQ39Q3;DeP1Q3@Q3A'1RbQ0OPPQ3@C>PbPPPHQ3@PbPHPhQ3@PbPhQ32Q3@L02DeQ33PGQ3>Q33Q3<H1pPiP?C_P3Q0]#2R?Q0]#:+0TQ0OPPP?C>Q0\#2R?Q0\#:+0TRiPPPHP?PiPHPhP?PiPhQ32P?L02DeP0Q3CQ0Z9MuCR?Q3DPjQ0aQ0PQ0;Q01Q1xP31[0QP0Q33O3b5bGPoQ3C9MuCRi/1tRGQ0}'3X6AQ0PQ0;Q06Q23P3%<0P0Q33O3b5bGQ3BQ0bD8PoQ3EQ0b'fRbQ03#hRcPiPGPbDgX6AP@Q0^#2%@j'1RbP3PcPiQ18=5i3CqXY@Q0PQ0;Q3EQ0Z5|NRiPo%;iRG/?CS0ZP>PsPxPiPG%=GPoPCQ1VM9DQ0cDFQ0Zp+01o,\KRGPq%;GRi/?QS0ZP>PsPxPGPi%=iPqPQQ1RM9DQ0eDFQ0Zp+020=|N0Ri#H%Eip+021Ri,\KRG#H%EGQ3GQ0iQ0mQ0lQ0kQ0j'W'W'W$0<Q3H'`'`'`PBQ3JPOP~Q3OPDP~Q02/w{Q085V~PDP~Q3QPDP~Q1}PDP~P~Q1|/wcQ09Q07GzCrCrCrPEP4b:b;b<X3@XL@XM@XN@X4FQ3PA59{7Q3SQ3TQ3UPcQ3VQ3WCq[[[[^3@^L@^M@^N@^4FP3%2jR{%BjRGPPPHP{DgPGPiQ0f#@P{P;Q0RQ0UQ3EO9b5b9b8b0b0bGPbPcP?Q18=5?bCqe1f0jQ0VJ0`Q3BQ0bD8Q0fPjQ0aQ0`O3N:1mWQW@P5P3O2n2001000000121000000b=WRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000b=WKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000WKW}P5P3O2n2001000000121000000W1W|P5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000W1WbP5P3O2n2001000000121000000W1WqP5P3O2n2001000000121000000W1Z09JP5P3O2n200100000012110=000bWK1lWkXBMX?kQ0weP|PmPeP5Q11PvEbQ0zQ10Q10Q17P8P9g03KNQ1001t8'jP1&0Q}P|PmPeP5Q1PPvEbQ2@[^2J^>IP|PmPeP8Q19Q2BE7P|PmPeP9Q1[#TR}Q1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q1PQ0rFmP|PmPeQ1uQ19PvE7Rk/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q1PQ1lFp10k=X2J#A[^BM^?pH0LANdyzQ1:P7P8H0FQ0eQ1P$0QP|PmPeP5P}PvE7Q2@[^2J^>IP|PmPeP8Q1a#TR}Q2BE7P|PmPeP9Q1d#TRdQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q1[Q0rFmP|PmPeQ1uP}PvE7R}/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q1[Q1lFp10}=X2J#A[^BM^?pH0LP1P|PmPeP5Q1XPvE7Q2@[^2J^>IP|PmPeP8PdQ2BE7P|PmPeP9PrQ1~EbQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5PwQ0rFmP|PmPeQ1uPdPvE7R}/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5PwQ1lFp10}=X2J#A[^BM^?p3GQ1TQ1PQ1[3NQ1\P2P:H0FP3P|PmPeP5PdPvE7Q2@[^2J^>IP|PmPeP8Q0@#TRdQ2BE7P|PmPeP9Q1AQ1~EbQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5PrQ0rFmP|PmPeQ1uPdPvE7Rv/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5PrQ1lFp10v=X2J#A[^BM^?p3GP5PTQ0:PSO3Q0:#2RS#JPSPfQ0:#:RpPS%KpRpPn1PSpI05H1JP1%2TRp#J%:TRTPp%KTRTPn1PpTI059xpfQ1dQ1aQ293NPrPuPCQ1dQ29Q1aERPVPUH0FP3Q1MQ0B#2RUQ0B#:RVPU%KVRVPn1PUVI057xfP1%2WRW/SfQ1oPWQ1KPnQ1K,PWI05Q1AQ0@Q0<3NQ1JPuPCQ1AQ0<Q0@ERPYPXH0FP3Q2=/SfQ0C#:RfQ0C#2RX%KfRfPn1PXfI05P1Q2J#<%2ZRZQ2:PnQ2:,PZH0\Q1<Q1;Q2I3NQ1@PuPCQ1<Q2IQ1;ERP\P[H0FP3%:\#<Q0D#2R\Q0D#BR[Pn1P\[H0\P1%2]R[%B]R];5n1P[]Q2>Q2HQ2?3NQ2GPuPCQ2>Q2?Q2HERP^Q0EH0FP3Q2WQ2XQ0G#2R^Q0G#BR]<0}311^]R]Q0OPPP^P]PPPHP^P]PHPhP^P]PhQ32P^L02DeDeP1Q2[Q0H#:+0TR1Q0OPPQ2[C>P1PPPHQ2[P1PHPhQ2[P1PhQ32Q2[L02DeQ2CQ2AQ2K3NQ2MPuPCQ2CQ2KQ2AERQ0IP_H0FP3Q2`Q0OPPQ2^C>Q0J#2R_Q0J#:+0TR1PPPHP_P1PHPhP_P1PhQ32P_L02DeQ2LQ2K;N<Q2OQ2YQ2ZPaP`Q0PQ0;Q01Q1xP31[<QP<Q2KO3b5bGPoQ2O9MuCR_/1tRtQ0}'3X6AQ0PQ0;Q06Q23P3%<<P<Q2KO3b5bGQ2Z,6NR1Q0KD8PoQ2gP_PtQ2fC>X6AQ0PQ0;Q2SQ2L5|NRAPo%;ARt/?CR_P>PsPxPAPt%=tPoPCQ1VM9DQ0LDFP_Q2T,\KR_Pq%;_Ro/?QRtP>PsPxP_Po%=oPqPQQ1RM9DQ0RDFPtQ2c=|N<R<#H%E<Q2b,\KRK#H%EKQ0h$0<Q0jQ3F'W$0<RKQ0kQ0jQ0gQ1i'W'W'W$0<Q1j,`K'`'`'`PBP@Q3IP520e@8H0|POP~20t~6P~P~Q1|Q3L+0kQ3NH0iP~P~Q1|Q3M+0kQ3KH0i60=~60=~PDP~Q1}PDP~P~Q1|Q09Q1sQ1n5V~GzCrPEP4b:b;b<X3@XL@XM@X4F1135R4Q1m80JHQ3R:0J4h5G8Q3S1[8Q'0P9P8AMuC7RuA5uC9Cq[[^3@^L@^M@^4FP3Q2uPPPHQ2rC>Q2bQ2tQ2rP;Q2SO6b5b9b8b0b0bGQ2e%:`+0TQ2YQ2YQ18Q2e3540JeP1Q0KD8Q0QPaP`Q0JQ0IO4N:1kWQW@P5P3O2n2001000000121000000b=WRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000b=WKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000K1vWmWoZ07JX>IQ0xeH0oK0RK0RQ0pPlQ0q-1jRQ0sH1xebwbsbnblWyWiP5P3O2n2001000000121000000W1WZP5P3O2n2001000000121000000W1WhWgP5P3O2n2001000000121000000W1WfP5P3O2n2001000000121000000W1WeP5P3O2n2001000000121000000W1WdP5P3O2n2001000000121000000W1P5P3O2n2001000000121000000W1W`W_P5P3O2n2001000000121000000W1W^P5P3O2n2001000000121000000W1W]P5P3O2n2001000000121000000W1W\P5P3O2n2001000000121000000W1W[P5P3O2n2001000000121000000W1P5P3O2n2001000000121000000W1W~P5P3O2n2001000000121000000b1WrWxY0<Z0:@Y04Y0;o"). Qed.


Lemma rshadow_rep_le : forall st st' m rid r,
  shadow_le (get_shadow st rid) (get_shadow st' rid) -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.

(* [comment removed for export] *)
Lemma rmrep_upd_shadow : forall st m rid f,
  rmrep st m -> ticks_ok st ->
  (shadow_le (get_shadow st rid) (f (get_shadow st rid)) /\ sh_ticks (f (get_shadow st rid)) (s_tick st)) ->
  rmrep (upd_shadow rid f st) m /\ ticks_ok (upd_shadow rid f st).
Proof.
  intros st m rid f MR TK [HL HT]. pose proof MR as (WF & CX & GL & AR & GR & SH).
  assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
  assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
  { intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
    destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
  split.
  - split; [exact WF|]. split; [eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX]|]. split; [exact GL|].
    split; [intros a ar Ha; eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
    split; [intros b gh Hb; eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)]|].
    intros rid' r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
    rewrite GS. destruct (N.eqb_spec rid' rid); [subst; exact HL| apply shadow_le_refl].
  - destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
    + intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
    + intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.

Lemma rmrep_havoc : forall st m p n, rmrep st m -> ticks_ok st -> rmrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof.
  intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
  set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
  - destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
    set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
    assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
    { subst hav1. destruct (snd p <? _); [apply havoc_units_le; exact T0| split; [apply shadow_le_refl|exact T0]]. }
    destruct S1 as [L2 T2].
    set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
    assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
    { subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; exact T2| split; [apply shadow_le_refl|exact T2]]. }
    destruct S2 as [L3 T3].
    destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
    split; [|exact T4]. eapply shadow_le_trans; [exact L2|]. eapply shadow_le_trans; [exact L3|exact L4].
  - apply havoc_units_le. exact T0.
Qed.

Lemma rmrep_hdr_havoc : forall st m b, rmrep st m -> ticks_ok st -> rmrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof.
  intros st m b MR TK. unfold hdr_havoc.
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
  set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  apply hav_unit_step. exact T0.
Qed.


(* [comment removed for export] *)

Lemma rmrep_transport_high : forall st m m' W,
  rmrep st m -> munch W m m' -> wmono usegs m m' -> W_high W -> rmrep st m'.
Proof.
  intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (D : forall a n, a + n <= ATOP -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).
  atop_facts.
  assert (TC : forall A cs, rw_cells usegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells usegs m' A cs).
  { intros A cs RC HB. eapply rw_cells_transport; eauto. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | unfold RCTX; cbn; lia].
    + eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + apply TC; [exact C6 | unfold RCTX; cbn; lia].
  - (* [comment removed for export] *) destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 | unfold RMLOCK; cbn; lia].
    + apply TC; [exact G2 | unfold RNEED_LOCKS; cbn; lia].
    + apply TC; [exact G3 | unfold RPAGE_SIZE; cbn; lia].
    + apply TC; [exact G4 | unfold RGOT_SSP; cbn; lia].
    + apply TC; [exact G5 | unfold RSSP_GUARD; cbn; lia].
  - (* [comment removed for export] *) intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3).
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
    split; [|split].
    + apply TC; [exact A1 | cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
    + apply TC; [exact A3 | cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC). atop_facts.
    apply TC; [exact R | cbn; lia].
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _). atop_facts.
    split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed.


(* [comment removed for export] *)
Lemma rmrep_set_tick : forall st m t, rmrep st m -> rmrep (set_tick t st) m.
Proof.
  intros st m t (WF & CX & GL & AR & GR & SH).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity | intros; reflexivity | exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.


(* [comment removed for export] *)
Lemma rwr_at_bytes_exist : forall m a n,
  wr_at usegs m a n -> 0 <= n -> (a + n <= 0x10000 \/ 0x5d000 <= a) ->
  exists bs, length bs = Z.to_nat n /\ bytes_at usegs m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h04__x1h14__x2h22bsh37__arithh44__ffh58__varmaph65__with74__x3h82H1h91ih:2z1h;3Hk0h<4__p1h=1bi001bh>4cstrh?1xi011xh@1HhA2L0hB2HihC1WhD5cstr0hE1mhF4__p2hG6__sat2hH4__x4hI1khJ1yhK1zhL1BhM1ahN1ehO1ni021nhP1oi031ohQ2HahR3Hi0hS2HkhT1LhU6__sat1hV4__x5hW3bs1hX3bs2hY4segshZ2A0h[2Anh\1Gh]2H2h^2Hbh_4Himgh`2Hnha2IHhb3REChc5cstr1hd2z2p%0p&0p;1p;4p;2p;3p;6p;<p;5p;7p;8p;Bg006_j1ETg00i7k10CTg00iUk10?Tg00R@R0k10wTg011Sk40eTg007Dj1lTg01V\k20YTg01;Nk10LTg00N4S00j2<Tg007bj1gTg00VgS01j23Tg00Zlj2]Tg004Ik101Tg01=bj2;Tg017YR1j1@Tg00`;S02j2=Tg00X?R2j20Tg01ARj1kTg02eDk20WTg02elk30STg02fPk20RTg004ij2aTg0114R3j14Tg01`Zj2hTg008Gk10:Tg019ij2tTg012ck10vTg013Ak10uTg013lj2oTg01:Gj2qTg015:k20bTg015\k20aTg00:?j38k10;Tg016Hk30`Tg016gk40_Tg01i5k20GTg01V9k30^Tg05G:k20FTg00>fj6mTg05H2k30]Tg00>Jk60DTg00S\j2xTg01cWj4wTg02hOk20\Tg05I3k30ZTg018PR4j2DTg01KgR5j11Tg01_dR6j2_Tg05J2j3dTg01eHj4ATg012Ek10VTg05JPj3vTg00U5R7j2NTg01eoj1JTg00Okj4YTg01=7j4ZTg03?ZR8j2?Tg01`<k105Tg01Fbl<OTg01k>k60QTg01dHk20PTg01dkk30OTg008gj3LTg01aCk10MTg01aak20UTg01bBk30KTg01R7j3{Tg01D>j4FTg01RTk50tTg01?<k10rTg05K3k40oTg05KTk30lTg00YXk10kTg01nLk30HTg01bkk204Tg01QYk40jTg014Ok402Tg01E3k703Tg01Gkk70iTg01<0k30hTg01:jk70gTg01<Sk806Tg05LQk307Tg018jk20fTg01EWm<08Tg019Gk20pTg01GGk60dTg03c6k40cTg01F<mB0ETf0R9#E#Ep>0Jg00OMR:/39p=5f2R;f1R<'0/39p=>1N<9,<;p=[10<9#kp=ug00;^R=@0l<9p=cA8;<9$0kp=V%E9#E#E#Ep=pP=P;P<P9CFp=Bg01KHR>?8;</<9p=e1N:9p=jg005CR?@0H<9p=^g01O8R@B0H?;<g022TRA+04;L9p=KP?P;P<P9H0jp=WP;g01IIRBg01IhRCPCg01JHRDP?P<g01OdP9H02g01JhREK03p=7P?P<g01PKP9H02p=sP<PBPCPCPDP9PEK03p=rP;PBPCPCPDP<P9K0ip=TB0h?<9p=IP;PBPCPCPDP<P9K0gp=nf6RFPBPCPCPDf5RGf4RHf3RIPBPCPCPDP;P<P9L06L06p=HPIPBPCPCPDP;P<P9L06p=fB07=<9p>0[B07=;<=8I9p>0BA8><9p=C1?<9,0;p=9P=P;P<P9CF,<Ip=|10;<#k:07=I=8H9p=S20f:9p=61a?9p=2P?P>P?P?P1PHP5PIg01LGP;P<P9N<08p=RP>P?P4P5Q01g01N7R1g01NYRJP:PIP;P<P9M<Op>0A20p:9p=U1N:HA8?I;'<13<:A8?9:'<']p=X2049Ap>0XAL@<9p>0@P>P?P6P5P7g020KRKPIP;P<PJP:P9M<Op>0TP<PBPCPCPDP9J0dp=iP>P?P4P5Q01P1PGPHPIP;P<P9M<Op=`P>P>P?P?P3P5P5PIg0220P;P<P9N<08p=QA8>GHP=PI10;<P9CF'<p=P%19,?<p=GP=PI10;<P9CFp>0>P?P?g045IP9H0cp>0=P>P?P?P?P5P5PGPHPIP;P<P9N<08p>00P?P?P?P?P?P?P8P9P<P;P8PIPHPGPFf7R8f8R3f9R1NB0Ep=yP?P?Q01PGQ01PHP:P:PIP;P<P9M<Op>0<A8?<9p=:P>P?P9P5P<P;PIPHPGPFP8P3M<Op=b%19,3:p=\P;PBPCPCPDP?P<g01Q2P9H02PEK03p=MA8?9:p>0NA8?;<,<I/]9p=}139:p>09P=PH%1<,?;,0IP9CFp=zP?P?P?P?P?P?P2P9P<P;P2PIPHPGPFP8P3P1NB0Ep=~A8?9:,<<p>0sP>P?P6P5P7PKPGPHPIP;P<P9M<Op>0q10;</09p>0I204<A=L@9p>0n13<:/<9p>0mg00;9RA#ERK#ES03#ER5#E$0JR6$0CR2$0?&0C5$0?R5$0wRE[S04P=P;P<P9H0eQ00%5;RB%lKR4%l6RL+0YRM9>;<%59RN?[9;1uH<,cG&0L5RO5VE[^9?'<&0J6#p#p#lR69>HI%EA#g#g#g#E#g#p#p#p#lRP/3H']&015RQ1;59RR%@GAB8F93eX2Q'=[\BP9%5HS05A>GHMA[N9G1u8<,c3=VEO[^9?'<Q00A>FGMA[N9F1u3<,c1=VEO[^9?%5F1038RS/3613P3']%@1f;RTf:RU;B95eRX2Q,=Q[[P913SMA[N91f<RS1uT<'c=VEO[^9?%51A>TU613PT']A[N9SRVPHP<P9O2f?RWf>RX/u<'c=VEOPEf@RY10W;RZ#kR['cAVE9OR\XPEP9PYP[O1R]P?PZ%lAR^,09R_/3613P9']XK?R`20W4LRa%j4Rb%5L%jM[Rc[Rd%54Reg02g1RfB0S4L<UWQRL%5M\f^QeReP<g02gM20R:4'aPbeO1RbPc%4JRf#4Rg#4Rh,h?Ri1h?gRg1h?fS06'^%4hS07,h?S081h?JS09,^gRh&0:@Rj3KRk3K&01@R@1t?;Rl1t?IS0:7W<S0;&0v?Rm&0u?Rn1o?:Ro1q?KRp57nS0<%gA,q?Rq,sp,rn5TnRr&0LCRCPn1q?ARs/IqRt1o?6Ru57n1o?PRv=7ns5nnPC1IspRw1o?^Rx'I=7nuA7nvw5nnFH20bnDRDP9P;g00bcRvg00cCRu'a20a9;=8vudB0`?:<H0_Rub4b5b6X0?X1?X7?Rv%5<Ry?[<;Rz10<IR{/3613P<']10;IS0=?>^6Q0=,3P'][[^0?^1?^7?RPP9fBR6PFfCR|PGP8O5b3bGbUbG20G2[Q08Q06Q09'^S0>;Kj9KihP@Q0;PmPnPrPCPn1o?4>0^?2R497ntPCPnA7nosS0?PCA7now1sw4,rn5TnCfFHPDPub4b5b6X0?X1?X7?Rt13{M10IHR{#5?[{M\B[\z^0?^1?^7?RzP9PWPIPYP;P8PTO6b3-0FZEm:0]Y[J0DAVE]OPEfAR]10YIRZ#kR{O1Rr1x59Rh98E<X=5,=5XPEPrPEP0P5A8E;hX=5,=5^C\P9AVEhOP51x5;=8EhX=5P<1x5<,aECwWCX=5P9O1AVEOOA8EOhX=5,=5P91aEOO1+0\WCn10110300021010000P<O1bP20[]{P?PZP`PaPdPLPePbPcPvPPP9P|P8fDRPPFP3O5b3bGbUbG20G2{PtPzP9PYPHP]PIP3PSO6b3-0FZEm:0Z]{EmbCbCWBX9?PEPYP[PhH0BX=5,=5\V^9?%@XS0@,D91CR;S0AP6%1;RV99]YP9C|X2Q,=Q[S0BXI>f=R[#@R{,DJPQA8>RJP]%1JRZ99YWP9C|X2Q&0:5Rz1;5zRt=8>JA9WXZR2=BYz1a>J%52%1t=>2MR21_9tRtPEP6A9]YZ%1<RvAd5z<DS[^9>Rc'<Q0@,DJ%6XS0C#5Rb1a?:S0DQ0@%69X??RePXO1P9X??RLPePXPX%2XDRH0AP9CARdPb%UWRaPW%6WR`PWPWP`DXR`%6YROP?Q0>,^gS0E$0XS0F00@jP@&0V?R\9Wl<S0GPmPnQ0<PCPnQ0?PCAv?po,IsR097noFHPDPub4b5b6X0?X1?A9;I:#5\y\y^0?^1?P9P6P|P3PXO4b3b:b8b;P2PcPdPbPaP`POP?PjP@Q0GPmPnA7nw4S0HPC1I0o=7n4CfPDPub4b5b6X0?X1?A>9<MA9<;:?>:M[^0?^1?P9P6P|PUO3b3b:b8b;P2e1_<J1Nv:R2P<Pv%2vS0IQ0DH0TP9CAP2%@]S0J,DJ%6]#5R2Q0DQ0JPeP]O1PLPeP]P]%2]DRH0APICAP2%JIR2%1IR0#5Rw%U|P|%6|R`P|P|P`DX%6PP?p-0RaPjP@1t?<S0K9W\<S0LPmPnA7noqS0MPCPn1sqo,rnPC1inIS0NFHPDPub4b5b6X0?W<1N<:PI[\N^0?^<aP9PEfHRbfGRdfFRc;9Z%18RyAd5z8DSPyPIPGO4b3b:b8b>b;bRXBtX9>CYCYCYCwWSQ0B%4<S0O%@WS0P'DP<%@YRt,D;13VOP;PV%2VRrPtPOPLPePYPY%2YDRR}E`%4;R~/DtA>V^OROP~P_X??R~PVO1P~P;PVPrCQPtPePYO1P}E`P9CAPOP2Pw%U6P6%66RwP6P6PwDXP`P?PjP@Q0GPmPn1IsxS0Q=7npPCA7nspCfPDPub4b5b6X0?X1?13_<13<;[^0?^1?P9P<PyPHO3b3b:b8b>b;CZO1PRPIP|P61?]0P9EPX2Q,=QQ02PQPRPHPPP|%1HS0R,?6P9EPX2QPR%4GR0fER_PP1G|0P9EPX2Q,=QP9PRPFPcP_1GPFP9EPQ001;5<S0S/C8PdPc1?_yP<H0>PR%41RyfIR0Pb1GdyP9EPX2Q,=QP91;5IS0T/C1fJR1P0%1US0U,?bPHH0>P[%4TS0V#1S0W,?0Ry%5yS0X1Ny0R`'<%1TRw/0^R2,?0RO#5R}1NO0Rr'<Q0XP`P}PrPL13<9$05XJ?X??S0XQ0DPyPOPLPLPL1?<9$0=#2XE?XO?S0YP0P0%20RrQ0WP2PLPL%19R}#2X?>S0WQ0VP2P~PTPw%2wR2CQJ00M:yR`J0<P?P?P7PLP71N<9$05XJ?X??PyPOP`P0P0PrM<OJ0Q1;5GRr/CT%1rR`/:wRO&0;>S0V&0;?Ry1:v}1C<920P<940OXJ>X?>S0ZPrP`%2`S0[PTPwP2M9bP<CAPO%4SRO%@1R2'D%1SRw%617>^R}POP~PwO1P~PSPw%2wCQP2PeP1O1PLPeP1P1%21DRE`PUCAP}%J[%\[1;53R}#J%\}fMR}#UP}%6}R2P}P}P2DXfNS0\#6P?Q08Q0E;KkP@Q0:?WI\9Wl<PmPn1inGS0]%gK,q?RK=Mns5Tn1inFAMnKoS0^5Tn5nnPCPnQ0<PCPn1IpxS0_=7nKPCPnQ0?PCQ0_9v?sRl97no1sls,rn5TnFHFHPDPub4b5b6X0?X1?X7?X<aXFaPIP;P9&0N;S0`,<HC}A>I^H%5IS0a10G^,?HS0b#5Q0b;[H[[\B[^0?^1?^7?^<a^FaP9fPRl$09%jlP<%16RkPlP;PHPGPcO9b3b:b8bDb>b;bACZO2PEfLS0cfKS0d1G1OPhDSX=5,=5Q02P5PEP}Q0cQ0d%4['GPhDSX=5PR%4XROQ0\P}Q0c/GOP9EPX2Q,=QP9PEfOROQ0\%4W,G}PhDSPQ%4]RhfQR}%1hS0e,?OS0f,0lR2;B95eRX2QAL5<URw1;5w%4YS0g'CS0hPlPOQ0\Q0gPwDz1;5URw#4S0iQ0g'C%1wRS/0^S0j%1YR7/0^S0k':Q0VPyQ0ZQ0iQ0jP~PwPS%2SS0jCQQ0gQ0kP~PYP7%27S0kCQM9b1CwY1:S7S0gQ0VPyQ0ZPwPSQ0jPYP7Q0kM9bPFCAQ0g%@OR7,Dh%1]RS/0^S0g%6O'3RwPhP~PSO1P~P]PS%2SS0kCQS0jP7PePOO1PLPePOPO%2OS0iDRE`PWCAPw%J6%5k1;5[Rw#J%\wfRRw#UPw%6wR7PwPwP7DXfSR7#6S0lP?&0MA-0U?S0mQ0660K?Q09;KjP@Q0GPmPnAMnspPCQ0QQ0_5MnCfPDPub4b5b6X0?X1?1:9<10<^S0_10;^S0Q':[^0?^1?P9%1dS0G1;5]S06#1RAPFO3b3b:b8bDb>b;bACZQ0heg01SM$01S0hQ04Q00PHPIP;A{5<9CFPGPHPIP;CFPGPH1;5;#1,0IP<CF'<S0n[PHPIP;P<CFPHPIQ0S#1,0;P9CF'<PGPHPIA{5;<CF[S0oQ0nPFPGPHA{5I;CF[PHPIP;P<P9I0tP9n2001000000120000000XXQXWQXM?WEWYQ0hQ04Q0o^XQ^WQ^M?]E]YP9P=P}P2AL5;zR=PTAB}2=1;5=#1,02R==B}TS0h%52S0413=MS0oAL5Iz,;5,_9S0nPEP7%4|#199w}PvAL5Hz=d5<DS[^9>S0p'<Q04Q0g,?OS04,0lR=#5PLQ0XQ0DP2P=PLPLPL10<9$0=#2XE?XO?S0DPlPl%2lS0qQ0fQ04PLPLPLQ0YPOPOQ0iQ0eQ0gPLPLQ0WPhQ0gQ0jJ00M:yM:~S0jJ0<1;5TRT/C]%1TRh/:SS0gQ0VPyQ0ZPTPh%2hP]PSQ0kM9bP8CAS0kQ0g%46S0e%@lRh'D%6l9>k^S0iQ0eP~PkO1P~P6Pk%2kCQPhPePlO1PLPePlPlQ0qDRE`PYCAS0qQ0i%J|S04%\|S0f1;5XRh#JS0r%\hS0s%U7S0tP7Q0lP7P7Q0lDXS0lfTS0u#6S0vP?Q07#4,h?RhQ081^ig'^Q0>,^i=Khj3KP@1t?H?W;\S0>1t?G?WI\7W<PmPn1in8AMnKp5Tn1in3Q0^5Tn5nnPCPnQ03,q?R\97noS03PCPn1IqxS0^=7nKPCPnAMn\qS08PCPnQ0?PCQ0^9v?p,IsS0?97noCfFHFHPDPub4b5b6X0?X1?X7?XH?XV?X<aXFaPGPHP<20sFHC}Q05A>H^F1:FGQ05108^99GF#5[[[[[^0?^1?^7?^H?^V?^<a^FaP9fVR\$09%j\P<1;56#1S05%1bRKP\fWS07P;PIPGPFPwO<b3b:b8bDb>b;bACZQ0oQ0p102^Rh/3M10=^RT/3MP?P?Q01PLQ01Q0XPhPTPLPLPLQ0DP2P=Q0jP^P^%2^R=M:~S0jPMPM%2MM<OQ0kQ0gQ0qQ0iQ04Q0fQ0rQ0sQ0tQ0lQ0vP?Q0E=KijP@Q0>Q0:7W<PmPnQ03PCPnQ08PCPnQ0HPCQ0?/IxR2=7n4CfFHPDPub4b5b6X0?X1?X7?XH?Q0a1:HIQ0=/3MQ0b,0I?>^M[[[^0?^1?^7?^H?P9Q05PKP\Q07PIPFQ0\O7b3b:b8bDb>b;bACZQ0oeQ0nP>1_9fPEfURMQ0u%4_#1797PvAL5Fz=d5<DS]BP<1_JfP?%4P#1997wRwPEPM%k91x5FH0BXK?PH10w:&0rwEmPEQ0uPwPZAL5Gz=d5JDSeWB%49/_fQ0O/_f10v^/N^RJQ0OP~PvO1P~P<PvQ0ICQPfP^P=J0qP9CAPJQ06/CdQ0G,:ARJQ0VPyQ0ZQ06PA%2APdQ0GQ0G#2M9bP[CAPJ%4bRJ%@\RA'D%6\9>K^R=PJP~PKO1P~PbPK%2KCQPAPeP\O1PLPeP\P\%2\DRE`PcCAP=%JHQ0R#5%J1%\11;5_R=#J%\=fZR=#UP=%6=RAP=P=PADXf[#6P?PjP@Q0LPmPnQ0MPCPnQ0^/sx,rnPCQ0NFHPDPub4b5b6X0?X<aQ0_/N^PI[\N^0?^<aP9PEf_f^f]%4O#139%4URU#1AL5Yz=d5UDSQ0UPGP3O4b3bdb]bcbDb>b;bAbRWBX9>P9O1n0110200020011102P9O1WBX9>CYCYA9lOSRS/:hRO1:STP?P?PyPLPy1:<9$05XJ?X??R3PSPS%2SPhPTQ0jM<OQ0kQ0gQ0qQ0iQ04Q0fQ0rQ0sQ0tQ0lQ0vP?PjP@Q0;PmAv?pq,IsRT=Mn2PDPub4b5b6X0?X1?X7?A99<;Q0Q,?<>0I9^':^0?^1?^7?P9PKP\Q07O3b3b:b8bDb>b;bACZPOP?A9}lkAB79[XK?P8Q0e,Gl>0I}^P9J0Db@Q0heCYO6b@CYCwW^X=5P<P9O2n2001000000121101000bNWLWTP<P9O2n2001000000121000000W@X2QP<P9O2n2001000000121101000bNWSWaXI>P9H0oXI>1D9{Q0AP]A9YWVP9C|X2Q,=Q[^I>P9P{1D{{%6[R>/3>P{P>PLPeP[P[%2[DRRVP{P>PVE`%U[P[P>P[P[P>DXQ0CP?PjP@Q0KPmA7nssPDPub4b5b6X0?1399^0?P9P<O1b3b:b8CZO2PRQ0@PYPWQ0@,GXP9EPX2Q,=QQ02PQPRQ0PP]PYQ0P,GWP9EPX2QAB6]99eRtX2Q,=QP9PRQ0JP|P6Q0J,G]P9EPQ00Q0S%@6Rt'CPPP|P6PtP<Dz%@PRPABc_95eRX2Q,=QP9Q0T/CPPdPcP_%@_PHDzPQ%@dR_AB0b95eRX2QPG%@cRR,CrRPABbdGP<%1RRG,?cRt,0dR6,:dR|%6cRW,?cRY,0dRX,:dP?P?PyPLPyP3PdPd%2dR3P6PXPLPLPLQ0DPdPdP3PtPYPLPLPLQ0YPcPc%2cRYPGPWPLPLQ0WPRPWPLPePcPcPYDRRYJ00M:yM:~M<OPP1:`WRWQ0VPyQ0ZPrP`Q0[PRPePcO1PYM9bP<CAPW1;5FR5#J%\5%UbPb%6bR5PbPbP5DX%60P?Q0FQ0m>0K?gQ09'^Rg20ngj5Ki+0@P@Q0;PmPnQ0]AMnqp5TnA7npoAMnqo5Tn5nnPCPnQ0<PCAMnsTFHPDPub4b5b6X0?X1?X7?X<aPIP;P<Q0`-0m<C}A9;IH,:;\B[^0?^1?^7?^<aP9Q0d#jP<Q0dQ0cP;P]O6b3b:b8b>bACZP|P?%1_99bdAB198XK?P<PbP9EmAB0bFP9bLb@CYCwWLWTP<P9O2n2001000000121000000W@X2QP<P9O2n2001000000121101000bNbbb\W_W`WCW[P<P9O2n2001000000121000000W@WZP<P9O2n2001000000121000000W@XO?XM?WEo"). Qed.

(* [comment removed for export] *)
End CANSEC1.
