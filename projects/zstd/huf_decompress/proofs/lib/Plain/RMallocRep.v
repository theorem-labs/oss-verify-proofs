(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Export PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocRep () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp4base6LookupC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C35stdpp4base;RelDecisionI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Plain4PImg>plain_reservedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib6Malloc9MallocRep>ctx_head_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega6VarMap1t03C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep=RSIZE_CLASSESC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRepCrsize_classes_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep@rsize_classes_roC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2ex01C47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8f_equal2C35stdpp7tactics<f_equal_helpC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnK46Stdlib9micromega=RingMicromega5Psatz06C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep5rsecwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_rC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes3orbC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib5Plain:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5wr_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc9MallocRep:lr_lo_nbrkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep<rwr_in_imageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep?rmrep_ctx_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep=rmrep_ctx_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRepCrmrep_globals_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5Plain:RMallocRep<rwr_in_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep?rarea_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep=rarea_rep_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat3N2Z9is_nonnegc59OSSVerify5KrLib5Plain:RMallocRep@rgroup_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep>rgroup_rep_extC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib6Malloc9MallocRepBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemCbytes_at_write_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepDget_shadow_wr8_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRepArshadow_rep_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep?rshadow_rep_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep9rmrep_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7wr8_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib3Mem7wa_succC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9le2_splitC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib6Malloc9MallocRep@get_meta_rec_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C56Stdlib6NArith6BinNat1N7eqb_neqC47Corelib4Init5Logic5proj2C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRepArmrep_meta_store4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepBactives_set_activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib6Malloc9MallocRep9shadow_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8sh_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>shadow_le_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep>rshadow_rep_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC35stdpp4base5emptyC35stdpp8fin_maps<lookup_emptyC56Stdlib6NArith6BinNat1N7compareC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison03C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepDsh_ticks_of_ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>havoc_pages_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>havoc_units_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep?shadow_le_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMallocRep@rmrep_upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep=hav_unit_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6W_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep?W_high_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImgAref_wview_overlayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg?ref_mrd_overlayC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition RCTX : Z := 0x57b38.
Definition RMLOCK : Z := 0x57b30.
Definition RLIBC : Z := 0x57ac0.
Definition RNEED_LOCKS : Z := 0x57ac3.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSIZE_CLASSES : Z := 0x10734.
Definition RDEBRUIJN : Z := 0x10600.
Definition RSMALL_CNT : Z := 0x10794.
Definition RMED_CNT : Z := 0x107af.
Definition RGOT_SSP : Z := 0x264b0.      (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0x57aa0.    (* [comment removed for export] *)
Definition RATP : Z := 0x37830.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x3778c.        (* [comment removed for export] *)

Definition rget_meta_entry : Z := 0x1ddc4.
Definition rmalloc_entry : Z := 0x1e584.      (* [comment removed for export] *)
Definition rfree_entry : Z := 0x1dbf8.        (* [comment removed for export] *)
Definition ralloc_meta_entry : Z := 0x1e2ac.
Definition ralloc_slot_entry : Z := 0x1e8f4.
Definition renframe_entry : Z := 0x1f198.
Definition rnontrivial_free_entry : Z := 0x1ded4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlock_entry : Z := 0x2503c.
Definition runlock_entry : Z := 0x252c4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ref_reserved : list (Z * Z) := [(0x10000, 0x2000); (0x12000, 0x14000); (0x26000, 0x1000); (0x27000, 0x32000)].

Lemma ref_reserved_plain : ref_reserved = plain_reserved.
Proof.
reflexivity. Qed.

Lemma reservedZ_ref : reservedZ psegs = ref_reserved.
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
  rw_cells psegs m RCTX rctx_head_cells
  /\ u64arr psegs m (RCTX + 80) (actives st)
  /\ u64arr psegs m (RCTX + 464) (usages st)
  /\ u8arr psegs m (RCTX + 848) (unmap_seqs st)
  /\ u8arr psegs m (RCTX + 880) (bouncess st)
  /\ rw_cells psegs m (RCTX + 912) (ctx_tail_cells st).

Definition rmrep_globals : Prop :=
  rw_cells psegs m RMLOCK [C4 (wz 0)]
  /\ rw_cells psegs m RNEED_LOCKS [C1 (b8 0)]
  /\ rw_cells psegs m RPAGE_SIZE [C8 (wz 4096)]
  /\ rw_cells psegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
  /\ rw_cells psegs m RSSP_GUARD [C8 CAN].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rarea_rep (a : aptr) (ar : area) : Prop :=
  rw_cells psegs m (conc st a) [C8 (wz SECRET); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
  /\ (forall k, 0 <= k < NSLOTS ->
        rw_cells psegs m (conc st a + AREA_HDR + META_SIZE * k)
                 (meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
  /\ rw_cells psegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition rmrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.

(* [comment removed for export] *)
Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
  exists w8 : byte,
    rw_cells psegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
    /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition rmrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.

(* [comment removed for export] *)
Definition rshadow_rep (rid : N) (r : region) : Prop :=
  wr_at psegs m (r_base r) (round_up_pg (r_len r))
  /\ forall o v, 0 <= o < round_up_pg (r_len r) ->
       cell_read (get_shadow st rid) o = Known v ->
       bytes_at psegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition rmrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstatics : Prop :=
  s_reserved st = ref_reserved /\ s_atop st = ATOP /\ s_secret st = 0.

Lemma rstatics_reserved : rstatics -> s_reserved st = ref_reserved.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g004bj27Tg005Bj16Tg00K0j11Tg00;8j30Tg00Kkj15Tg00Lbj12Tg00MXj13Tg00NQR0j24Tg00NlP0g006<R1/71#6p,2stR2#1g00=L30R3%52p,2rc#2501R4%32g00Oj501R1'4R2P3f0R5P0P4P1P3P5f5X31X24f1R4P5O2n2001000000120000000X02X13P4P5O2n2001000000120000000W0o"). Qed.
Lemma rstatics_atop : rstatics -> s_atop st = ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g004bj27Tg005Bj16Tg00K0j11Tg00;8j30Tg00Kkj15Tg00Lbj12Tg00MXj13Tg00NQR0j24Tg00NlP0g006<R1/71#6p,2stR2#1g00=L30R3%52p,2rc#2501R4%32g00Oj501R1'4R2P4f0R5P0P4P1P4P5f1R0X31X14P0P5O2n2001000000120000000X02X23P0P5O2n2001000000120000000W0o"). Qed.
Lemma rstatics_secret : rstatics -> s_secret st = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"; "MREP"] "h02H0h11Hh22_Hh33_H0p;2p;1p;3g004bj27Tg005Bj16Tg00K0j11Tg00;8j30Tg00Kkj15Tg00Lbj12Tg00MXj13Tg00NQR0j24Tg00NlP0g006<R1/71#6p,2stR2#1g00=L30R3%52p,2rc#2501R4%32g00Oj501R1'4R2P1f0R5P0P4P1P1P5P5X11X34f1R4P5O2n2001000000120000000X02X23P4P5O2n2001000000120000000W0o"). Qed.

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
  ov_read_bytes psegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256.
Proof.
  intros st m rid r o v (WF & _ & _ & _ & _ & SH) Hr Hk Ho Hc.
  destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read psegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rmrep_shadow_read2 : forall st m rid r o v0 v1,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o -> o + 2 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v0 ->
  cell_read (get_shadow st rid) (o + 1) = Known v1 ->
  ov_read_bytes psegs m (wa (r_base r + o)) 2 = Some [b8 v0; b8 v1] /\ 0 <= v0 < 256 /\ 0 <= v1 < 256.
Proof.
  intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
  pose proof MR as (WF & _ & _ & _ & _ & SH).
  destruct (SH rid r Hr Hk) as [HW HB].
  destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
  split; [|split; assumption].
  assert (B : bytes_at psegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
  { apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read psegs m _ _ 0 2 B); [lia|cbn; lia].
Qed.


(* [comment removed for export] *)
Definition rsize_classes_bytes : list byte :=
  Eval vm_compute in (match image_bytes psegs RSIZE_CLASSES 96 with Some bs => bs | None => [] end).

Lemma rsize_classes_ro : forall m, mem_inv psegs m -> ro_cells psegs m RSIZE_CLASSES [CB 96 rsize_classes_bytes].
Proof. intros m MI. apply (ro_cells_image psegs m); [exact MI | vm_compute; reflexivity | unfold RSIZE_CLASSES; lia | unfold RSIZE_CLASSES; cbn; lia]. Qed.

Lemma rsize_classes_read : forall m sc, mem_inv psegs m -> 0 <= sc < 48 ->
  ov_read_bytes psegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))).
Proof.
  intros m sc MI Hsc.
  destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read psegs m RSIZE_CLASSES rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
  assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.


Lemma rmrep_meta_chunk : forall st m g,
  rmrep st m -> meta_slot st g ->
  rw_cells psegs m (conc st g) (meta_cells st (get_meta_rec st g)).
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
  ov_read_bytes psegs m (wa (conc st b)) 8 = Some (le8 (pw st (g_meta gh)))
  /\ exists w8 : byte, ov_read_bytes psegs m (wa (conc st b + 8)) 1 = Some [w8] /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Proof.
  intros st m b gh MR Hb. pose proof MR as (_ & _ & _ & _ & GR & _).
  destruct (GR b gh Hb) as (w8 & RW & Hw8). split.
  - rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at psegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
  - exists w8. split; [|exact Hw8].
    apply (rw_cells_read_at psegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.

Lemma rmrep_area_check_read : forall st m a ar,
  rmrep st m -> (s_areas st) !! a = Some ar ->
  ov_read_bytes psegs m (wa (conc st a)) 8 = Some (le8 (wz SECRET)).
Proof.
  intros st m a ar MR Ha. pose proof MR as (_ & _ & _ & AR & _ & _).
  destruct (AR a ar Ha) as (HD & _ & _).
  rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at psegs m _ _ 0 (C8 (wz SECRET)) 8 _ HD); reflexivity.
Qed.

Lemma rmrep_ctx_secret_read : forall st m,
  rmrep st m -> ov_read_bytes psegs m (wa RCTX) 8 = Some (le8 (rsecw st)).
Proof.
  intros st m (_ & (HD & _) & _).
  rewrite <- (Z.add_0_r RCTX). apply (rw_cells_read_at psegs m _ _ 0 (C8 (rsecw st)) 8 _ HD); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rsecw_init : forall st, c_init_done (ctx st) = 1 -> rsecw st = wz SECRET.
Proof. intros st H. unfold rsecw. rewrite H, Z.mul_1_r. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rreserved_disjoint : forall b n, ranges_free ref_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x12000 <= b) /\ ((b + n <= 0x12000 \/ 0x26000 <= b)
  /\ (b + n <= 0x26000 \/ 0x27000 <= b) /\ (b + n <= 0x27000 \/ 0x59000 <= b)).
Proof.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H.
lia.
Qed.

Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  b + n <= 0x10000 \/ 0x59000 <= b.
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H).
lia. Qed.

Lemma rwr_in_image : forall st rid a len,
  rregions_wf st -> wr_in st rid a len ->
  ((a + len <= 0x26000 \/ 0x27000 <= a) /\ (a + len <= 0x27000 \/ 0x59000 <= a)) /\ 0 <= a /\ a + len <= 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h01rh11Hh21ah33ridh42arh51bh62ghh72r1h82r2h94rid1h:4rid2h;2_Hh<2Hah=4__p1h>6__sat5h?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE2a0hF5ATOPRhG2B0hH2BChI2D2hJ2H0hK2H1hL2H2hM2H3hN2HrhO2L0hP2RFhQ2WRhR3_H0hS7__arithhT4__ffhU6__sat4hV8__varmaphW5__withX3lenhY2sti001xp&0p;1p;4p;2p;3p;6p;7p;8g00Q\k10PTg00Nlj1uTg00R]j1cTg00E]j4fTg00?aj4hTg00S?j1<Tg00T9j2YTg00T[j12Tg007Xj14Tg008=j1>Tg00VNj1?Tg00W`j1CTg00X\j23Tg00Lbk10JTg00;8j3LTg00Z5j1jTg00ZNj1HTg004bk202Tg00[ck401Tg00\Ak600Tg00\bj1]Tg00]nj3zTg00^Kj3xTg00^hj1vTg00WDj20Tg00NQR0j21Tg00__j1bTg02afj4iTg008[j19Tg01W9k20NTg02bak10ITg02`^k30HTg02c_k10ETg02dck10DTg02eak20CTg02fIk30BTg02fmk20@Tg005bj2pTg011Qj1=Tg01a7j2oTg009@k10=Tg005Bk10<Tg01:Fj2eTg012bk10;Tg01R6j4dTg013@k106Tg013^k105Tg01:dj2UTg01;kk104Tg01<Mj3lTg01Gdk603Tg014Ij2kTg014lj4nTg00iTk108Tg01VVk309Tg015Wk20:Tg0169j2~Tg016ek30>Tg017Dj4|Tg00]Zj6qTg00URj2{Tg00Unk20ATg00Y9j3rTg00[Ij2STg00`XR1j2yTg01nij3`Tg01cHk20GTg009`j3_Tg01EPj7tTg01;Gj7wTg01HHk70KTg01=0k80LTf5R2g00a2R3g00aPR4f4R5f3R6f2R7f1R8Eqf0R93Lp=5g00OjR:/{9p=R%49#4p=Z%49#4#4#4p=Fg006<R;20A89;L:p=N1067g00c@R<g00=LR=?r89g00c`R>3L'1p>0F10:8/19p=^1189,17p=;%?9#C,38p=G%?9#Cp=M1378/09p=X1078/S9p=\f7R?f6R@P2P5P6P7P8Eq;L9p=J10:9p=61y49p=Q1367/08/19p=:%49#4#4#4#4#4#4#4p=I%99#9p>0O10@2/S5/1610:71089'1'1p>0M1089,17p=a1056/S7/18/19p=s1078/19p=g10671089'Sp=810?@1025'S/1610:71089'1'1p=EAr=89=L<>p=D%99#9#9#9p=T10561078'S/19p=P1o;9p=@A`;89p=BA`;89g0231+0Gp=AA`;899`;7p=mg01OUR=A_=899_=79_=67_5p=OP7g01IfRAg01JERBPBg01JeRCP;P8g01PAP9Cng01KERDFtp=71k;9p=VP7PAPBPBPCP8P9Fwp=[P7PAPBPBPCP8P9K0Kp=WP8PAPBPBPCP9PDFtp>07P6PAPBPBPCP7P8P9L0Lp=KAL<9>p=}1067/S8/19p>0?g00Pc&0P6P0%u5%c4RDP3g00bIREg00bbRFP4CfRGP3PEPFP4ChRHP8%<@1Y49RIE5%28RJ#Rg00<2RK#4RL#4RM#ZRN#ZRO#Z#FRP#>RQ,NJ%?8RR%CRRR,3JRSp,2rcRT$0JRUPJPRH0F'^3;RR[^04^33PDPGPHP6f8RJ#<RV1Y47RWE5PDPGPHP7f9RX#<RY1Y48RZE5AL326#j%22/G2R[%H6%26%M6%H2R\3X3\[R][[^84^:3^74^932023;R^g00d@R_%c_R`P^P_g00>NRaP3PEP;g00e7RbH01RcP3PEPFP;Pbg00ePJ00RbP_CfRFPaPcPbP_ChREP8%]@1Y_9RdGJPDPGPHAz3;6RePVPIE5RVAx3;6Rf#6Rg%M9Rh9XfQ1NfQg00en%v9g00ff3LRi#j%H9Rj%29Rk/3f'03;3;Rl'1X04#Q[]4]2g00g^Rm%cmRnP^PmPaPcPbPmCfRoPaPcPbPmChRbP8%b@1Ym9RcGJPf%>NRNPh1NfNC:9;igRi,1VX04#Q[]6^5^'13;P2P5P6P7Ci1356RV%9MRg#9RN#4#F#I#>Rf%9N#F#I#>RN/05Ra%4K$0O#Z#9#F#I#>Rp/05Rq9\VNP5PV%>LRV%>ORr+0NRsK0M[P9%u@PDPGPHP8PYPIE5PR[^04^33PDPGPHP6f;RY#<RtPWE5PDPGPHP7f<Ru#<RvPZE5P][[^84^:3^74^93P`P^P_PFPEP8%]XPdGJPDPGPHPePtPIE5Rt/1lX04#Q[^4_^2^PnP^PmPoPbP8%bXPcGJ11tiX04#Q[^6m^5^'13;P0PDPGPHP8f:Rt#<PIE5PR[^04^33PDPGPHP6PvPWE5PDPGPHP7f=Rw#<PZE5P][[^84^:3^74^93P`P^P_PFPEP8%]tPdGJPDPGPHPePvPIE5Rx/1lX04#Q[^4_^2^PnP^PmPoPbP8%btPcGJ11xiX04#Q[^6m^5^3;PXPJP?P@Ci13J?RxPf10NJRy10pJRz9\xN%6JR{?axsDs[P9PDPGPHP8PvPIE5PR[^04^33PDPGPHP6f?RR#<RvPWE5PDPGPHP7f@RW#<RxPZE5P][[^84^:3^74^93P`P^P_PFPEP8%]wPdGJPDPGPHPePvPIE5Rv/1lX04#Q[^4_^2^PnP^PmPoPbP8%bwPcGJ11viX04#Q[^6m^5^3;PuPYPtPXCiP1P4PDPGPHPwf>R1#<PIE510ju13uYR^13khRk%6Y3g3;X04P^PfPNPuP^PNPpPuC8PuP^PsGEP9PDPGPHPRPxPIE510j1P1PwPk%6wC:3;P0PDPGPHPWfARk#<PZE5%H8PRP1PS%61C:7gR13WRRRPfPNPWPRPNPpPWC8PWPRPsGEP9PDPGPHfBRHfCRG#<1Y46E5%H5PHPk%25/G5%6kC:7gHP010\GPGPHP[%6HC:fDR[/3GRGPfPNP[PGPNPpP[C8P[PGPsGEP9%H?fERG'0fFR\PG%2J/GJ%6GC:P0fGRD%2X/GX7X\%6\fHRR/3DRDPfPNPRPDPNPpPRC8PRPDPsGEP9fIRD%2Y/GY7XR%6DPHfLRSPwPXO3%2wRZ#R1NZQ%?wRjPZ%CjRjPU1DZjC:'^3;P0%21Rj#R1NjQ%?1R1#6Pj%C1R1PU1Dj1C:3;fMR1/3SRjPfPNP1PjPNPpP1C8P1PjPsGEP9%2W#R%2kRW/NQ%?kRk#6PW%CkRkPU1DWkC:3;P0%2HRk/NQ%?HRHPk%CHRHPU1DkHC:'^fQRHfPRk'3RWPfPNPHPWPNPpPHC8PHPWPsGEP9%2[/NQ%?GRQ%2GRG%CQRQPU1DGQC:'^P0%?\RQ#6%2\R\%CQRQPU1D\QC:fURQfTR\'3RGPfPNPQPGPNPpPQC8PQPGPsGEP9%?R#6%2DRR%MDRGPU1DRGC:P0fJRG#2RR%MGRG;XU1DRGfYRGfX'3RRPfPNPGPRPNPpPGC8PGPRPsGEP9%2S%MS;XU%21%M1'D&0IT%9KRT#9RS#T#T#TRR#4#T#T#4#Z#F#I#I#>/0URG%9R#T#T#4#Z#F#I#I#>RR7aUfOR[#2RW%M[R[<0H813W[R[%FP#>RP%4g#F#I#>RgPWP[PgPfPWP[PfPNPWP[PNPpPWC8DPDPDPP0%2kR0/GkRkPPPgP0C8PkPgPfP0PkPfPNP0PkPNPpP0C8DPDPf_R0f^'3RkPfPNP0PkPNPpP0C8P0PkPsGEP9fRRk#2R0/GkPPPgP0C8fSR0#2RP/G0R0PgPfPPP0PfPNPPP0PNPpPPC8DPDP%?\R\$0E%C\,0\&0DQ%2Q%HQ'020CVr%RVRQ%6r%Rs[R\[%6VRPg02gNR0B0BVr8UW<%6s\0^<PP8g02gj20@:V'pPQeO1P\p-0R\g01O6RQ#=RP#=R0#=Rr#=RW#=R[#=RH#=Rj#=RZ#@RI%@rRr%@PRP'BRx'A%=ZRZ#=R^#=#@Ru%@ZRZ%@0R01o;QRQ'BRh'B'A%@^R^1BPQRQ,BZ'ARP%@H%@[/Bh'AR[1BIh,AuRhPh%@j/BQ,A^RjP[1AZxRxPx%@WRW/BQ,A^P[PhPhPjP[P[1BIQ,A^AmWr09m^Z,AuRuPuP[PjPhPhP[PPPxPxP[PjPhPh&0==DODODODODODODODO&0<=P;P;1e;5P7&0;;CdP8P;1e;2P61e;@CdCd&06;&05;R=1U;MRM1U;TRT57=&04BRhP=%9L,U;9l;MRj%Vg57=%VfR[=7=M5[=A7=j[%VNRx=7=M5[=A7=jx%VpRp=7=M5[=5W=5W=PhP=P=PAPBPBPCPJJ031U;SRS%VR57=5W=PhP=A7=jSPhP=P;1k;:RSg01PhPMCn-07=PhP=1U;LRL97=SPhP=1U;KRK=l;LRL=7=jPhP=A7=TKPhA7=L[A7=xK5[=A7=LxA7=pK5[=5W=A7=SK%VV&08O609;97=L5W=5W=CKCKCKCKCKCKCKCK20:=CP9P71p<>1~97#}dB0>;:8C|bTbVbWX?;X@;XA;XB;XC;XD;W=10671352R2PgPfP5P2PfPaA\2NqH0?DPAaJ?R13@?RR/0J%R?%6@13Xt,0R10X?13JXRXPfPyA\XNzAa{XsDs[[[[[[[[^?;^@;^A;^B;^C;^D;^=\P9PGPUfZRU#M%2U%HUfgfhP5P@PYPwPDP1fNPkO?bSb>bUb>bJb1WIW;P8P9O2n2001000000121000000bEbFWPWHP8P9O2n2001000000121000000W1WOP8P9O2n2001000000121000000W1W;P8P9O2n2001000000121000000W1WGP8P9O2n2001000000121000000bEWMWLP8P9O2n2001000000121000000W1WKP8P9O2n2001000000121000000W1WNP8P9O2n2001000000121000000W1X04P8P9O2n2001000000121100000W1WRWQP8P9O2n2011000000121000000W1W;P8P9O2n2011000000121000000W1XX;X2;X33WYo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h02L0h11Hh21rh34__x1h44__p1h57__arithh61nh74__p2h84cstrh95cstr0h:4__ffh;8__varmaph<5__with=1ai001ah>3ridi013ridh?1bi021bh@2_HhA2arhB2ghhC2r1hD2r2hE4rid1hF4rid2hG5ATOPRhH5cstr1hI5cstr2hJ5cstr3hK3_H0hL4__x2hM4__x3hN4__x4hO1ihP1qhQ1DhR2RFhS2WRhT3_H1hU3_H2hV2a0hW1ehX1lhY1zhZ2ARh[2C1h\2C2h]2C3h^2C4h_2C5h`2C6ha2Cahb2Cbhc2E6hd2G1he2G2hf2G3hg2G4hh2G5hi2GRhj2Hahk2Hbhl5Hconchm3Hk'hn3Hpwho3Hr'hp3Hrahq3Hrbhr3Hschs2L1ht2L2hu2L3hv2L4hw2L8hx2MRhy2SHhz3Sa0h{3Sa1h|3Sb0h}3Sb1h~2WFi031ki041mi053offi062q0i072r'i082rai092rbi0:2sci0;2sti0<1vi0=1xi0>1yi0?1op%0p%1p%2p%3p&0p&1p&2p;1p;2p;4p;3p;8p;:p;6p;5p;<p;7g007Xj16Tg00iTk11TTg00j2k11ETg00R]R0k10eTg00jUk20vTg008[j1OTg00URj2`Tg00Q\k10pTg00kPk20NTg00lOk10ATg00X\j21Tg008=j1kTg02I`k10TTg02Jej1tTg02LUj1YTg02MQj1ZTg01lDk10wTg02:[k11ZTg009@k11;Tg02?\j4lTg01Ccj1}Tg02CZk10MTg03Sjk12ATg00NQR1j20Tg00mRk20mTg00nSk20`Tg00oUk20_Tg025Qj2jTg04Uij3MTg028jj2UTg00;8j39k11:Tg00T9k20FTg005bj2gTg01;kk11LTg011Qj1STg037ak21ITg01>?j25Tg03Mfk21FTg01LDR2j1;Tg0361k21xTg03NEk40fTg03Nak40iTg04Vdk11mTg01^Kk20UTg04W[k10]Tg03?Ak11STg005Bk115Tg03>Kk10cTg02;Pk11`Tg01[ek21_Tg01W9k21^Tg03@7k21]Tg00;Rk41\Tg02PAj1xTg0186k11=Tg04XQk41<Tg038Yk21[Tg03:ck21YTg03<Yk21XTg02OCk100Tg02H5j1~Tg01dek21WTg01eHk31VTg01fLj1HTg01a7k218Tg01hCk21UTg01:Fk20uTg013@k12ETg013^k12DTg014Ik217Tg01:dk20rTg01hok31RTg015Wk22CTg0169k22BTg016ek32?Tg017Dk42>Tg00WDj23Tg014lk40WTg01VVk32;Tg04YAk82:Tg03Q5m:29Tg03Qnm:1OTg00PHk40lTg04Z:k427Tg00?Ck60^Tg00[ck426Tg00\Ak625Tg00E]k412Tg00?ak411Tg00\bk11NTg00]Zk60VTg024\k223Tg02<Kk222Tg03aRk521Tg00T[j12Tg00Z5k110Tg00Unj2vTg00Lbk11~Tg03Baj4bTg00S?j1VTg00VNj1:Tg00W`j1ITg00Nlk10ZTg00ZNk10xTg004bk21}Tg02`^k30~Tg04[Bk31|Tg02bak11{Tg02c_k11yTg01g1k21wTg01gZk31DTg012bk11tTg01R6k40}Tg03f8m<1sTg03g=k81rTg00__k11CTg03h@k51nTg03Ijj4]Tg03l1m:1pTg03m7k71qTg01@:k21kTg03Jjk40DTg0436m:1jTg044=k71iTg01Aok10QTg03Rfk30YTg02NQk40STg02Kbk41BTg009`k30OTg027>k11MTg01G?m<1hTg01eek41gTg01nik320Tg01cHk21fTg01EPk70tTg01Gdk624Tg01HHk71eTg01<Mk31ATg01=0k813Tg03O@k11dTg00[Ik20:Tg01;Gk716Tg03P9m:1cTg00]nk32<Tg00^Kk32=Tg00^hk11bTg00`XS00k21aTg00Y9k30|Tf0R3#6#6#6#kp=Lg00OjR4f1R5'3/03p>0Cf5R6f4R7+0mf3R8f2R9+0`20_53'0'0p=R1053,09p=G1U53#~p=Cf7R:f6R;;M620U95,18$0Q>0Y73+0vp=[&0A5/03p>0Gg00<WR<P5g02QER=P3Clp>0j%O3#6p=KP<P6P7&008H0SP<P9P5%x3Cl'0p>05P<P8P9P5H0S/03p>0@P<P8P9P5H1B/03p>0EP<P9P5P3H1Bp=pP<P9P5%Z3H0Sp>1@P<P9P5&003H0Sp>0{P<P9P5%x3Clp>1?g00J;R>@0O53p>19P<P5g03U[P3Clp>0d%63#6p>0L%63#6#6#6p>0s&0w5$1M>0O>3p=wP<P5g03V\P3Clp>0XP<P5g03WVP3Clp>0<&1M5>0O>3p>1QP<P5g03XTR?P3Clp>0;1053,09,08p>0I20`8920_53'0p>1Pg006<R@/g3p==1j95=9@3p>09%S3#S#S#S#S#S#S#Sp>0bg01KeRA?953p>06PAP7P8P9P5P3J0^p=8%t3,55p=^%~3,55p>1l%O3#O#O#Op=f%63#Op=\%O3#Op>0J&0Q5>0Y93p>0aB0O>53:0O>9p>0B20U95,18$0Q>0Y73p>0zP<P9P5P3H0Sp>0yP<P9P5P3Cl,08p>1>1053,09,08,07p=d20U53,19p=NP<P9P5P3Clp>08A9@53p=>PAP@P3P2P5P9P8P7P6P;P:f8R2N<1hp=DA9A78P9P5P3H1gp=F1U53#~,59p>02%;3,34p=E218@3p>0>B20@53p=Wg0231-1f3p=|g01OURB@0O53p=cP9g01IfRCg01JERDPDg01JeREP@P5g01PARFP3H0Wg01KERGK0tp=XP5PCPDPDPEP3J24p>0qP9PCPDPDPEP5P3K1ep>0=217@3p=_217@3:1A@5p={B1A@53p=hP8PCPDPDPEP9P5P3L13p=qg00c@S01g00c`RH793p>2@1343p=<P5PCPDPDPEP3PGK0tp>14&1d3#;,15p=y13891353+0:p=?P:PCPDPDPEP;P6P7PCPDPDPEP8PCPDPDPEP@P9PFP5H0WPGK0tP3K16L13p=z139500:3p>0K1195/33p=4P<P3P5P9P8P7P6P;P:P2N:1cp>0HP6PCPDPDPEP7P8P9PCPDPDPEP5P3K16L13p>0o1353-0:9p>0n1178/391353+0:p=iP;P6P7P8P9P5P3H0lH0lp>0PP<P8P9&005H0S/03p>281189/3500:3p=ng00a2RI@2<@3p>0?PIg00aPRJP7P8P9%V5J0V=963p=aB2=I@3p=@%:3#Ip=B1v53=9@4p=Qg00en&1b3g00ff39p=r1`43p=JA9@54/03,09,08p>0k21aJ3p=A1v95=9@4/03p=uPIPJP7P8P9P5J0V=963p=7&1081053,09'0p>071167/381v95=9@4/03'0p=o20U89,17$0Q1U53#~60Y6p=Tg00=LRK@0|53p>1KQ01?93H,05p>1JP6g00d@RLP7P8P9&1N5J0V=9;3p=sP6g00g^RMP7P8P9&1C5J0V=9;3p=m1v95=9@4/03,08p>1HQ01B0|K53;9Hp=P13471189/35/03'0p>0113471389Q01B0|K53;9H'0'0p>1G1189/35/03p>0\%63#6#6#6#6#6#6#6p>0313:;1367+0:13891353+0:'0p>0413781395+0:/03p=e%I3,15p>0R1395/03p>1zP@P5PFP3H0Wp>0gP8PCPDPDPEP9PCPDPDPEP5PGK0tP3K16p>0h1v89=9@41053'0p>0[&0Q91U53#~60Y8p>1o1153$0Qp>1uB0Y953-0v8p>1vg00Pcg00<2RG#6S02#6S03#6RC#6S04#6S05#6RF$1TS06$1ERK&1TC$1ERN$0e[g00@LRO20v89%OGS07#6RP#LRQ,`9-0C9P520v67P1&0p;20N;6&0A6P;P6P;P6P;P6ER3GP6P7P:P;Q02#OS08#6#LS09,1=RR%kCRCP61C:7G[P3&0p2f9RS00N2&0A2PSP2PSP2PSP2ER3GP1f:S0:00NSQ0:PSQ0:PSQ0:PSER-0GSPSP2f;RTQ0:PRPCPS1CT2G[P3f<RU00NTP1f=RV$0T-0jUPUPR%tVPUQ07#OS0;#6RW#K#LS0<,1=S0=%YVPU%OPRP#6#K#LS0>,1=S0?%ZVPU%OP#K#LS0@,1=RPPVPU%6W#K#LS0A,1=R=PVJ05H0@H0EH0Ef>S0BPVQ0BPVQ0BPVER-0GVPVPUf?RWQ0BPRPCPV1CWUG[[P3Q0B&0TW+0jPWPRf@RX#tPWQ0=%YXPWQ0?%ZXPWPPPXPWP=PXJ05H0@H0EH0EP1fARY#t9pXRPXQ0=%YYPXQ0?%ZYPXPPPYPXP=PYJ05H0@H0EfBS0CPYQ0CPYQ0CPYER-0GYPYPXfCRZQ0CPRPCPY1CZXG[[P3Q0C%tZ7pRPZQ0=fDR[#YPZQ0?%Z[PZPPP[PZP=P[J05H0@H0EP1Q0=fER\#Y5p[P[Q0?%Z\P[PPP\P[P=P\J05H0@fFS0DP\Q0DP\Q0DP\ER-0G\P\P[fGR]Q0DPRPCP\1C][G[[P3Q0DQ0=%Y]3pP]Q0?fHS0E#ZP]PPQ0EP]P=Q0EJ05H0@P1Q0EQ0?fIR^41@Q0EPPP^Q0EP=P^J05fJS0FP^Q0FP^Q0FP^ER-0G^P^Q0EfKS0GQ0FPRPCP^Q0GQ0E'CG[[P3Q0FQ0?Q0G41@Q0GPPfLS0HQ0GP=Q0HJ05P1Q0HfMR_80{PQ0H@1?=_fNS0IP_Q0IP_Q0IP_ER-0G_P_Q0HfOS0JQ0IPRPCP_Q0JQ0H'CG[[P3Q0IQ0J80{PQ0JfPR`81?=fQRaP`PaP`PaP`ER-0G`P1&0AafRS0KPaQ0KPaQ0KPaERPaP`fSS0LQ0KPRPCPaQ0L/C`G[P3Q0L$0AP1P<fTRbg03T_Rc&0w4Rd$1Z&1;>Re+19S0MCl%}4$0M019eS0N-0db&0LF$0sS0O#kRf/weRg-0Xb1w?eR?-0<bp,2rcS0P$2A01QeRh-0;bH0IfVS0QfUS0RQ0QQ0RQ0QQ0RERQ0RPbfWS0SQ0QPRPCQ0RQ0S/CbG[[P3P<Q0QPcQ0MClQ0SQ0N+0dQ0S00XgQ0S00<?Q0S00;hH0IP1fXRcQ0N+0d20Xcg20<c?20;ch3GfZS0TfYS0UQ0TQ0UQ0TQ0UERQ0UPcf[S0VQ0TPRPCQ0UQ0V/CcG[[P3Q0TQ0N+0dQ0V00XgQ0V00<?Q0V00;h3GP1f\S0W00XgQ0W00<?Q0W00;h'0f^S0Xf]S0YQ0XQ0YQ0XQ0YERQ0YQ0Wf_S0ZQ0XPRPCQ0YQ0ZQ0W'CG[[P3Q0X00XgQ0Z00<?Q0Z00;h'0P1f`S0[00<?Q0[00;hfbS0\faS0]Q0\Q0]Q0\Q0]ERQ0]Q0[fcS0^Q0\PRPCQ0]Q0^Q0['CG[[P3Q0\00<?Q0^00;hfeR?fdS0_P?Q0_P?Q0_ERP1ffRi00m?PiP?PiP?H1PP?Q0_fgS0`PiPRPCP?Q0`Q0_'CG[P3fhS0aQ0`+0mfiRjQ0aPjQ0aH1PP1fjS0b00`jQ0b00_jPjQ0afkS0cQ0bPRPCPjQ0cQ0a'CG[P3flS0dQ0c+0`fmS0eQ0d+0_g00>NRkfoS0f/j3Rl#=WPQ0eQ0dQ0f3M@093l^PkP0PkQ0ffnR0fqRl3M/U31Ul359KP3frRm20Fk3'U,gKXPkP3O1fpRn&1Lk'U,gKn10110?00021010000Z06OQ0e=M0n/U31Un359K^POg01O6RO%SOS0g#SS0h#SS0i#SS0j#SS0k#SS0l#SS0m#SRo$0b$0b$0bRp$0b$0bRq+1IRr,5AS0n2063qX6ARsPqPs1gAqQ0n21FqOD8S0oPAPK%;3Rt-1xl,UlXOARuPrH0f,5KPAPKPuPrH0iD81^Kn006qRuePu1Ul0R0$1m21lN0006oQ0f=MnmS0p$0pQ0p%6G#K#f#\#K#\$0J#LR0Q09'1Ru20UCnS0q'1S0rQ0f,CmS0s60alRv+0NS0t&0AvS0uQ0p00mvS0vQ0p00`vS0wQ0p00_vS0x'0S0y'0S0z'0Rw'0PjQ0tPw&0]mRw$1SS0{g03AfRxPx&15>R>ftRy$0]$0c#}$0MRzQ0mQ0m$1`+1_R{PxP@P3P4Q02#kS0|%kF+1^S0}%kGS0~+1]RFfsR|fvR}5MyS10PIP@P5P3H1\R~'jn0110=0003000020101105/we40BPxP@P3P4PF1j}~n0110=0003000020101105/we:0Bz{39P3&0]|$0c#}$0MRz21Qde80B{,g>1wFe:0Bz{,g>fwRz$0]$0c#}$0M1jz~/we80B{,g>Z05@X>IP5P3O2n011020003000020101105b?Q0p$0]Rd$0c#}$0MPxP@&1SdP4PFAMmlyS11/j~n0110=0003000020101105/we80B{&0cw#}$0MPxP@Q0{P4PF1jy~n0110=0003000020101105/we80B{59>eQ0p#x%xm59>R{eP{P>%x|S0{P|PuPCPm1CylS12I0zR{&0Ty+0jR~Q11#t9p{RQ0=%Yy5p{RFQ0?%ZyRx60y{RwB0{{PyRdP{P=P3H1>DdXX>&15KR>PK%t|S13&1=l1U|nS14H1<S15P~Ap{R3PFPwPdP{P=%xyH1>DdXX>Q0nPsQ0oPAPK21[yt$0wXOARsPrH0f,5KPAPKPsPrH0iD8%Y|S0o,5K006qRrePr21IOpRr,5ARs2063pX6AR>PpP>1gApPs21FpOD8R{PAPNfuRd01Yt#}XOARwPrH0f,5NPAPNPwPrH0iD815Nx006pRxePxPsP>P{PAPN21X}t#}XOAR{PrH0f,5NPAPNP{PrH0iD8&00d,5N006pRrePrANuCyS0n1U}|Rr#~S1660adS17&0T}S188080Q17PK%t}S19&1=yPrH1<7puS1:Q17Q0<,10S1;%Y}S1<3pS1=Q17Q0>,10S1>%Z}S1?40yS1@Q17Q0@,10S1A&00}S1B40yS1CQ17Q0A,10S1D%x}S1E408S1F'0S1G'0S1H'0S1I'0PdP0Q18Q0nQ16PiQ1B,5NS1JPpQ1J#;RrQ05#kR{'>S05&1:AR>&1:@Rs%;5/>t2065321W5341VZ0>AZ0=ARxQ1JPr%=rPpP{%={S1KM9DP3DFS1LQ05%Zz,5NRrPp%;rS1M/>{S1NP>PsPxPrQ1MQ1M#=PpP{Q1KM9DP9DFS1OQ1NfxS1P#Y,5KRrPq%;rRw/>QS1QP>PsPxPrPw%=wPqPQ%=QS1RM9DP7DFS1SQ1QfyS1T>02N}RwPo%;wRr/>CS1UP>PsPxPwPr%=rPoPC%=CS1VM9DP:DFS1WQ1UfzS1X,^KRrPq%;rRw/>QS1YP>PsPxPrPw%=wPqPQQ1RM9DPSDFS1ZQ1Yf{S1[Q1P'CS1\,5NRw#HS1]%EwS1^f|Rw#Y,5KRr#HS1_%ErS1`f}S1a$00,5NRr#HS1b%ErS1cf~S1d,^KRr#HS1e%ErS1fp+01@Rr#Z,5NRF#HS1g%EFS1hp-0RF218@OS1iQ1iQ0h$0>S0h'W#|+1U&1;BS1j'cS1k&15BRB20u@5S1l&2E@RO&2D@R~217@4S1m20r@GS1n5X~S1o20q~8S1p60=~S1q&1LDRDQ1m%_0S1rQ09'{S09%_CS1sQ1n61R@'hS1t5X~Cq22C~EREP3P9Q01/gH22B39$2@dB2?@45H2>R4b:b;b<X3@W4S01%<3S1u/05S1vANuC5S1w#<[^3@^4FS1xP31`rQS1yPrPwO3b5bJbIbHb9b8b0b0b0b0b0S1zPoANuCdRH/1tS1{Q0}'3X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pP@Q1ng01PhS1|%_QS1}H0W-14~S1~60=~S1pPDQ1tQ1s'hS20Q0|#_Q0662;@5X~CqPEP4b:b;b<X3@X4FS061`3QS0|,05S21Q1w/1CS22Q0}'3[^3@^4FS23P3%<rS24PrPwO3b5bJbIbHb9b8b0b0b0b0b0Q16,5NS25P7D8S26Po&0Tz,y0PHQ1{P0C?X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1qPDP~P~Q09Q1t20q~7S27GzPEP4b:b;b<X3@X4FX7FQ1vQ1w>0Ku8[^3@^4F^7FP3ANuCrS28?4C0Q1yPrPwO4b5bJbIbHb9b8b0b0b0b0b0Q18,y0Q0nQ0n%;oS18'1S1yP0C?eQ25P7D8N90HQ1:Q1IQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1jPBQ1lPOP@Q1tg01QOQ1tH0W-14~PEP4b:b;b<X3@ANuC3R0/>0^3@P3PrO1b5bJbIbHb9b8b0b0b0b0b0Q0nQ0n'>P<P}Pu%tzS1IPd1UzyS1:Q0^Pq1`}t-0C}X6A&00z,5NS29PpQ29#;R0/>{S2:P>PsPxQ29P0%=0PpP{Q1KM9DP5DFQ2:Q1P#Z,5NS2:PpQ2:#;S29/>{S2;P>PsPxQ2:Q29Q29#=PpP{Q1KM9DP8DFQ2;Q1T#Y,5KS2;PqQ2;#;S1K/>QS29P>PsPxQ2;Q1KQ1K#=PqPQQ1RM9DP6DFQ29Q1X>02NzS29PoQ29#;S1K/>CS2;P>PsPxQ29Q1KQ1K#=PoPCQ1VM9DP2DFQ2;Q1[,^KS2;PqQ2;#;S1K/>QS29P>PsPxQ2;Q1KQ1K#=PqPQQ1RM9DQ0:DFQ29Q1T:02NwS29#HQ29#EQ1a#Y,5KS29#HQ29#EQ1d$00,5NS29#HQ29#E1^KrS29#HQ29#Ep+01AS29#Z,5NS1K#HQ1K#EQ1jPBQ1lPOP~Q1oQ1~60=~S1~PDQ1~CqPEP4b:b;b<X3@S1~Q1uQ0|'01`5Q-0C5[^3@S0|P3Q29Q1aO2b5bJbIbHb9b8b0b0b0b0b0Q1I,5KP;D8L2:b1Q1=Q1HP<PdQ1;Q1<Q0nQ16Q0XQ1zQ26PoQ1;%Yz,5K#;7NCPHQ1{Q1;C?X6APqQ1;?NCtPHQ18,1HS1HQ1;C?X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0<'{5X~J0oPEP4b:b;b<X3@X4FX7FQ21Q22Q1;60n8[^3@^4F^7FP3Q1;20UCQQ2834Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1<,5KP9D8Q25P7D8N:29Q1@Q1GP<PdQ1>Q1?Q0nQ16Q0TQ1zQ26PoQ1>Q1MPHQ1{Q1>DiX6APpQ1>PtPHQ1HQ1>DiX6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0>'{5X~J0oPEP4b:b;b<X3@X4FX7FQ21Q22Q1>60n8[^3@^4F^7FP3Q1>Q2874{Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1?,5NP5D8Q25P7D8N:1OQ1CQ1FP<PdQ1AQ1BQ0nQ16Q0QQ1zQ26PoQ1AP0PHQ1{Q1ADiX6APpQ1APtPHQ1HQ1ADiX6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0@'{5X~J0oPEP4b:b;b<X3@X4FX7FQ21Q22Q1A60n8[^3@^4F^7FP3Q1AQ2874{Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1JP3D8Q25P7D8N:1OPdQ1DQ1EQ0nQ16Q0RQ1zQ26PoQ1D%xz'yPHQ1{Q1DC?X6AQ1LQ05Q1OQ1NQ1SQ1QQ1WQ1UQ1ZQ1YQ1]Q1^Q1_Q1`Q1bQ1cQ1eQ1fQ1gQ1hQ1kPBQ1lPOP~Q1pPDP~Q27Q20Q1rQ0A'{5X~J0oPEP4b:b;b<X3@X4FX7FQ21Q22Q1D60n8[^3@^4F^7FP3Q1DQ04#kR{Q2834Q24PrPwO4b5bJbIbHb9b8b0b0b0b0b0Q1DQ1E'yQ0nQ1yQ1DC?eQ25P7D8N90HH0lK0PK0PbvbubtANuClS25Q14#~Rp60amR0&0T|+0jQ159p0RP0Q0=Q0oP0Q0?%Z|P0PPP|Q0{:080=H28H0@H0E3GeAMln|R0#tP|PlPn15NpRpPo%;pRn/>CR=P>PsPxPpPn%=nPoPCQ1VM9DP5DFP=1^KyR=Pq%;=Rn/>QRpP>PsPxP=Pn%=nPqPQQ1RM9DP8DFPp1CdmS0{,5NRp#H%EpQ19,5KRp#H%EpQ1~Q0|P3P}P|O2b5b9b8b0b0H27J0^%x0P3J0^bcQ0teQ0uQ0z%6G#K#f#\#K#\#K#LR0Q0M608v%\G#\$0J#K#K$0J$0s$0J#kRpQ0N608vS0z%6G#K#f#\#\$0J#K#LRn>08vgS0t&0LG$0J$0L#K#\#\#K#LR=%6G#K#f#\#\#\$0L#LRP/weS0|608vS1~B08vPhS19'0S0?'0S0o'0PlP0Q0MQ0rQ0sQ0FQ0s,5NRvPo%;vRe/>CS0=P>PsPxPvPe%=ePoPCQ1VM9DP3DFS15Q0=Q13,5KS13PqQ13#;Re/>QR<P>PsPxQ13Pe%=ePqPQQ1RM9DP9DFS13P<Q12,5NRe#HS12%EeS141^KdRe#HS1D%EeS1yQ01Q1xP31`dQS0nPdPmO3b5b9b8b0b0S1EPoQ25/1tS24Q0}'3X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ06Q23P3%<dPdPmO3b5b9b8b0b0PvP3D8S28PoQ0M,y0S0MQ25Q24P0C?X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%_0Q03#kRe'{Q1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vP0PeQ1wP8Cn[^3@^4F^7FP311HCRe/30Q0nPdPmO4b5b9b8b0b0Q0MQ0rQ0rQ18'1S0MP0C?ePvP3D8N90HQ0zQ0oPlPpQ0NQ0rQ0sQ0DQ1EQ28PoQ0N,ypR0Q25Q24PpC?X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%_pQ0~'{Q1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPpQ0~Q1wP8Cn[^3@^4F^7FP313epQ0nPdPmO4b5b9b8b0b0P0Q0rQ0MPpC?ePvP3D8N90HQ0tQ0?PlPnPgQ0rQ0sQ0CQ1EQ28Po1yngRgQ25Q24PnC?X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%_nQ1s'hQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPnPCQ1wP8Cn[^3@^4F^7FP313enQ0nPdPmO4b5b9b8b0b0PgQ0rQ0MPnC?ePvP3D8N90HQ1~Q19PlP=Q0|Q0rQ0sQ0BQ1EQ28PoQ0|,y=RnQ25Q24P=C?X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%_=Q1s'hQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vP=PCQ1wP8Cn[^3@^4F^7FP313e=Q0nPdPmO4b5b9b8b0b0PnQ0rQ0MP=C?ePvP3D8N90HPlPPPhQ0rQ0sPVQ1EQ28Po1yPhRhQ25Q24PPC?X6AQ15Q0=Q13P<Q12Q14Q1DQ1yQ1kPBQ1lPOP~Q1qPDP~P~%_PQ1s'hQ1tQ27GzPEP4b:b;b<X3@X4FX7FQ1vPPPCQ1wP8Cn[^3@^4F^7FP313ePQ0nPdPmO4b5b9b8b0b0PhQ0rQ0MPPC?ePvP3D8N90HK0PK0PQ0ueQ0vQ0y&0eLS0yPkPLPkPIg00bIRvP@g00e7RPH26RhPIPvg00bbReP@PPg00ePJ25RPPLH12S0uPkPhPPPLH11S0MP5Q11$1NJ0V20FL3S0r39PdAM|mdS0nPyPuPCP|Q0{I0zS0{P9P5P;Q1ug02BE,`3'0g03I3g02@Rg02AK;N5-237-22z'gUZ03@PdP9P5Q0dP3I21&0eJR|PIPvPePJH12RmPIPvPePJH11Re&0?8S1uP}20FJ3RvEaS1v%23R<%@8R='1S1w:09}8S27%<=S1t%B3S1q94=fS1l1Q=fS1k%r3S1y$10S1D%J<S141v<fQ1qQ0P$1~Rn54<S12H0kRg'0DdX2J#AQ00PJP|PmPe&0?7PzPvEaS13%@7S0=,1<:09z7S15Q0=#<S24Q0=Q1q74fQ0=?ufgDdX2JPzQ1:#~:0a}HS1:P7P8CbP3P|PmPe&0?;Q1TPvEaS25Q1T%@;S28,1<809;S1EQ28#<S0|Q28Q1q74fQ28?ufgDdP1P|PmPe&0?:Q1X#VS1920FJ5S1~E7S0?Q1X%25Rg%@:S0t'1809:S0~Q0t#<S0NQ0tPf%:5R<#IS0oQ0tPf%r5S0z%JgS041QgfRHQ0o=4gnS21H07Eo3GQ1[Q1XPuPCQ1TQ1\I0zS1\P2P:CbP3P|PmPe&0?S%VwS1X20FJ8E7S22Q1aQ0:%27RpQ0:#@S20'1409S1rQ20#<S0AQ20Pf%B7S1pQ20Pf%r7S1h%JpS1g1QpfQ1p=4pnS1fH07Eo3GP1Q1d%26Rp%@TS1e'1809TS1cQ1e#<S1bQ1e%B6S1`74fQ1e/vf%r6S1_%JpS1^1QpfQ1`,1pRp/3nS1]H07H0kPrQ1dPuPCQ1aPrPwETS1YPUPTCbP3Q29%2:%@V'1809VS1ZQ0B#@S1U#<S1WQ1U%B2S1Q74fQ1U/vf%r2S1S%22R0#JS1N1Q0fQ1Q=40nS1OH07H0kP1%@WS05#<S1LQ05Pf%BSS1{Q05Pf%rSS26%2SR0#JS1z1Q0fQ1{=40nS16H07Eop+01DS1Jp+01CS1APuPCp+01BS0@Q1JQ29ETS1HPXPWCbP3%@Y#<Q0C#@S1BPf%BUS1FQ1BPf%rU%2UR0#JS1C1Q0fQ1F=40nS1?H07EoP1%@ZS1>%BVS0>74fQ1>%rV%2VR0#JS1M1Q0fQ0>=40nS1GH077ufp+01HS1@p+01GS1<PuPCp+01FS1;Q1@p+01ES0<ETS1=P[PZCbP3%@\S1I%:WS1o#IS1K74fQ0D#@S2;%rX%2XR0#JS2:1Q0f%BXS2<=40nS2=H077ufP1p+01KS2>$0ZP|PmPeP5p+01MS2?PvEaQ04Q21Q0o-1Kg+1J-0C<7GHS2@[^2J^>IP|PmPeP8p+01OS2A#VRH20FJ9S2BE7P|PmPeP9p+01PS2C#VR<Q1~E7A9I68$10&0x8%28%B8&0x63460Kp[S2D[[^DJ^FI^CJ^EI21}I@RpQ0yPpQ0uQ0MP5Q2?Q0rFsP|PmPeQ1uPHPvE7RHQ1tQ1lQ1kQ1D&0x3Q1w'3DdRg'0X2J#A[^AL]=&0eMS1wPpPkPhPPPMH12S1DPkPhPPPMH11S1kP5Q2?20FM3S1lFmQ1yQ1tQ1q94={S2E1Q={S2FH0IR=,0HX2J#A[^BM^?pH0Ip+01LS2GQ2>PuPCp+01JS2HQ2Gp+01IS2IETS2JQ0EP]CbQ0@Q2?$0ZP|PmPeP5P<PvE7Q2@[^2J^>IP|PmPeP8p+01RS2K#VR<Q2BE7P|PmPeP9p+01SS2L#VRHQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2CQ0rFsP|PmPeQ1uP<PvE7R</0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2CQ1lFm10<=X2J#A[^BM^?pH0IP1P|PmPeP5p+01QS2MPvEaQ2@[^2J^>IS2NP|PmPeP8PHQ2BE7P|PmPeP9p+01TS2O#VS2PQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2MQ0rFsP|PmPeQ1uPHPvE7R</0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2MQ1lFm10<=X2J#A[^BM^?p3GS2QQ2CQ2APuPCp+01NQ2CQ2?ETS2RQ0HQ0GCbP3P|PmPeP5PHPvE7Q2@[^2J^>IP|PmPeP8p+01VS2S#VRHQ2BE7P|PmPeP9p+01WS2T#VS2UQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2OQ0rFsP|PmPeQ1uPHPvE7RH/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2OQ1lFm10H=X2J#A[^BM^?p3GS2VP5Q0J$0?P^P\O3%2^RH#JPHPf%:^R<%I<R<=4HnS2W21KH<+1J+0CH1HP1Q0F#2R<#JQ0F#:RHP<%IHRHPn1P<HS2XI019u<fp+01UR<Q2OQ2L9NuCS2YQ2K,C<S2Z40aPaP`CbP3Q0H#2S2[#J%2_S2\%:_RHQ2\%IHRHPnQ2\/PHI017ufS2]P1Q0I#2S2^/QfS2_Q0I#:RHQ2^%IHRH'1S2`PnQ2^PHI1GS2ap+01YS2bp+01XS2cPuPCQ2TQ2bQ2SETS2dQ0RPbCbP3%2`S2e/Qf%:aRH%2aS2f%IHRH'1S2gPnQ2fPHI1GS2hP1Q0K#:RH#<S2iQ0K#2S2j%IHRHPnQ2j/PHH0\S2kp+01]S2lp+01\PuPCp+01[S2mQ2lp+01ZS2nETS2oQ0UPcCbP3%:b#<Q0R#2RHQ0R#:S2p#IRPPn1PHPH0\S2qP1Q0Q#2S2rQ0Q#:S2s#IS2t'1S2u/3nS2vQ2rQ2t'PS2wp+01aS2xp+01`PuPCp+01_Q2xp+01^ETS2yQ0YQ0WCbP3%2c%:cS2z#I;4nQ0U#2S2{Q0U#BS2|'PS2}Q0T#2S2~Q0T#BS30<0~3Q2~Q30'1S31Q0O#6#LS0OQ03#OS03$0L$03#LRPQ2~Q31PPQ03#ORH$0L$03#LRhQ2~Q31Ph%KH$03#LRHQ2~Q31PH%6G$0J$0L#K$03#LS32Q2~L04DeDeP1Q0V#2RGQ0V#:+0RR0Q0OPPPGC?P0PPPhPGP0PhPHPGP0PHQ32PGL04Dep+01fS33p+01eS34PuPCp+01dS35Q33p+01cS36ETQ0\Q0]CbP3Q0Y#2S37Q0Y#BS38Q0OPPQ37DiQ0X#2S39Q0X#BS0X'1S3:PPPhQ39Q3:PhPHQ39Q3:PHQ32Q39L04DeS3;p+01iRGp+01hR0p+01gS3<9NuCQ33,CGS3=P?Q0_&0pG20NG0&0A0PGP0PGP0PGP0ER3GQ3441|Q0^Q0P$1{S0PQ0;#f#f#fS0;#6#f#f$0s$03$03#LQ0;#O#f#f$0s$03$03#L,3n81znS0;Q01Q1xP31`GQPGQ33O3b5bGPoANuC0S3>/1tS3?Q0}'3X6AQ0PQ0;Q06Q23P3%<GPGQ33O3b5bGQ3=,5NS3=PiD8Pop+01jS33/jiS3@PfQ3>Q3?Q3@DiX6AP@Q0Z#2S3@%@?'1P3PfQ3>Q3>Q18'1S3?P3DiXY@Q0Z#:S0Z$1yQ0ZQ0Z#IS3A'3Q0PQ0;p+01kS0Z>02N0S3BPoQ3B#;R0/>CS3CP>PsPxQ3BP0%=0PoPCQ1VM9DQ0aDFQ3Cp+01lS3C,^KS3BPqQ3B#;R0/>QS3DP>PsPxQ3BP0%=0PqPQQ1RM9DQ0bDFQ3Dp+01mR0Q33'CS3D,5NS3B#HQ3B#Ep+01nS3E,^KS3F#HQ3F#EQ0l$0>S0lQ0j$0>S0j21w@CS3FQ0h61D@Q1i'W'WS0h'W#|S3GQ0m$0>S0mQ0k$0>S0kQ3FQ0i$0>61D@Q0g$0>S0g'WS3F'WS0i'W#|Q3GQ0lQ0i'W#|S0iQ1j'cS3H'c'c'cPBP@20u@9S3IP5P@20u@7P8&1t@H0}H0}S3JPOP~20q~;P~P~Q1nQ08-0r@S08'hS3K%_hS3L+0g%_HS3MQ1n5X~S3NH0hP~P~Q3KQ3M+0gQ32#_Q1n5X~S3KH0h60=~60=~S3OPDP~Q02-0r@S02%_fS3P'hQ085X~PDP~Q1mQ025X~S3QPDP~Q1mQ07-0r@S075X~P@Q07Q1|Q1}H0W-14~60=~S1}PDP~P~Q1nQ02'hS1|Q3P'hQ09Q1sQ0761R@'hS09Q09Q1s'hS1sQ1|5X~S07GzCqCqCqPEP4b:b;b<X3@XL@XM@XN@X4F1138S3P13H3S1m80KhQ3PQ32/33S3R80KH5G7S3PA49f7%<8S3S1`6Q-0C6S3T1176S3UPfANuC;S3VQ3VQ3U74CS3WCn[[[[^3@^L@^M@^N@^4FP3%2iS3X%BiS3YPPPhQ3XDiQ3YQ3EQ0d#@Q3XP:Q0QQ0TQ0ZO9b5b9b8b0b0bGQ0[#2%@i'1S0TPfQ3>Q3?Q0TDieb11jG?Q0SJ0^Q3=PiD8Q0fP?Q0_Q0^O3N<1sWQW@P5P3O2n2001000000121000000bVWRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000bVWKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000W@W{P5P3O2n2001000000121000000W1WzP5P3O2n2001000000121000000W1WaP5P3O2n2001000000121000000W1WpP5P3O2n2001000000121000000W1Z08JP5P3O2n200100000012110=000bWL1rWjXALX=kQ0veQ0wQ0xQ1wPkPMQ1DQ1kP5Q11$1CJ0VQ1l39PdQ0nQ0{P9P5P;PdP9P5Q0dP3I1nQ1vQ27Q1yQ1tQ2EQ2FQ14Q12'0S123GDdX2J#AQ00PJQ13Q15Q1yQ24Q0=P{Q1qQ0=P{Q12EoDdX2JPzQ1:P7P8C]P3Q25Q1EQ1yQ0|Q28P{Q1qQ28P{Q12EoDdP1Q0?Q0~Q0zQ0NQ0tQ0o74{Q0tP{Q04Q21H0[DdQ1[Q1\P2P:C]P3Q22Q1rQ1hQ0AQ20Q1p74{Q20P{Q1gQ1fH0[DdP1Q1cQ1_Q1bQ1eP{Q1`Q1eP{Q1^Q1]'0Eo3GPrQ1YPUPTC]P3Q1ZQ1SQ1WQ1UP{Q1QQ1UP{Q1NQ1O'0Eo3GP1Q26Q1LQ05Q1{74{Q05/v{Q1zQ16'0H0kQ1JQ1HPXPWC]P3%rTQ1BQ1BP{Q1FQ1BP{Q1CQ1?H0[I01P1Q1>#<Q1>P{Q0>Q1>P{Q1MQ1G'0EoQ1@Q1=P[PZC]P3Q1I#<Q2;P{Q2<Q2;P{Q2:Q2='0EoP1%@]S2=%BYS2:74{Q2=P{%2YS2=#JQ2=Q2:;4nH0[Q2GQ2JQ0EP]C]P3%@^%:ZS2J#IS2:74{Q0F#@P{%2[S0F#JQ0F%B[;4nH0[P1Q2A$0ZQ2NQ2Q'0Q2CQ2RQ0HQ0GC]Q1;Q2M$0ZP|PmPeP5Q2PPvE7Q2@[^2J^>IQ2V'0P1P|PmPeP5P<PvEaQ2@[^2J^>IP|PmPeP8Q2UQ2BE7P|PmPeP9Q2cQ1~EaQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5P<Q0rFsP|PmPeQ1uQ2UPvE7S2V/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5P<Q1lFmQ2V/0=X2J#A[^BM^?p3GQ2OQ2LPuPCQ2KQ2OQ2METP`Q0JC]P3P|PmPeP5Q2UPvE7Q2@[^2J^>IP|PmPeP8Q2n#VS2nQ2BE7P|PmPeP9Q2mQ1~EaQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q2cQ0rFsP|PmPeQ1uQ2nPvE7S2n/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q2cQ1lFmQ2n/0=X2J#A[^BM^?p3GP5Q0L$0?P_P^O3Q2\#JQ2]'0P1Q2^#JQ2_Q2a'0Q2bQ2dQ0RPbC]P3Q2e#JQ2fQ2h7ufP1Q2j/QfQ2iQ2k'0Q2lQ2oQ0UPcC]P3%2b/QfQ2pQ2q+0CP1Q2s#<Q2vQ2w'0Q2xQ2yQ0YQ0WC]P3Q2z#<Q2{Q2|PnQ2}H0\P1Q31/3nQ2~Q30'PQ34Q35PuPCQ36Q34p+01bETQ0]Q0[C]P3Q0W#2Q0W#B;4nQ37Q38'PQ39Q0X<0~3Q3:Q0OPPQ39Q3;DeP1Q3@Q3A'1RbQ0OPPQ3@C?PbPPPhQ3@PbPhPHQ3@PbPHQ32Q3@L04DeQ33PGQ3>Q33Q3<H1oPiP?C]P3Q0]#2R?Q0]#:+0RQ0OPPP?C?Q0\#2R?Q0\#:+0RRiPPPhP?PiPhPHP?PiPHQ32P?L04DeP0Q3CQ0Z9NuCR?Q3DPjQ0aQ0PQ0;Q01Q1xP31`0QP0Q33O3b5bGPoQ3C9NuCRi/1tRGQ0}'3X6AQ0PQ0;Q06Q23P3%<0P0Q33O3b5bGQ3BQ0bD8PoQ3EQ0b'jRbQ03#kRcPiPGPbDiX6AP@Q0^#2%@j'1RbP3PcPiQ18=4i3CnXY@Q0PQ0;Q3EQ0Z602NRiPo%;iRG/>CS0ZP>PsPxPiPG%=GPoPCQ1VM9DQ0cDFQ0Zp+01o,^KRGPq%;GRi/>QS0ZP>PsPxPGPi%=iPqPQQ1RM9DQ0eDFQ0Zp+020>02N0Ri#H%Eip+021Ri,^KRG#H%EGQ3GQ0iQ0mQ0lQ0kQ0j'W'W'W#|Q3H'c'c'cPBQ3JPOP~Q3OPDP~Q02/{{Q085X~PDP~Q3QPDP~Q1}PDP~P~Q1|/{cQ09Q07GzCqCqCqPEP4b:b;b<X3@XL@XM@XN@X4FQ3PA49{7Q3SQ3TQ3UPcQ3VQ3WCn[[[[^3@^L@^M@^N@^4FP3%2jR{%BjRGPPPhP{DiPGPiQ0f#@P{P;Q0RQ0UQ3EO9b5b9b8b0b0bGPbPcP?Q18=4?bCne1j0jQ0VJ0^Q3BQ0bD8Q0fPjQ0aQ0`O3N:1pWQW@P5P3O2n2001000000121000000b=WRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000b=WKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000WKW}P5P3O2n2001000000121000000W1W|P5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000W1WbP5P3O2n2001000000121000000W1WqP5P3O2n2001000000121000000W1Z09JP5P3O2n200100000012110=000bWK1qWkXBMX?kQ0weP|PmPeP5Q11PvEaQ0zQ10Q10Q17P8P9g03KkQ1001k8'gP1&0Z}P|PmPeP5Q1PPvEaQ2@[^2J^>IP|PmPeP8Q19Q2BE7P|PmPeP9Q1[#VR}Q1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q1PQ0rFsP|PmPeQ1uQ19PvE7Rk/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q1PQ1lFm10k=X2J#A[^BM^?pH0IAMdyzQ1:P7P8H0DQ0eQ1P$0ZP|PmPeP5P}PvE7Q2@[^2J^>IP|PmPeP8Q1a#VR}Q2BE7P|PmPeP9Q1d#VRdQ1~E7Q2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5Q1[Q0rFsP|PmPeQ1uP}PvE7R}/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5Q1[Q1lFm10}=X2J#A[^BM^?pH0IP1P|PmPeP5Q1XPvE7Q2@[^2J^>IP|PmPeP8PdQ2BE7P|PmPeP9PrQ1~EaQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5PwQ0rFsP|PmPeQ1uPdPvE7R}/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5PwQ1lFm10}=X2J#A[^BM^?p3GQ1TQ1PQ1[3MQ1\P2P:H0DP3P|PmPeP5PdPvE7Q2@[^2J^>IP|PmPeP8Q0@#VRdQ2BE7P|PmPeP9Q1AQ1~EaQ2D[[^DJ^FI^CJ^EIQ0yPpQ0uQ0MP5PrQ0rFsP|PmPeQ1uPdPvE7Rv/0gX2J#A[^AL^=pQ1wPpQ1DQ1kP5PrQ1lFm10v=X2J#A[^BM^?p3GP5PTQ0:PSO3Q0:#2RS#JPSPfQ0:#:RpPS%IpRpPn1PSpI01H1HP1%2TRp#J%:TRTPp%ITRTPn1PpTI019upfQ1dQ1aQ293MPrPuPCQ1dQ29Q1aETPVPUH0DP3Q1MQ0B#2RUQ0B#:RVPU%IVRVPn1PUVI017ufP1%2WRW/QfQ1oPWQ1KPnQ1K,PWI01Q1AQ0@Q0<3MQ1JPuPCQ1AQ0<Q0@ETPYPXH0DP3Q2=/QfQ0C#:RfQ0C#2RX%IfRfPn1PXfI01P1Q2J#<%2ZRZQ2:PnQ2:,PZH0\Q1<Q1;Q2I3MQ1@PuPCQ1<Q2IQ1;ETP\P[H0DP3%:\#<Q0D#2R\Q0D#BR[Pn1P\[H0\P1%2]R[%B]R];4n1P[]Q2>Q2HQ2?3MQ2GPuPCQ2>Q2?Q2HETP^Q0EH0DP3Q2WQ2XQ0G#2R^Q0G#BR]<0~311^]R]Q0OPPP^P]PPPhP^P]PhPHP^P]PHQ32P^L04DeDeP1Q2[Q0H#:+0RR1Q0OPPQ2[C?P1PPPhQ2[P1PhPHQ2[P1PHQ32Q2[L04DeQ2CQ2AQ2K3MQ2MPuPCQ2CQ2KQ2AETQ0IP_H0DP3Q2`Q0OPPQ2^C?Q0J#2R_Q0J#:+0RR1PPPhP_P1PhPHP_P1PHQ32P_L04DeQ2LQ2K;M<Q2OQ2YQ2ZPaP`Q0PQ0;Q01Q1xP31`<QP<Q2KO3b5bGPoQ2O9NuCR_/1tRtQ0}'3X6AQ0PQ0;Q06Q23P3%<<P<Q2KO3b5bGQ2Z,5NR1Q0KD8PoQ2gP_PtQ2fC?X6AQ0PQ0;Q2SQ2L602NRAPo%;ARt/>CR_P>PsPxPAPt%=tPoPCQ1VM9DQ0LDFP_Q2T,^KR_Pq%;_Ro/>QRtP>PsPxP_Po%=oPqPQQ1RM9DQ0RDFPtQ2c>02N<R<#H%E<Q2b,^KRK#H%EKQ0h#|Q0jQ3F'W#|RKQ0kQ0jQ0gQ1i'W'W'W#|Q1j,cK'c'c'cPBP@Q3IP520u@8H0}POP~20q~6P~P~Q1|Q3L+0gQ3NH0hP~P~Q1|Q3M+0gQ3KH0h60=~60=~PDP~Q1}PDP~P~Q1|Q09Q1sQ1n5X~GzCqPEP4b:b;b<X3@XL@XM@X4F1135R4Q1m80KhQ3R:0K4H5G8Q3S1`8Q'0P9P8ANuC7RuA4uC9Cn[[^3@^L@^M@^4FP3Q2uPPPhQ2rC?Q2bQ2tQ2rP;Q2SO6b5b9b8b0b0bGQ2e%:`+0RQ2YQ2YQ18Q2e3440KeP1Q0KD8Q0QPaP`Q0JQ0IO4N:1jWQW@P5P3O2n2001000000121000000b=WRWUP5P3O2n2001000000121000000W1WTP5P3O2n2001000000121000000W1WKP5P3O2n2001000000121000000W1W@P5P3O2n2001000000121000000b=WKWSP5P3O2n2011000000121000000W1W@P5P3O2n2011000000121000000K1iWmWoZ07JX>IQ0xeH0lK0PK0PQ0pPlQ0q-1uRQ0sH1vebwbsbnblWyWiP5P3O2n2001000000121000000W1WZP5P3O2n2001000000121000000W1WhWgP5P3O2n2001000000121000000W1WfP5P3O2n2001000000121000000W1WeP5P3O2n2001000000121000000W1WdP5P3O2n2001000000121000000W1P5P3O2n2001000000121000000W1W`W_P5P3O2n2001000000121000000W1W^P5P3O2n2001000000121000000W1W]P5P3O2n2001000000121000000W1W\P5P3O2n2001000000121000000W1W[P5P3O2n2001000000121000000W1P5P3O2n2001000000121000000W1W~P5P3O2n2001000000121000000b1WrWxY0<Z0:@Y04Y0;o"). Qed.


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
  rmrep st m -> munch W m m' -> wmono psegs m m' -> W_high W -> rmrep st m'.
Proof.
  intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (D : forall a n, a + n <= ATOP -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).
  atop_facts.
  assert (TC : forall A cs, rw_cells psegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells psegs m' A cs).
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
  wr_at psegs m a n -> 0 <= n -> (a + n <= 0x10000 \/ 0x59000 <= a) ->
  exists bs, length bs = Z.to_nat n /\ bytes_at psegs m a bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocRep ()) ["CANSEC1"] "p'0h04__x1h14__x2h22bsh37__arithh44__ffh58__varmaph65__with74__x3h82H1h91ih:2z1h;3Hk0h<4__p1h=1bi001bh>4cstrh?1xi011xh@1HhA2L0hB2HihC1WhD5cstr0hE1mhF4__p2hG6__sat2hH4__x4hI1khJ1yhK1zhL1BhM1ahN1ehO1ni021nhP1oi031ohQ2HahR3Hi0hS2HkhT1LhU6__sat1hV4__x5hW3bs1hX3bs2hY4segshZ2A0h[2Anh\1Gh]2H2h^2Hbh_4Himgh`2Hnha2IHhb3REChc5cstr1hd2z2p%0p&0p;1p;4p;2p;3p;6p;<p;5p;7p;8p;Bg007Xj1HTg00iTk10DTg00j2k10@Tg00R]R0k10wTg0120k40eTg008=j1kTg01W9k20YTg01;kk10LTg00NQS00j2;Tg008[j1qTg00WDS01j23Tg00[Ij2]Tg005Bk101Tg01>?j29Tg0186R1j1@Tg00`XS02j2=Tg00X\R2j20Tg01Aoj1jTg02eak20WTg02fIk30STg02fmk20RTg005bj2aTg011QR3j14Tg01a7j2gTg009@k10;Tg01:Fj2tTg013@k10vTg013^k10uTg014Ij2nTg01:dj2pTg015Wk20bTg0169k20aTg00;8j38k10<Tg016ek30`Tg017Dk40_Tg01iRk20GTg01VVk30^Tg05GWk20FTg00?Cj6lTg05HOk30]Tg003Ok60ETg00T9j2xTg01d4j4wTg02hlk20\Tg05IPk30ZTg018mR4j2BTg01LDR5j11Tg01`AR6j2_Tg05JOj3dTg01eej4ATg012bk10VTg05Jmj3vTg00URR7j2NTg01fLj1GTg00PHj4YTg01=Tj4ZTg03@7R8j2>Tg01`Yj1}Tg01G?l<OTg01k[k60QTg01dek20PTg01eHk30OTg009`j3KTg01a`k10MTg01b>k20UTg01b_k30KTg01RTj3{Tg01D[j4ETg01S1k50tTg01?Yk10rTg05KPk40oTg05L1k30lTg00Z5k10kTg01nik30HTg01cHk206Tg01R6k40jTg014lk404Tg01EPk705Tg01HHk70iTg01<Mk30hTg01;Gk70gTg01=0k807Tg05Lnk308Tg019Gk20fTg01F4m<09Tg019dk20pTg01Gdk60dTg03cSk40cTg01FYmB0JTf0R9#H#Hp>03g00OjR:/39p=5f2R;f1R<'0/39p=?1N<9,;;p=[10<9#jp=ug00<WR=@0l<9p=cA8;<9$0kp=V%H9#H#H#Hp=oP=P;P<P9CEp=Cg01KeR>?8;</;9p=e1N:9p=ig006<R?@0H<9p=^g01OUR@B0H?;<g0231RA+06;K9p=MP?P;P<P9H0jp=XP;g01IfRBg01JERCPCg01JeRDP?P<g01PAP9H04g01KEREK05p=7P?P<g01PhP9H04p=sP<PBPCPCPDP9PEK05p=rP;PBPCPCPDP<P9K0ip=QB0h?<9p=IP;PBPCPCPDP<P9K0gp=mf6RFPBPCPCPDf5RGf4RHf3RIPBPCPCPDP;P<P9L07L07p=FPIPBPCPCPDP;P<P9L07p=fB08=<9p>0[B08=;<=8I9p>0CA8><9p=D1><9,0;p=<P=P;P<P9CE,;Ip=|10;<#j:08=I=8H9p=S20f:9p=61a?9p=2P?P>P?P?P1PHP5PIg01LdP;P<P9N<09p=RP>P?P4P5Q01g01NTR1g01O6RJP:PIP;P<P9M<Op>0B20p:9p=U1N:HA8?I;';13<:A8?9:';']p=W2069Ap>0XAK@<9p>0AP>P?P6P5P7g020hRKPIP;P<PJP:P9M<Op>0TP<PBPCPCPDP9J0dp=hP>P?P4P5Q01P1PGPHPIP;P<P9M<Op=`P>P>P?P?P3P5P5PIg022MP;P<P9N<09p=PA8>GHP=PI10;<P9CE';p=T%19,><p=JP=PI10;<P9CEp>0?P?P?g045fP9H0cp>0>P>P?P?P?P5P5PGPHPIP;P<P9N<09p>02P?P?P?P?P?P?P8P9P<P;P8PIPHPGPFf7R8f8R3f9R1NB0Jp=yP?P?Q01PGQ01PHP:P:PIP;P<P9M<Op>0=A8?<9p=:P>P?P9P5P<P;PIPHPGPFP8P3M<Op=b%19,3:p=\P;PBPCPCPDP?P<g01QOP9H04PEK05p=LA8?9:p>0NA8?;<,;I/]9p=~139:p>0:P=PH%1<,>;,0IP9CEp=zP?P?P?P?P?P?P2P9P<P;P2PIPHPGPFP8P3P1NB0Jp>00A8?9:,;<p>0sP>P?P6P5P7PKPGPHPIP;P<P9M<Op>0q10;</09p>0I206<A=K@9p>0n13<:/;9p>0mg00<2RA#HRK#HS03#HR5#H$03R6$0DR2$0@&0D5$0@R5$0wRE[S04P=P;P<P9H0eQ00%5;RB%kKR4%k6RL+0YRM9?;<%59RN?[9;1uH<,cG&0L5RO5VE[^9?';&036#o#o#kR69?HI%HA#q#q$03#q#o#o#o#kRP/3H']&015RQ1959RR%@GAC8F93eX2Q'=[\BP9%5HS05A?GHMA[N9G1u8<,c3=VEO[^9?';Q00A?FGMA[N9F1u3<,c1=VEO[^9?%5F1038RS/3613P3']%@1f;RTf:RU;C95eRX2Q,=Q[[P913SMA[N91f<RS1uT<'c=VEO[^9?%51A?TU613PT']A[N9SRVPHP<P9O2f?RWf>RX/u<'c=VEOPEf@RY10W;RZ#jR['cAVE9OR\XPEP9PYP[O1R]P?PZ%kAR^,09R_/3613P9']XK?R`20W4LRa%i4Rb%5L%iM[Rc[Rd%54Reg02gNRfB0S4L<UWQRL%5M\f^QeReP<g02gj20R:4'aPbeO1RbPc%4JRf#4Rg#4Rh,g?Ri1g?gRg1g?fS06'^%4hS07,g?S081g?JS09,^gRh&0;@Rj3MRk3M&01@R@1t?;Rl1t?IS0:7X<S0;&0v?Rm&0u?Rn1n?:Ro1p?KRp57nS0<%qA,p?Rq,sp,rn5QnRr&0LCRCPn1p?ARs/IqRt1n?6Ru57n1n?PRv=7ns5mnPC1IspRw1n?^Rx'I=7nuA7nvw5mnFF20bnDRDP9P;g00c@Rvg00c`Ru'a20a9;=8vudB0`?:<H0_Rub4b5b6X0?X1?X7?Rv%5<Ry?[<;Rz10<IR{/3613P<']10;IS0=??^6Q0=,3P'][[^0?^1?^7?RPP9fBR6PFfCR|PGP8O5b3bGbUbG20G2[Q08Q06Q09'^S0>;Mj9MihP@Q0;PmPnPrPCPn1n?4>0^?2R497ntPCPnA7nosS0?PCA7now1sw4,rn5QnCfFFPDPub4b5b6X0?X1?X7?Rt13{M10IHR{#5?[{M\B[\z^0?^1?^7?RzP9PWPIPYP;P8PTO6b3-0FZEl:0]Y[J0EAVE]OPEfAR]10YIRZ#jR{O1Rr1x59Rh98E<X=5,=5XPEPrPEP0P5A8E;hX=5,=5^C\P9AVEhOP51x5;=8EhX=5P<1x5<,aECwWCX=5P9O1AVEOOA8EOhX=5,=5P91aEOO1+0\WCn10110300021010000P<O1bP20[]{P?PZP`PaPdPLPePbPcPvPPP9P|P8fDRPPFP3O5b3bGbUbG20G2{PtPzP9PYPHP]PIP3PSO6b3-0FZEl:0Z]{ElbCbCWBX9?PEPYP[PhH0CX=5,=5\V^9?%@XS0@,B91DR;S0AP6%1;RV9<]YP9C|X2Q,=Q[S0BXI>f=R[#@R{,BJPQA8>RJP]%1JRZ9<YWP9C|X2Q&0;5Rz195zRt=8>JA<WXZR2=CYz1a>J%52%1t=?2MR21_9tRtPEP6A<]YZ%1<RvAd5z<DS[^9>Rc';Q0@,BJ%6XS0C#5Rb1a?:S0DQ0@%69X??RePXO1P9X??RLPePXPX%2XDRH0BP9CARdPb%UWRaPW%6WR`PWPWP`DWR`%6YROP?Q0>,^gS0E$0XS0F00AjP@&0V?R\9Xl<S0GPmPnQ0<PCPnQ0?PCAv?po,IsR097noFFPDPub4b5b6X0?X1?A<;I:#5\y\y^0?^1?P9P6P|P3PXO4b3b:b8b;P2PcPdPbPaP`POP?PjP@Q0GPmPnA7nw4S0HPC1I0o=7n4CfPDPub4b5b6X0?X1?A?9<MA<<;:??:M[^0?^1?P9P6P|PUO3b3b:b8b;P2e1_<J1Nv:R2P<Pv%2vS0IQ0DH0TP9CAP2%@]S0J,BJ%6]#5R2Q0DQ0JPeP]O1PLPeP]P]%2]DRH0BPICAP2%GIR2%1IR0#5Rw%U|P|%6|R`P|P|P`DW%6PP?p-0RaPjP@1t?<S0K9X\<S0LPmPnA7noqS0MPCPn1sqo,rnPC1hnIS0NFFPDPub4b5b6X0?W<1N<:PI[\N^0?^<aP9PEfHRbfGRdfFRc;<Z%18RyAd5z8DSPyPIPGO4b3b:b8b>b;bRXBtX9>CYCYCYCwWSQ0B%4<S0O%@WS0P'BP<%@YRt,B;13VOP;PV%2VRrPtPOPLPePYPY%2YDRR}E`%4;R~/BtA?V^OROP~P_X??R~PVO1P~P;PVPrCPPtPePYO1P}E`P9CAPOP2Pw%U6P6%66RwP6P6PwDWP`P?PjP@Q0GPmPn1IsxS0Q=7npPCA7nspCfPDPub4b5b6X0?X1?13_<13<;[^0?^1?P9P<PyPHO3b3b:b8b>b;CZO1PRPIP|P61>]0P9ETX2Q,=QQ02PQPRPHPPP|%1HS0R,>6P9ETX2QPR%4GR0fER_PP1J|0P9ETX2Q,=QP9PRPFPcP_1JPFP9ETQ00195<S0S/D8PdPc1>_yP<H0?PR%41RyfIR0Pb1JdyP9ETX2Q,=QP9195IS0T/D1fJR1P0%1US0U,>bPHH0?P[%4TS0V#1S0W,>0Ry%5yS0X1Ny0R`';%1TRw/0^R2,>0RO#5R}1NO0Rr';Q0XP`P}PrPL13<9#}XJ?X??S0XQ0DPyPOPLPLPL1><9$0>#2XE?XO?S0YP0P0%20RrQ0WP2PLPL%19R}#2X?>S0WQ0VP2P~PTPw%2wR2CPJ02M:yR`J0=P?P?P7PLP71N<9#}XJ?X??PyPOP`P0P0PrM<OJ0Q195GRr/DT%1rR`/:wRO&0<>S0V&0<?Ry1:v}1D<920P<940OXJ>X?>S0ZPrP`%2`S0[PTPwP2M9bP<CAPO%4SRO%@1R2'B%1SRw%617?^R}POP~PwO1P~PSPw%2wCPP2PeP1O1PLPeP1P1%21DRE`PUCAP}%G[%\[1953R}#G%\}fMR}#UP}%6}R2P}P}P2DWfNS0\#6P?Q08Q0E;MkP@Q0:?XI\9Xl<PmPn1hnGS0]%qK,p?RK=Lns5Qn1hnFALnKoS0^5Qn5mnPCPnQ0<PCPn1IpxS0_=7nKPCPnQ0?PCQ0_9v?sRl97no1sls,rn5QnFFFFPDPub4b5b6X0?X1?X7?X<aXFaPIP;P9&0N;S0`,;HC~A?I^H%5IS0a10G^,>HS0b#5Q0b;[H[[\B[^0?^1?^7?^<a^FaP9fPRl$0:%ilP<%16RkPlP;PHPGPcO9b3b:b8bDb>b;bACZO2PEfLS0cfKS0d1J1OPhDSX=5,=5Q02P5PEP}Q0cQ0d%4['JPhDSX=5PR%4XROQ0\P}Q0c/JOP9ETX2Q,=QP9PEfOROQ0\%4W,J}PhDSPQ%4]RhfQR}%1hS0e,>OS0f,0lR2;C95eRX2QAK5<URw195w%4YS0g'DS0hPlPOQ0\Q0gPwDz195URw#4S0iQ0g'D%1wRS/0^S0j%1YR7/0^S0k':Q0VPyQ0ZQ0iQ0jP~PwPS%2SS0jCPQ0gQ0kP~PYP7%27S0kCPM9b1DwY1:S7S0gQ0VPyQ0ZPwPSQ0jPYP7Q0kM9bPFCAQ0g%@OR7,Bh%1]RS/0^S0g%6O'3RwPhP~PSO1P~P]PS%2SS0kCPS0jP7PePOO1PLPePOPO%2OS0iDRE`PWCAPw%G6%5k195[Rw#G%\wfRRw#UPw%6wR7PwPwP7DWfSR7#6S0lP?&0MA-0U?S0mQ0660K?Q09;MjP@Q0GPmPnALnspPCQ0QQ0_5LnCfPDPub4b5b6X0?X1?1:9<10<^S0_10;^S0Q':[^0?^1?P9%1dS0G195]S06#1RAPFO3b3b:b8bDb>b;bACZQ0heg01Sj$01S0hQ04Q00PHPIP;A{5<9CEPGPHPIP;CEPGPH195;#1,0IP<CE';S0n[PHPIP;P<CEPHPIQ0S#1,0;P9CE';PGPHPIA{5;<CE[S0oQ0nPFPGPHA{5I;CE[PHPIP;P<P9I0tP9n2001000000120000000XXQXWQXM?WEWYQ0hQ04Q0o^XQ^WQ^M?]E]YP9P=P}P2AK5;zR=PTAC}2=195=#1,02R==C}TS0h%52S0413=MS0oAK5Iz,95,_9S0nPEP7%4|#19<w}PvAK5Hz=d5<DS[^9>S0p';Q04Q0g,>OS04,0lR=#5PLQ0XQ0DP2P=PLPLPL10<9$0>#2XE?XO?S0DPlPl%2lS0qQ0fQ04PLPLPLQ0YPOPOQ0iQ0eQ0gPLPLQ0WPhQ0gQ0jJ02M:yN:00S0jJ0=195TRT/D]%1TRh/:SS0gQ0VPyQ0ZPTPh%2hP]PSQ0kM9bP8CAS0kQ0g%46S0e%@lRh'B%6l9?k^S0iQ0eP~PkO1P~P6Pk%2kCPPhPePlO1PLPePlPlQ0qDRE`PYCAS0qQ0i%G|S04%\|S0f195XRh#GS0r%\hS0s%U7S0tP7Q0lP7P7Q0lDWS0lfTS0u#6S0vP?Q07#4,g?RhQ081^ig'^Q0>,^i=Mhj3MP@1t?H?X;\S0>1t?G?XI\7X<PmPn1hn8ALnKp5Qn1hn3Q0^5Qn5mnPCPnQ03,p?R\97noS03PCPn1IqxS0^=7nKPCPnALn\qS08PCPnQ0?PCQ0^9v?p,IsS0?97noCfFFFFPDPub4b5b6X0?X1?X7?XH?XV?X<aXFaPGPHP<20sFHC~Q05A?H^F1:FGQ05108^9<GF#5[[[[[^0?^1?^7?^H?^V?^<a^FaP9fVR\$0:%i\P<1956#1S05%1bRKP\fWS07P;PIPGPFPwO<b3b:b8bDb>b;bACZQ0oQ0p102^Rh/3M10=^RT/3MP?P?Q01PLQ01Q0XPhPTPLPLPLQ0DP2P=Q0jP^P^%2^R=N:00S0jPMPM%2MM<OQ0kQ0gQ0qQ0iQ04Q0fQ0rQ0sQ0tQ0lQ0vP?Q0E=MijP@Q0>Q0:7X<PmPnQ03PCPnQ08PCPnQ0HPCQ0?/IxR2=7n4CfFFPDPub4b5b6X0?X1?X7?XH?Q0a1:HIQ0=/3MQ0b,0I??^M[[[^0?^1?^7?^H?P9Q05PKP\Q07PIPFQ0\O7b3b:b8bDb>b;bACZQ0oeQ0nP>1_9fPEfURMQ0u%4_#17<7PvAK5Fz=d5<DS]BP<1_JfP?%4P#19<7wRwPEPM%j91x5FH0CXK?PH10w:&0rwElPEQ0uPwPZAK5Gz=d5JDSeWB%49/_fQ0O/_f10v^/N^RJQ0OP~PvO1P~P<PvQ0ICPPfP^P=J0qP9CAPJQ06/DdQ0G,:ARJQ0VPyQ0ZQ06PA%2APdQ0GQ0G#2M9bP[CAPJ%4bRJ%@\RA'B%6\9?K^R=PJP~PKO1P~PbPK%2KCPPAPeP\O1PLPeP\P\%2\DRE`PcCAP=%GHQ0R#5%G1%\1195_R=#G%\=fZR=#UP=%6=RAP=P=PADWf[#6P?PjP@Q0LPmPnQ0MPCPnQ0^/sx,rnPCQ0NFFPDPub4b5b6X0?X<aQ0_/N^PI[\N^0?^<aP9PEf_f^f]%4O#13<%4URU#1AK5Yz=d5UDSQ0UPGP3O4b3bdb]bcbDb>b;bAbRWBX9>P9O1n0110200020011102P9O1WBX9>CYCYA<lOSRS/:hRO1:STP?P?PyPLPy1:<9#}XJ?X??R3PSPS%2SPhPTQ0jM<OQ0kQ0gQ0qQ0iQ04Q0fQ0rQ0sQ0tQ0lQ0vP?PjP@Q0;PmAv?pq,IsRT=Ln2PDPub4b5b6X0?X1?X7?A<9<;Q0Q,><>0I9^':^0?^1?^7?P9PKP\Q07O3b3b:b8bDb>b;bACZPOP?A<}lkAC79[XK?P8Q0e,Jl>0I}^P9J0Eb@Q0heCYO6b@CYCwW^X=5P<P9O2n2001000000121101000bNWLWTP<P9O2n2001000000121000000W@X2QP<P9O2n2001000000121101000bNWSWaXI>P9H0oXI>1B9{Q0AP]A<YWVP9C|X2Q,=Q[^I>P9P{1B{{%6[R>/3>P{P>PLPeP[P[%2[DRRVP{P>PVE`%U[P[P>P[P[P>DWQ0CP?PjP@Q0KPmA7nssPDPub4b5b6X0?1399^0?P9P<O1b3b:b8CZO2PRQ0@PYPWQ0@,JXP9ETX2Q,=QQ02PQPRQ0PP]PYQ0P,JWP9ETX2QAC6]99eRtX2Q,=QP9PRQ0JP|P6Q0J,J]P9ETQ00Q0S%@6Rt'DPPP|P6PtP<Dz%@PRPACc_95eRX2Q,=QP9Q0T/DPPdPcP_%@_PHDzPQ%@dR_AC0b95eRX2QPG%@cRR,DrRPACbdGP<%1RRG,>cRt,0dR6,:dR|%6cRW,>cRY,0dRX,:dP?P?PyPLPyP3PdPd%2dR3P6PXPLPLPLQ0DPdPdP3PtPYPLPLPLQ0YPcPc%2cRYPGPWPLPLQ0WPRPWPLPePcPcPYDRRYJ02M:yN:00M<OPP1:`WRWQ0VPyQ0ZPrP`Q0[PRPePcO1PYM9bP<CAPW195FR5#G%\5%UbPb%6bR5PbPbP5DW%60P?Q0FQ0m>0K?gQ09'^Rg20ngj5Mi+0AP@Q0;PmPnQ0]ALnqp5QnA7npoALnqo5Qn5mnPCPnQ0<PCALnsTFFPDPub4b5b6X0?X1?X7?X<aPIP;P<Q0`-0m<C~A<;IH,:;\B[^0?^1?^7?^<aP9Q0d#iP<Q0dQ0cP;P]O6b3b:b8b>bACZP|P?%1_9<bdAC198XK?P<PbP9ElAC0bFP9bLb@CYCwWLWTP<P9O2n2001000000121000000W@X2QP<P9O2n2001000000121101000bNbbb\W_W`WCW[P<P9O2n2001000000121000000W@WZP<P9O2n2001000000121000000W@XO?XM?WEo"). Qed.

(* [comment removed for export] *)
End CANSEC1.
