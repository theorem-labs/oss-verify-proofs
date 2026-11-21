(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (wr8_comm, rconc_b, rsk_nonneg and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMalloc_fp () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Ubsan:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps@insert_insert_eqC59OSSVerify5KrLib6Malloc9MallocRep<s_shadow_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepCget_shadow_wr8_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@insert_insert_neC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C35stdpp4base6insertI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp:rsk_nonnegC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rmrep_wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_A=ticks_ok_wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_A:rmrep_wr32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib5Ubsan:RMalloc_fp8wr8_commC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib5Ubsan:RF_enframe@renframe_off_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RF_enframeArenframe_tail_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rc59OSSVerify5KrLib5Ubsan:RMalloc_fp8rwr8_repC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib5Ubsan:RMalloc_fp9rwr16_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp=wr16_wr8_commC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z7div_posC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib5Ubsan:RMalloc_fp9rwr32_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp=wr32_wr8_commC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC59OSSVerify5KrLib6Malloc@F_malloc_enframe9land_le_lC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp7rconc_bC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5Ubsan;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib5Ubsan<RMallocKit_A;rpres_writeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepArmrep_shadow_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Malloc9MallocRep;b8_unsignedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepCrreserved_disjoint1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg@ref_seg_rom_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep@rmrep_meta_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fpCrreserved_disjoint2C1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_add_distr_lC56Stdlib6ZArith6BinInt1Z7mul_1_rC59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib5Ubsan:RMallocRepBrwr_at_bytes_existC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z6divideI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_A:b8_of_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fp:rrdv_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC59OSSVerify5KrLib6Malloc=F_malloc_free;bytes_at_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib;setoid_ring<Ring_polynom3Mon00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib5Ubsan:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib6Malloc9Malloc_fp@round_up_pg_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9mf_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A;fact_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>lowbit_testbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_fast;lowbit_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A=mf_free_clearC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A7mf_hdr0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_AAmf_slots_completeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RMalloc_fpArget_meta_rec_st2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g _ ref_reserved).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x2a000 <= b) /\ (b + n <= 0x2a000 \/ 0x5d000 <= b).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "h04__x1h14__x2h21Hh32H0h42Hnh57__arithh64__ffh78__varmaph85__with91bh:1np;3p;2p;1p;4p;7p;8p-1p10000R0p4p7210R1p8p1000Dp4p70R2p10019p4p710R3p8P2p1001Wp4p710R4p8P2p10025R5p4p710R6p8P2P5p4p7210p8P2p1002RR5p4p710R7p8P2P5p4p7210R5p8P2p1002kR8p4p710p8P2p1003Dp4p73110R2p8p1003Vp4p70R9p1004Kp4p710p8P9P4p8P9P6p8P9P8p4p741110R8p8P9P1p8P9P0p4p73110R9p8P3P7p8P3P5p8p1004gR1p4p73101R6p1005AR:p4p73110p8P6p1005ZR;p4p73110p8P6p10066p4p710p8P6p1006IR<p4p7201p8P6p1006[p4p7201p8P6P9p8P6p1006mR9p4p73110p8P6p1007AR=p4p73110p8P6p1007[p4p7201p8P1p4p710R6P:p4p710p8P6P;p4p710p8P6P7p8P6P5p8P6P0p4p710p8P6P9p4p710p8P6P=p4p710p8p1007nR=p4p710R6P3p8P6P7p8P6P5p8P6P2p8P=p4p741110R=p1008Bp4p73101R2p8P2P4p8P8P1p4p7511100R4p8P4P8p8p1008^p4p741110R8P1p4p76111100R4p8P4P8p8p10096p4p741110R8P1p4p771111100R4p8P4P8p8p1009Vp4p741110R8P1p4p7:1111111100R1p8P1P8p8P<p4p7200R<P=p8P=P<p8g009mj3]Tg00:ij3DTg00;Cj2ATg00;_j3KTg00<gj2>Tg00=Dj10Tg00=ij19Tg00>Gj12Tg00>lj24Tg00?Gj15Tg00?fj2:Tg00@Oj3=Tg00A8j2CTg00Adj1XTg00BDj3BTg00Bdj1VTg00CDj2UTg00Cbj1TTg00D@j4PTg00D^j1OTg00E<j1NTg00Egj2?Tg00FJj3LTg00Fmj26Tg00GPj1JTg00H2j4@Tg00H]j2ITg00I?j2QTg00IYj2HTg00JEj3RTg00Jdj4STg00KVj2GTg00L2j2\Tg00LLj7FTg00M0j7[Tg00MTj7ZTg00N8j8YTf0R<#0#0p=W%0<#0#0#0p=;%0<#0#0#0#0#0#0#0p=8f3R=f2R8'Gf1R1/G<'\p=1P8g00N\R4g00O;R2P2g00O[R6g00P;R5P1g00PYP<C@g00Q@R7FFp=3P8P4P2P2P6P1P<F[p=7P8P4P2P2P6P1P<FZp=<P1P4P2P2P6P<P7FFp=MP=P4P2P2P6P8P1P<GYp=Eg00Q`R4g00R@?]1<g00SBR73Dg00SbR3/A1AK=811>=8R9g00T@R0#0R;#0R:#W#;#8#9R>%2:#0#;#8#9R:P=C1P9P:%00#2#0#2#0#;#8#9R?P=C1P9P?%00#2#0#2#2#;#8#9R@P=C1P9P@%00#2#2#2#0#2#;#8#9R9P=C1'4'4'4g00TeRAg00UQ#5#5RB#5RC#5RD#5RE#5,:51:5E1:5BRB5=55=5g00V0RE'C1:5D1:5C==5B5=5/CE%XA5BA3B%VAP51U58P1%T5CP%O5%N5RA1?50R01?5;R;5L5RE165>53ARB165:RC=3A057AA3AEC165?RC=3A0RD57AA3AECRC165@RF=3A057AA3AEF1659=3A0R057A5<A5<A5<A%J2R2PAP51653g00V\P;C@,MAP2A7ABDA7AC05<ACECE1IA6P<P81Q471H<8=D47dAR531CSb6b7b8X05X151><1R7P>P:P<C1P7P:P?P<C1P7P?P@P<C1P7P@P9P<C1'4'4'41A381>8=R=P>P?P8C1P=P?P9P8C1'4[[^05^15P<f4f5P1P8O4b5b3W4W2X:5X95o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof.
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma rconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma rsk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma rwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr16_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

(* [comment removed for export] *)
Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
  wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof.
  intros Hf H0 H1. unfold wr16.
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma renframe_mrep :
  let res := enframe_at st2 g k n off in
  rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
  /\ ticks_ok (fst res)
  /\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  rpres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

(* [comment removed for export] *)
Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
  rmrep st m1 -> unk_agree st o m1 ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  bytes_at usegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read usegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). atop_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rmeta_chunk_facts : forall st m g,
  rmrep st m -> meta_slot st g ->
  let G := conc st g in
  rw_cells usegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= ATOP
  /\ (G + 40 <= 0x10000 \/ 0x2a000 <= G) /\ (G + 40 <= 0x2a000 \/ 0x5d000 <= G)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "p'0h01Hh14rid'h22r'h32r0h44rid0h51ri001rh64__x1h74__x2h84__x3h94__x4h:4__x5h;4__x6h<2arh=5ATOPRh>7__arithh?4__ffh@4__p1hA8__varmaphB5__withC4__x7hD1ahE2H0hF3Hr'hG1bhH2ghhI2r1hJ2r2hK4rid1hL4rid2hM1khN2H6hO4__p2hP4__x8hQ4__x9hR1oi011ohS3ridhT2CahU3DA1hV3DA2hW2H1hX3HrahY3LRahZ2NKh[3RFah\4RaALh]4RaB0h^3RaCh_3Sa1h`2_Hha3H10hb2H2hc2H3hd2H4he2H5hf2H7hg2H8hh2H9hi3_H0hj6__sat3hk6__sat4hl1ehm1ghn3rgaho1zhp4DISJhq2Eghr1Ghs2HGht2Hahu3Heqhv3Hk'hw3Hkkhx3LR'hy2MRhz2MSh{2NEh|3Sa0h}3SaLh~2WFi022WRi033_H1i043_H2i052a0i063arai075heq_Gi082kki091mi0:2sti0;1xp%0p%1p%2p&0p&1p;1p;3p;2p;4p;6p;8p;Bp;7g00=Dj19Tg015mk10aTg016Kk10]Tg016nS00k10KTg017Pk30kTg02k:k21<Tg00o8k206Tg025Pk20~Tg02l9k20}Tg02m9k40zTg00>Gj1@Tg00=ij1QTg00<gj20Tg02[ik11XTg007nk40RTg002kk40QTg00mdj11Tg00Wcj1mTg02\_j1GTg00KVj23Tg02mok60wTg02Tck20LTg02Udk30\Tg02Vck20ZTg02Wfk30YTg02Xgk20XTg02Yik20WTg02Zkk20lTg01A0j1RTg01Afj1VTg019Ij1NTg00:iS01j34Tg00WCk21CTg01:Ck41;Tg01:ak619Tg02]Zj1aTg00>lR0j22Tg01;Bk105Tg01?Wk20NTg00;Cj2CTg01T[j2_Tg02eFR1j2[Tg02o5k60|Tg01@9k100Tg0305k80yTg0316k10xTg02^Rk10vTg00I?j2~Tg00?Gj1KTg00?fk20[Tg00Adk10uTg00Bdk10tTg00Cbk10sTg00D^k10rTg00E<k10qTg00Egk20pTg00GPk11\Tg00Fmk20oTg00H]k21[Tg00IYk21ZTg00JEk31WTg00Jdk41VTg032:k41STg00lbk41QTg001Wk60BmB1@k71ATg033Ck21PTg033Xk40UTg0342k41OTg01Vnk11MTg01WLk21LTg022?k20ITg00n[j2qTg0351k31Fk21ETg01Ybj2ITg01YAk20iTg013Bk207Tg01ZBk20hTg01Zik20bTg01[Pk20gTg01\6k20fTg01\\k20cTg013_k21DTg01f7k20GTg01J3k61BTg035bk21:Tg004Kk61=Tg02P\k61>Tg00fWk21?Tg01I4j4lTg01?Cj6xTg00L2S02j2uTg009mk30eTg0025k30jTg00g6k317Tg00@Ok30?Tg00A8k20dTg00BDk316Tg00CDk21KTg00D@k40VTg00FJk315Tg00H2k40>Tg00LLk70CTg00N8k80@Tg01Wmk30mTg022hk314Tg01Bbk313Tg01IOk61TTg00MTk71UTg00M0k712Tf0R2#9#9p>0E%92#9#9#9p>0;%92#9#9#9#9#9#9#9p=|%@2#@p>1Gg01JWR300N2p=Af5R4g00hGR5P3f4R6f3R7f2R8f1R9#NEx;42p=8g01MGR:&002g01N?R;34p>0O%R2#Vp=E13781392'up=61389/22,27,26p=o1[32p=513461378'u1[52,29'2p=;g00SbR<f7R='Cf6R>/3413671389'u/22'2'2p=>1292,28p=H1C<2p=O1067/381392'up=d13671389'u/22p>0ng00P;R?1I92;4<p=W1089/32p=Dg00R@R@@0e92p>1Jg00Q`RAg00SBRB742,29p>1I13<9/22p=JP5P3P6P7P8P9Ex=442p==%R9#V,08/32p=U1389/u2p>0PP6g02jCRCP7P8P9P2Exp>0920NC2p>0=B0j5?2p=eB175?2p=713<2p=?1392,28p>0D1I89=4?</22p=FP6g01KPRDP7P8P9P2Exp>0413671089/32'2,24,2>p=<1[52,29p>111C<71389/22'2p>10g000DREPCP7P8P9%a2Exp>03g036c/q2p=wg037]/02p=vA4E92,28p=hA4789/22p=\PEPCP6P7P8P9Ex=442p>0`1C92,28p>021_9294E8p>0_P5P3P7P8B0j5?9P2Exp>0120678109254?p=b%m9/22p>0{&009=4:;#m/22p=c1C<9/22p>0^1078/39/22p=X1C<71I89=4?</22'2p=`%R2#V,09p=jA4:2;#mp>0FB0e@92=4ABp=S%@2#@#@#@p=t1389/22p>0MA4?92p=Z20[?2p=MB0??92p=^B0??92g00V0R@+0dp=Yg00TeR;@1692p=L21K?2p=gP?P?P6P7P8H0VP9P2H0Vp=p20p?2p=]20o?2p=rB15?92p=:P?P9g00V\P2H0>p>0<P9g00N\R:g00O;RFPFg00O[RGP2g00Q@RHK0Cp=}P4P:PFPFPGP6P:PFPFPGP?P7g00PYRIP8H0>PHK0CP9P2L0@p=nA4A2Bp>1Y20689=4?2p>1R1[52p>1NB0m?92p>0JB14?92p={P?P8P9P2H0Vp=fB13?92p>0:P8P:PFPFPGP?P9g01]XRJP2H0>PHK0Cp=sP8P:PFPFPGP?P9PIP2H0>PHK0Cp=BP9P:PFPFPGP2J1Tp>0HP8P:PFPFPGP9P2K1Up=zP>P:PFPFPGP4P6P7P:PFPFPGP8P9P2L0@L0@p=P109294?8p=i20d2@p>1HP?P9PJP2H0>p>0TP7P:PFPFPGP8P9P2L0@p=kP6P:PFPFPGP7P:PFPFPGP8PHK0CP9P2L0@p>0SA4?2<p>0AB0??92:0??8p=TB0m?89>0??2p=yP8P:PFPFPGP9P2K12p>081392,u8p>18g00i^g00T@RH#9RJ#9S03#9S04#9R@$0ERI$0a$0]Q04$0a$0]$0K[p,2rcRK@0k8921<7920668P?g02e`P6P220~47-0}4H0zP2%@JS05#9$0E#QRL,02RM&1XKRNPM&0EI$0;RI$0;#QRO%9H#@#9#@#9$0;#|#QRPP2PMPP%9H#@$1G#9#@$0;#|#QRMP2&0K3RQP5g00jWRRg00k0RSP3H0RRTP5PRPSP3H0QRUP9P=%A2RVE8RW&0O9RX106LS06%18RY%E8S07,0YRZP6C6[[^23^15PW&0O2RW#mR[%G2R\P8108LR]%12R^%E2R_'0R`'3DoX33#5X45E;G>PKP4P6P7P8P9J0wP8B0kK46P020LK>B0\K>420ZK4B0YK>420X>420W>43H3H%O8S0813]NP]POPPP8P]PPPMP8PQPTPUP9f9R]PVE8RaP>PLPYPZP>Dd\X[^23^15PaP[P\P6Q06/3`DoX33#5X45E;I0n3HP2f8Ra-0LKB0\K]a20ZKaB0YK]a20X]a20W]a3H3HP9f:Rb-0LKP0f;Rc-0lKPQPTPUP9f=RdPVE8%19S09#OS0:Q09%QIRI'WS0;%R9ReQ09%VeRe;DNRfQ0901Je+1I'J3HRg[^53^S5PQPTPUP7f?Rh#NRi%A8RjE=PQPTPUP8f@Rk#NRl%A9RmE=A4547#m%14Rn%E4S0<'0S0=%G7%17%G4S0>7U740P[Ro[[^J3^L5^I3^K521C5?Rp&0KCRqPpPEP5PRP?g00kNRrH1;RsP5PRPSP?Prg00kgJ19RrPCH0RRSPEPsPrPCH0QRRP9%adI09&0=2Rt34PQPTPU%e7RuPiPVE=Ri%77Rv#?RwADvI_10^v:0D[\9FvI3HRx'2X53#5[^<C]D&0KDRyPpPEPsPrPDH0RRzPEPsPrPDH0QRrP9&05dI0420ND2Rs34PWPw%Q@R@,0vP_1Wv@DoR@,2iX53#5[^HD^Gp'23HP=10=LRiPNPiPOPPP=PiPPPMP=PQPTPUP9f>S0?PVE8Ri10cLRvPYPZPcC6\X[^23^15PiP[P\P]P]PLP`F<X33#5X45E;G>P220lKdPQPTPUP9PlPVE=Pg[^53^S5PQPTPUP7fBRl#NRiPjE=PQPTPUP8fCRw#NRWPmE=Po[[^J3^L5^I3^K5PpPSPRP9%akI09=4qtPQPTPUPuPiPVE=R{/2xX53#5[^<C^DpPpPzPrP9&05kI04=4ys12{@X53#5[^HD^Gp'23HP0PQPTPUP9fAR{PVE8Pg[^53^S5PQPTPUP7PWPjE=PQPTPUP8fDR|PmE8Po[[^J3^L5^I3^K5PpPSPRP9%a{I09=4qtPQPTPUPuPWPVE=R}/2xX53#5[^<C^DpPpPzPrP9&05{I04=4ys12}@X53#5[^HD^Gp3HPcPvPNPvPOPPPcC6S0@PvPPPMPcC6S0APQPTPUP9PiPVE=Ri10hLRvPYPZPhC6\X[^23^15PiP[P\PdPdPLP`F<X33#5X45+113HH10P2PQPTPUP9PWPVE=Pg[^53^S5PQPTPUP7fFS0B#NRgPjE=PQPTPUP8fGRW#NRiPmE=Po[[^J3^L5^I3^K5PpPSPRP9%a|I09=4qtPQPTPUPuPgPVE=R}/2xX53#5[^<C^DpPpPzPrP9&05|I04=4ys12}@X53#5[^HD^Gp3HP0PQPTPUP7PiPjE=PQPTPUP8fHR}PmE8Po[[^J3^L5^I3^K5PpPSPRP9fER~#aI09=4qtPQPTPUPuPiPVE=Ri/2xX53#5[^<C^DpPpPzPrP9&05~I04=4ys12i@X53#5[^HD^Gp'2PhPvPNPvPOPPPhPvPPPMPhPQPTPUP9PgPVE=Rg10wLRvPYPZPwC6\X[^23^15PgP[P\P{P{PLP`F<X33#5X45E;G>P2PQPTPUP7fIRgPjE8PQPTPUP8fJRj#NRiPmE=Po[[^J3^L5^I3^K5PpPSPRP9%a}I09=4qtPQPTPUPuPiPVE=Ru/2xX53#5[^<C^DpPpPzPrP9&05}I04=4ys12u@X53#5[^HD^Gp'2P1PEPqPSPRP8PjH03&0=9Rpg038VRD,C2,J2Ru%w2#vR@,_8Rs7h}C\XM?,[?X<C,[CXDEPwPvPNPvPOPPPwPvPPPMPwPQPTPUP9PiPVE=Ri10WLRvPYPZPWC6\X[^23^15PiP[P\P~P~PLP`F<X33#5X45E;G>PwPqPSPRP8fLRiH03PpAhujsC\XM?,[?X<C,[CP1PCPqPSPRP7fMRsH03PpfKRy1_7@5huC\XM?,[?X<CPWPvPNPvPOPPPWPvPPPMPWPQPTPUP9fNRvPVE8Rr10yLRzPYPZPyC6\X[^23^15PrP[P\PgPgPLP`F<X33#5X45E;G>P2PqPSPRP4fORrH03Pp1_4@9husC\XM?,[?P1P?PqPSPRP>fPRpH03&0=81_>@9huvC\XM?PyPzPNPzPOPPPyPzPPPMPyPQPTPUP9fRRzPVE8Rx10rLRtPYPZPrC6\X[^23^15PxP[P\PsPsPLP`F<X33#5X45E;G>P2PqPSPRPaPzH03&0=61_a@9hupC\P0PqPSPRP]fSRu#a&0=4J0`1C9D,J9fQR@%w9#v,_]3hPrPtPNPtPOPPPrPtPPPMPrPQPTPUP9fVS0CPVE8Rt10uLRxPYPZPuC6\X[^23^15PtP[P\P@P@PLP`F<X33#5X45E;G>P2PqPSPRPcfURR#a&0==J0`%?6S0D@026DfTS0Ef<RS%w6#v'_3hP0%?4S0F@024D%w4#v:0_RdPuPxPNPxPOPPPuPxPPPMPuPQPTPUP9fZS0GPVE8RxfWRqPLPYPZPqDd\X[^23^15PxP[P\PRPRPLP`F<X33#5X45E;G>P2%?=S0H@02=DfXRD%wa#v80_kPKf[S0IP{PdPzP4J0|PQPTPUPlf\Rx#NH01PVPxPlP^%7lRtCb%?t10tIP_%O^13`N9F^I5H[Ro9FtIDoC\X53#5P1P3PQPTPUPwf]R1#NH01PVP1PwP^%7wRtCb%?t10tIP_AFtIoDoC\X53PD10DLRtPNPtPOPPPDPtPPPMPDPQPTPUP9f_S0J#NS0KPVE=S0L10xLRtPYPZPxC6\X[^23^15Q0LP[P\Q0GQ0GPLP`F<X33#5X45E;G>P2PQPTPUP~Q0KH01PVQ0JP~P^%7~R^Cb%?^10^IP_AF^IoDoC\P0PQPTPUQ0B#ef`R^PmE8P^Q0BQ09Q0B#7RmCb%?m10mIPeQ0:Q0;;Hf-0{X9FmIDoPxPtPNPtPOPPPxPtPPPMPxPQPTPUP9fcRxPVE8Rt10^LRmPYPZP^C6\X[^23^15PtP[P\f^S0;Q0;PLP`F<X33#5X45E;G>P2PQPTPU%e}fbRt%A7E8PxPg%16Rf%7gReCb%?e10eI%E6Ro%OfS0:1WfI10foS0K/3N3H,c69FeIDoP0fdRePjPn%7jRoCbPoPIQ0<1WnIS0<Q0=<0DN-0^n,c49FoICX,JoP^PmPNPmPOPPP^PmPPPMP^PQPTPUP9fgS0LPVE8R^10eLRmPYPZPeC6\X[^23^15P^P[P\PtPtPLP`F<X33#5X45E;G>P2ffR^Pi%1=S0M%7iCb%7sRoPoPI%EaS0N%1aS0OQ0OPIQ0OQ0N;DNC`,ca9FoICX'JP0%7vRo#?PoPI%E]S0P%1]S0QQ0QPIQ0QQ0P'0S0R/3NC`,c]9FoICXPePmPNPmPOPPPePmPPPMPePQPTPUP9fkS0SPVE8RmfhRo/0LRnPYPZPoC6\X[^23^15PmP[P\P^P^PLP`F<X33#5X45E;G>P2%7p#?%7@RmPI%ESRf%1SS0TQ0TPIQ0T?DfNC`,cS9FmICXP0%7zRm%EdS0U7DI%1dRfPfPIQ0U=DfNC`,cd9FmIPoPnPNPnPOPPPoPnPPPMPoPQPTPUP9foRnPVE8RmflRf/0LR_PYPZPfC6\X[^23^15PmP[P\fjRmPmPLP`F<X33#5X45E;G>P2Q0E#7%Eh7DI%7R%1kRm1WmIS0V1jmk<0DN+0^,ck7FIP0Q0C#7/WI%1{RkPkPIAUk{NS0WC`,c{PfP_PNP_POPPPfP_PPPMPfPQPTPUP9fsS0XPVE8R_fpR{/0LRkPYPZP{C6\X[^23^15P_P[P\fnS0YQ0YPLP`F<X33#5X45E;G>P2%7D/WI%1|S0ZQ0ZPIQ0Z/j|S0[/3NC`,c|P0&00~$0F%1~S0\Q0\PIQ0\/j~S0]/3NC`P{PkPNPkPOPPP{PkPPPMP{PQPTPUP9fwRkPVE8RDftR_/0LRmPYPZP_C6\X[^23^15PDP[P\frS0^Q0^PLP`F<X33#5X45E;G>P2&0OWS0_#m%1}RDPDPIAUD}NC`P0%1gRD#OAUDgN9FDIP_PmPNPmPOPPP_PmPPPMP_PQPTPUP9f{S0`PVE8RmfxRD/0LR}PYPZPDC6\X[^23^15PmP[P\fvS0aQ0aPLP`F<X33#5X45E;G>P2%1y#O%1iRyAUyiN7FIP0%1sRy/WIAUysNPDP}PNP}POPPPDP}PPPMPDPQPTPUP9p+01@S0bPVE8R}f|S0cPLPYPZQ0cDd\X[^23^15P}P[P\fzR}P}PLP`F<X33#5X45E;G>P2%1r/WI%1p?UpNPKp+01AS0dP^PtP@PkQ0GPsL0y%G@%1@%7^'0'3PnQ0L#ePzPvO3%1zRvPvPI%RzRsPv%VsRsPN1SvsCX'JC`P0%1uRs#O%RuRuPs%VuRuPN1SsuCX'J9FsIf~Rs10sLRuPNPuPOPPPsPuPPPMPsPQPTPUP9p+01FS0ePVE8Rup+01CRv/0LRkPYPZPvC6\X[^23^15PuP[P\Q0dQ0dPLP`F<X33#5X45E;G>P2%1R#OQ0C#1RuQ0C#RRpPu%VpRpPN1SupCX'J7FIP0%1qRp/WI%RqRuPp%VuRuPN1SpuCX'JPvPkPNPkPOPPPvPkPPPMPvPQPTPUP9p+01JS0fPVE8Rvp+01GRk/0LRuPYPZPkC6\X[^23^15PvP[P\p+01ES0gQ0gPLP`F<X33#5X45E;G>P2fY#1/WIQ0G#RRvQ0G#1Rp%VvRvPN1SpvCX'JP0Q0I#RRv#?Q0I#1Rp%VvRvPN1SpvCXPkPuPNPuPOPPPkPuPPPMPkPQPTPUP9p+01NS0hPVE8Rkp+01KS0i/0LRuPYPZQ0iC6\X[^23^15PkP[P\p+01IS0jQ0jPLP`F<X33#5X45E;G>P2%R1#?Q0;#1R1Q0;#ERkPN1S1kCXP0Q0J#1RkQ0J#ER1;DN1Sk1Q0iPuPNPuPOPPQ0iPuPPPMQ0iPQPTPUP9p+01RS0kPVE8Rup+01OS0lPLPYPZQ0lDd\X[^23^15PuP[P\p+01MS0mQ0mPLP`F<X33#5X45E;G>P2faRu#1?UuN%1t%Et'S%1xRt%RxRx#VRuP2&0xx13xu&0vKS0n%@HRK#@S0o#t#t#tRx#9#t#t#9$0E$0;#|#|#Q%@x#t#t#9$0E$0;#|#|#Q,3N80MNS0pp+01US0qp+01SS0r+06Rx,~?p+01PR1/ZxRxePxg00UQRx#KRk#KS0s#MS0t%MkS0u20[?xRx'^'Y&0u;Rk'L&0t;S0v&0s?R;P8%g8P9P;Dp&0r?S0w&0q?RvPv%9KS0x#]Rp%rIR}':S0y20p?HRy&1\FRiPvPv20o?<RmPpPi20<my,}vS0zEnEn21[vGS0{P2P81~AB21Z28$1YdB1W?<9H1VS0|b?bAbBX6?X7?AD9I2%?8Q08[[^6?^7?P2Q0c#7Q0L#ERBPqQ0IO4b>c07b=b0H1S10tuRuPOPPPtPuPPPMPtC6I0nP0%1eR0/jeRtPOPPP0C6PtPPPMP0C6P1101LR0PNP0POPPP1P0PPPMP1PQPTPUP9p+01WPVE8R1p+01TR0/0LS0cPYPZP0C6\X[^23^15P1P[P\Q0kQ0kPLP`F<X33#5X45E;G>P2%1^R1/j^POPPP1C6Q0L#1R1PBPPPMP1DdPEf}R1fuS0k#w#vRB'_S08p+01YS0}fiRt#1S0~%7s'0Q0a#w#vS10'0Ru81R2XmEP?p+01XRq0061S11/0B1Z2uXo?P?%1o%71'0RAQ10,02/ZuXo?10ABRA,~?Q11PqP1PoPeH1QJ0BQ08-06qPqP1PBPQ%AoRB21P32XRQP3%AtS08=4QVZ0;3Po1~QBH0UPTPUP1%NqH01PeJ0BH1OJ0Bp+01VS11PfJ0BQ0r/ZA%O0Q0c/3NS10Q0cPOPPP0C6S12Q0cPPPMP0C6S13PQPTPUP9p+01[PVE8S14PqPLPYPZPqDd\X[^23^15S15Q14P[P\Q11Q11PLP`F<X33#5X45S16$1NS17'2S18'2S19'2S1:'2Q0nQ0pp-0Rq&1MH-1L?RHQ0s#KRZ#KS0s#MRA+0J%MZS1;Q0t20I?LS1<Q0u'{/^xS1='^S1>'^S1?'Y/LkQ0v%g7P8P;P9%g6S1@?f6;DpQ0wPvQ03#]RZQ05#]R1':Q0x#9S03#9#QRB#rS1A%rLRo%]JRJ+0:':':9svyS1BPiPv20<mZ,}vS1CPiPvABvm1S1DPiPvABvmJS1E20Hv>5zvPiQ0zFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?W@10871qL9,0B5i2%O7Q0FQ0D/2=%O6[[[[^6?^7?^8?^9?^@qP2Q03#@#9#@#QRu,CDQ0d#7S0FQ0S#1S0DPDQ11P8PrQ0JP{O9b>b=Q10Q1:Q0nQ0pQ1?,^AS1?$1H/LkQ0vP;P8%g4S1:P9Q1@%g>S107f7DpQ0wPvPv1:1pQ1A%]KRK-0:o':':-0TyPiPvPvQ0o#]Rr,:1PJPiPvPvQ0yPrPiPv20Hva%ruS0y-0<K,}v5zvPi1:yoS0o=BvJS0zCkEnEnI0SQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?X@q10761qL8,0B5i2AD6>8AD>I=B02]4uQ06/34[[[[^6?^7?^8?^9?^:?^;?^@qP2%?DQ0S#ES06Q0FQ0DPDPNQ11P8PjQ0IP{O;b>b=Q12Q19Q0nQ0pQ0b#7Q0;81FIS19%?IRjQ0F/II#?[S12Q0D01EIS1FQ0D#?fm#1S1G/IIS1H#?\j[S1I%1f00iIS1J&0AIRj#mS1KQ1GQ1G007I,qIQ1H3i[S1HQ1G00hIS1G%OIS1LQ0Y#1S1M/IIS1NQ1N/CI'J[S1NQ1M00bIS1M1CI<S1O%1nS1P/IIS1Q,CIQ1Q<0D<[S1QQ1P00gIS1R%1{S1S007I$0A\jS1TQ1S00fIS1UfqS1V#1S1W/IIQ1W'Z\jS1Xg01^?S1YQ1W00cIS1ZeS1[Q1Zp+01H#700iIS1\Q1KQ0j#7S1]Q1]007I,qIQ1]/II3i[S1KQ1]00hIS1]Q1LQ0f#7S0f/IIS1^Q1^/CI'J[S1^Q0f00bIS1_Q1OQ0i#7S0i/IIS1`,CIQ1`<0D<[S1OQ0i00gIS0ip+01LS1`#7S1a007I$0A\jS1bQ1a00fIS1aQ0m#7S1c/IIQ1c'Z\jS1dQ1YQ1c00cIS1YeS1eQ1YP6g015G21D<I'~Q1LeS1LO1S1fQ0h#7S1g/IIR<1C<I'JS1hPcQ1LO1S1LfyS1i#1/IIR<1C<I'JS1jQ0s#KS0s#KS1k#KS1l#KS1m#KR<#KS1n#MS1o%M<S1pQ0s#MR<;TA'YS0sQ1n#KS1n#KS1q#KS1r#MS1sQ1q#MS1qQ1n#MS1nQ1m#MS1mQ1k#MS1kQ0u'^3T3TQ04#Q-0I?/{xS0uQ1r#KS1r#MS1tQ1s-0JHS1uQ1oQ1pQ1l#MS1lQ1kQ1<Q1;'{'^5yH5yH3T5yH'Y+0GS1vQ1vQ1uQ1q-0JHQ1nQ1mQ1k=yHx5yH5yH3TS1uQ0uQ1tQ1sQ1nQ1pQ1lQ1</{A7T<3T3T'Y+0G/Lk'L'L'LQ0v%g=S0u%g]7f7P8Q1:P9Q1@%ga?f>;7f]DpS1sQ0wPvPvPvP:PFPFPGAsv}mJ1BRGPiQ03#]S03-0:}/:r9sv1CkS1nPiPvPvPGPiQ05#@#]-0:}Q04#]RG':9svZCkS04PiPvQ1BPiPv1:ZpRF%rPR:5Bv%rMS1p=BvZ608vS1lPiPv%rOS1w9BvFABv:Z608vS1xPiPvAsvGmS1yPiPvQ1CPiPvAsvrmS1zPiPv1:1}=BvpS1{PiPvQ1DPiPvQ1EQ0y-0<J,}v5zvS1EPiQ0oQ1w5BvABv:y608vCkFPFPFPFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?XP?XQ?g00lERF\jS1w1qI]Rj=i6>[S1|Q1wAi6ja[S1w10641qL7,0B5i8S1}P4P=PPPMP4DdS1~P>PaPOPPP>DdS20&0AcS21%OaS22&0ASS23ADcISS24%?SS251Ccu,JcS26Q0@[[[[[[[[[[[^6?^7?^8?^9?^:?^;?^C?^P?^Q?P2p+01Q#7S0@007IQ0`#1Rj007I1IjIQ0@/IIQ0`#EQ0@PjQ0jp+01fS0@PaQ0?PlPwP|Q0IQ0JQ0LQ0SPnQ0dODS0db>bEbNp+01cR|/0LRjPOPPP|C6ebabhbgbfbNbebdbcbbbWbEb0bjbkb=Q13Q18Q0nQ0pQ19Q12Q1FQ1IQ1JQ1HQ1GQ1NQ1MQ1QQ1RQ1TQ1UQ1XQ1[Q1ZQ1\Q1KQ1]Q1^Q1_Q1OQ0iQ1bQ1aQ1dQ1eQ1YQ1fQ1hQ1LQ1jQ0sQ1vQ1vQ1uQ05#Q-0I?/{A,^x20I?I/{xQ1r#K#MQ1tQ1qQ1oQ1mQ1k'^3T3T'Y+0G+0G/Lk'L'L'LQ0vQ1sQ0wPvQ1nPiPvQ04PiPvQ1BPiPvQ1lPiPvQ1xPiPvQ1yPiPvQ1CPiPvQ1zPiPvQ1{PiPvQ1DPiPvQ1EPiQ0o=Bv:Q1p=Bvy608vCkFPFPFPFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?XP?XQ?Q1|Q1wQ1}Q1~Q20Q21Q22Q23Q24Q25Q26Q0A[[[[[[[[[[[^6?^7?^8?^9?^:?^;?^C?^P?^Q?Q0db>bEbNPjPPPMP|C6ebabhbgbfbNbebdbcbbbWbEb0bjbkb=Q15Q17Q1421:82%G8/ZYp+01D#e9456S17P5Q0g#eS0gPQPTPUP2p+01`#NRY%A4R|E=PF]FX15PQPTPUQ0gp+01_Rj%A6E8PQPTPUQ0ePYH01%A>RY94Q2XRQP2%A{R:PfJ1=A4Q:|Q01PQQ1V#AR:%AaR|94Q9PF[P2A4Q:YQ0^#A%A=R:54QPQP3Q00P3P3P2P2P_n10110100021010000XlQQ0X#AP|P2J1>Q0X=43aA43_]P2Q0k=43bP3PcPFX53P3PcPQPTPUQ0m#ep+01gR|PVE8p+01hQ0hQ09Q1gCbQ0l#7Q077DI&007$0FQ0:Q0<%1>S07/j>Rf/3N%G=Q0M%70'0'3Q0OQ0N'SQ0RPOPPQ0QC6%1bRN/jbPPPMPNC6%AcRN%AW54QPF]F]V]U][]Y]^]\]]]Z]_]T]XXn3PQPTPUQ1`#eQ0@PNE8P|Q0mQ0TQ1cCbQ1gQ0U7DIQ0?$00$0F%1h#OQ0VQ0W%Gl%1lQ0r#7'0'3%1w%Ew'SQ0[POPPQ0ZC6Q0]PPPMQ0\C6Q0B#ARM=4QMP~Q0_P]P2O1-1?FbuWFWVWUW[WYW^W\W]WZW_WTWXQ0aP9Q0^Q0YP^Q0;Q0GQ0CPRQ0EPwPhQ0?P4NB1@Q0aP2J0BbWWEP2O1bEW0P2O1W0n2002101000000101A4Q2:PF[XRQPYO1P21~Q:O1b0bFWFP4P2P7K1AW0Q17#mR:eP:Q0jP4P6Q0gPnP7Q0SP2O7Q0K%GnQ1P%G67Un40PQ02Q0=%G{'3Q1SQ0>7U{p+01\RnPLQ07PfPnDdP2Q1V#G,3fQ0nQ0pQ1;Q1>5yH,YA/LkQ0vQ0u9f;6P8Q1:P9Q109f;7DpQ0wPvPv1:JKRfQ03PiPv1:prRnQ1A20:oZ':':9svyR:PiPvQ03=BvnPiPvABvmZ20Hv]Rm5zvPi20HvbRnABvfy608vCkFPEnQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?X@qXOqAD98>104>Rf1qL6,0BRB'0RY,Z910>=RF,3a1J>bB18Sf6[[[[^6?^7?^8?^9?^:?^;?^C?^@q^OqP2Q0Q9DjLp+01BRf/Cu%G_Q0f%1_RSPfQ0PQ0QPjP8PcPzQ1iO=b>b=W0P2O1Q1WQ1V%G>3UQ0nQ0pQ1?,Y</LkQ0vQ10?f7;P8Q1@P9P;P=Q0uP=Q1:DpDpQ0wPvPv1:pGQ0x#@#]RpPiPvPv20TpJPiPvP:PiPv1:r}R}=BvGPiPvQ0y-0<Z,}v9zvmPiQ0z>08vnCkFPI0SEnQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?X@qXOqAD74>1Z=81Z8Y10=IRI/3aB02c>u104LRa@0P>d[[[[[^6?^7?^8?^9?^:?^;?^C?^@q^OqP2Q0R/3j%?f%G]%E_Q0fPSPfQ0QPjP8P>PcPeQ1iO>b>b=W0P2O1n200100000021100011000bRb{bxXvXWFX23X15P5Q16%esRsP3PQPTPUQ0bp+01Z#NH01PVQ0q,3\Q0q?DL`5H[C\X33PtPQPTPUPsQ0}Q08E8&00t$0FRs%GtQ0cQ0~/jt'380M0R0'2fePsP0P@Q0nQ0p20JH<Q1<Q0t'{=TAx'YQ1;Q1='^,Y</Lk'LQ0vQ1@P8P;P9Q1:Q107f7DpQ0wPvPv1:KrRrQ1A20:o1':':-0TJPiPvPvPyPrPiPvPvP}PZPiPvQ1DQ0y-0<1,}v5zvPiABvyJ1:Jo1:KZ5Bv5zvCkEnEnI0SQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?1084=i9B107>,3913I4Q0H@02=u13aF:0M64[[[[^6?^7?^8?^9?^:?^;?P2Q0FPDQ06Q0DQ11Q0S#GP8PgQ0IP{O:b>b=ClClH0UH0UClClClClClbsWVWUP9P2O2n2001000010121000000b0W[Y04P9P2O2n2001000010121000000W0Y03P9P2O2n2001000010121000000W0WiP9P2O2n2001000010121000000W0W`P9P2O2n2001000010121000000c05bYW^W\P9P2O2n2001000010121000000W0W]P9P2O2n2001000010121000000W0WZP9P2O2n2001000010121000000W0W}P9P2O2n2001000010121000000W0W_P9P2O2n2001000010121000000W0W|P9P2O2n2001000010121000000W0WTP9P2O2n2001000010121000000W0WXP9P2O2n2001000010121000000W0Xn3P9P2O2n200100001012110;000blWqWwP9P2O2n2001000010121000000W0WtP9P2O2n2001000010121000000W0Z08?P9P2O2n200100001012110;000W0Z06CP9P2O2n200100001012110;000W0XDEP9P2O2n200100001012110;000WiWpP9P2O2n2011000010121000000W0Y02P9P2O2n2011000010121000000W0W`P9P2O2n2011000010121000000b0W`W~P9P2O2n2001000010121000000b0ClbrWzWyXmEY09Y0:o"). Qed.

(* [comment removed for export] *)
Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x2a000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x2a000 \/ 0x5d000 <= r_base r).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "h01rh11Hh21ah33ridh42H0h52arh61bh72ghh82r1h92r2h:4rid1h;4rid2h<2Hnh=2_Hh>4__x1h?4__x2h@4__x3hA5ATOPRhB2H1hC2H2hD2H3hE2HrhF3RB0hG4RBALhH3RBChI3RFrhJ3RL0hK2WFhL2WRhM3_H0hN7__arithhO4__ffhP8__varmaphQ5__withR1mhS1qhT2r0hU2stp&0p;1p;3p;2p;4p;6p;7p;8g00=Dj12Tg015mj1oTg016Kj1fTg016nj1XTg017Pk30HTg02Tcj2]Tg02Udj3nTg02Vcj2lTg02Wfj3gTg02Xgj2tTg02Yij2eTg007nj4bTg002kj4aTg019Ij1;Tg01?Wj2MTg00=ij1HTg00mdj10Tg00<gj2=Tg02[ik10<Tg00>Gj19Tg00>lR0j21Tg02Zkj2pTg01A0j1>Tg01Afj1?Tg00:ij38Tg00Wcj1dTg02\_j1cTg00WCk20OTg01:Ck40NTg01:ak60MTg02]Zj1WTg0025k30LTg00g6k30KTg01@9k10GTg00KVj26Tg01;Bj1VTg01YAk20ETg013Bj2YTg00n[j2qTg01Ybj2GTg01ZBk20DTg00;Cj2QTg01Zik20ATg01[Pk20@Tg01\6k20>Tg013_k20=Tg00I?j2mTg02^Rk10;Tg01Vnk10:Tg01WLk208Tg00?Gj1STg00?fj2PTg01Wmj3kTg00@Oj3OTg00A8k207Tg01f7j2jTg00Adk106Tg00BDk305Tg00Bdk104Tg00Cbk103Tg00CDk202Tg00D@j4iTg00D^k101Tg00E<k100Tg00Fmj2hTg01J3j6}Tg00GPk109Tg00Egj2ZTg01Bbj3|Tg00FJj3{Tg00H2j4[Tg00H]j2zTg00IYk20?Tg00JEk30BTg00Jdk40CTg032:j4xTg01I4j4UTg01?Cj6sTg00L2j2wTg009mj3uTg02eFk20ITg00LLj7vTg00N8k80JTf0R1#2#2p=Rf2R2f1R3/11'1p=:f5R4g00hGR5g01JWR6f4R7f3R8P2P3Es;81p=4%21#2#2#2p=K%>1#?p=7g00SbR9/Q1p=5%>1#?,=3p=<%21#2#2#2#2#2#2#2p=J16821631'wp=3%91#9p=~1623/11p=Ag00P;R:1G23;89/11p=@1G31=8:9p=L1=78/62g00Q`R;g00R@R<?u31g00SBR=38'1p=B1693/11p=Cf7R>f6R?P4P7P8P2P3Es;81p=E1691p=`1=23/61p=_20I61p=D1=82/63/11p=I%?1,=3p>0FAu<31=8;=p=rA8:19p=\%91#9#9#9p=FP:P3g01]XP1C[p=^P3g00N\R<g00O;R@P@g00O[RAP1g00Q@Fvp=NP8P<P@P@PAP2P3P1L0Jp=TA8;1=p=yg00i^g00T@RB#2RC#RRD#2RE#RRF#o#f%oD#f#X[p,2rcRD@0H82P01]D7AnD781lD8AgD781t781e783:3:%X6RGP5g00jWRHg00k0RIP6CbRJP5PHPIP6CaRKP8%;41M62RLE4%RF#KRF#HRM%08RN%78RO,=NRP&0<DRQ%5ORO%07RR/<7RS%KF#HRF%2B#9#2#9#2#K#J#HRTPRC3[PSPT%2B#9#~#2#9#K#J#HRSPRC3\O'13A9@NM3A[P11]D?AnD>?1lD?AgD>?1t>?1e>?3:3:PGPJPKP?f8R?#;1M64E4P2f9R>,]DP0f:,pDPGPJPKP3f<RN#;1M61ROE4%03RR#51LRM%>3RUPR%?URUPQPRPUDB'C3:RU[^06^35PGPJPKP8f>#;RRPLE4PGPJPKP2f?RV#;RW1M63RXE4A8548#d%04/<4%c8PP%c4C3[RP[[^96^;5^86^:520O5:RYg02jCRZ%XZR[PYPZg000DR\P5PHP:g00kNR]H0NR^P5PHPIP:P]g00kgJ0MR]PZCbRIP\P^P]PZCaRHP3%WN1MZ1R_GEPGPJPKB0L5:8R`PRPOE4RRB0K5:8Ra#`Rb%71Rc9_aMg01MG&0G1g01N?38Rd#d%c1%01/=a'6'19@aM3:Re'1X06#D[]5]2g01KPRf%XfRgPYPfP\P^P]PfCbRhP\P^P]PfCaR]P3%VN1Mf1R^GEPa%HEREPc1LaECI9:dbRd,1RX06#D[]7^6Y'13:%0?RRPR%7?R?PQ%5?R?%0>Rb/<>REPFPTPbC3[PEPTPSPbC3\?'1CI9@RM5AMP11pDNPGPJPKP3PWPOE4PU[^06^35PGPJPKP8fARW#;RRPLE4PGPJPKP2fBR?#;RbPXE4PP[[^96^;5^86^:5P[PYPZPIPHP3%WVP_GEPGPJPKP`PRPOE4RR/1eX06#D[^5Z^2YPgPYPfPhP]P3%VVP^GE11RdX06#D[^7f^6Y'13:P0PGPJPKP3f@RR#;POE4PU[^06^35PGPJPKP8PbPLE4PGPJPKP2fCRE#;PXE4PP[[^96^;5^86^:5P[PYPZPIPHP3%WRP_GEPGPJPKP`PbPOE4Ra/1eX06#D[^5Z^2YPgPYPfPhP]P3%VRP^GE11adX06#D[^7f^6Y3:%0NRaPa%7NRNPQ%5NRNf=Rc#0R\/<cRcPFPTP\C3[PcPTPSP\C3\N'1CI9@aM5AMP1PGPJPKP3PbPOE4PU[^06^35PGPJPKP8fERU#;RbPLE4PGPJPKP2fFRL#;PXE4PP[[^96^;5^86^:5P[PYPZPIPHP3%WEP_GEPGPJPKP`PbPOE4RO/1eX06#D[^5Z^2YPgPYPfPhP]P3%VEP^GE11OdX06#D[^7f^6Y3:P3PRPVP>O3%0VRY#51LYM%>VRVPY%?VRVPQPYPVDB'C3:P0%0RRV#5%>RRRPV%?RRRPQPVPRDB'C9@VM%0WRVPV%7WRWPQ%5WRW%0?RR/<?R?PFPTPRC3[P?PTPSPRC3\W'1CI9@VM5AMP1%5R%0ERR%>ERVPR%?VRVPQPRPVDB'C7@MP0fDRV#0RR/LM%>VRVPR%?VRVPQPRPVDB'C%0URVPV%7URUPQ%5URU%0LRR/<LRLPFPTPRC3[PLPTPSPRC3\U'1CI9@VM5AMP11LRMfGRR#>RV%0RRU%?VRVPQPUPVDB'CP0fHRV#>RU#`%0VRV%?URUPQPVPUDBfIRU#0RVPV%7URUPQ%5URUfJRL#0RW%>LRL+0FR?PFPTPWC3[P?PTPSPWC3\U'1CI9@VM5AMP1%`LfKRL#0RV%7LRLPQPVPLDBP0fLRL#0RV%7LRL;_Q1rVLfMRL#0RVPV%7LRLPQ%5LRLfNRU#0RW/<URUPFPTPWC3[PUPTPSPWC3\L'1CI9@VM5AMP116UQfORU#0%7U'rfPRU#0RV,6M1LVMRL%7URU=_VQRW%5URUfQR?#0RY%7?R?'=RfPFPTPYC3RO[RdPfPTPSPYC3Rf\UR^'1R]'1Rh'120EVM%\MRV#d1YYM,qM1GYM'=98:Y[20DYM%5MRgfRRZ#0Re/GMRb1QbM'C[20AeM1QM9fSRb#0R`/GMRK,QM16K9'1[20@`MfTRK#0RJ/YM#\\V20>JMfURG#0R_/GM=8:_\V1Y_MP:fV#0/GMP:P4g015G20=9M'mPgeO11Q1M,C1&0;D%9BRD#9#F#F#FRg#2#F#F#2#R#K#J#J#H%9g#F#F#2#R#K#J#J#H,6Q7AQg00TeRQ&0:B-08:Rgg00UQR4#SRH#SRI#SR[,P:RP5k:1P:IRI9k:g1P:4R45O:5O:%S[,P:AO:PI5O:1P:H=O:4g00V0+07'j'j&06Q405&04QP:P:&03:RQP2202:8CiP3PQCi&01:&00:RQPQPQP<P@P@PA1h:MR<1h:9R4'^,NQE}&09@R@1Z:BRB%2D,Z:9|:<1Z:CRC5{:'^,NQCTP@PQ1^C4,NQP@PQP:P4g00V\PBC[,NQP@P:P<g00PYPBC[,NQCTCTCT1zQAP1P21m;=20?12#ydB0B:93H0CbObPbQX>:X?:X@:g00lE\V1qM8/=298:3[%\2%5216M8[[[^>:^?:^@:P1P7P8fZ#0P>PEPRO6bNbAb4bTbSbDbCbBb4b1PLPhP>PWP]P3PdP^PYP?P3P1CxR?11OfRfP01<eZRZPFPTPeC3ROPZPTPSPeC3Re1<`bRbPFPTP`C3P11<JKPFPTPJC3RJ1<_GPTPSP_C3R_P3W4W1P3P1O2n2001000000120000000b2X<UP?PfP0POPePbPTPSP`C3P1P1X4_X1JP3P1O2n2001000000120000000b2X<UCUCUCUCUWIWHP3P1O2n2001000000121000000W1WJP3P1O2n2001000000121000000W1WGP3P1O2n2001000000121000000W1WFP3P1O2n2001000000121000000b2WMWLP3P1O2n2011000000121000000W1W=P3P1O2n2011000000121000000b1WEW=WKP3P1O2n2001000010121000000W1X06X35WRWUo"). Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

Lemma rslot_facts :
  exists x3 x2 x1 : byte,
    wr_at usegs m1 (P0 - 4) stride
    /\ bytes_at usegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= ATOP
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x2a000 <= r_base r).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"; "SLOT"] "p'0h04__x1h14__x2h24__x3h34__x4h47__sat18h57__arithh6:heq_strideh77__sat17h87__sat19h94__ffh:8__varmaph;5__with<5heq_Bh=6heq_P0h>4__x5h?1Hh@4__x6hA1ihB2HihC3LbshD3YbshE4__p1hF3Hi0hG4cstrhH2_HhI1zhJ1ehK1rhL1bi001bhM2ghhN2H0hO3_H0hP5__x10hQ4__x7hR4__x8hS4__x9hT1ahU1li011lhV2x1hW3H10hX3H12hY2H5hZ2H6h[3_H1h\3_H2h]7__sat20h^7__sat21h_2x2h`2H1ha3H11hb3H13hc2H2hd2H3he2H4hf2H7hg2H8hh2H9hi2Hahj4SPANhk5__x11hl5__x12hm2bshn3bs1ho3bs2hp1dhq1mhr2r0hs2r1ht4segshu2x3hv3AL'hw5ATOPRhx2CBhy1Dhz1Eh{3H14h|3H15h}3H16h~2HBi023HWri033Hb'i042Hci052Hdi062Hfi072Hqi082NGi092R4i0:3RALi0;2RCi0<3RI1i0=3RI2i0>2SHi0?2SKi0@3WF'i0A2WGi0B3WR3i0C3WRsi0D2Y1i0E2Y2i0F2Y3i0G2Y4i0H2YBi0I3YB0i0J3YB1i0K3YB2i0L3_H3i0M2ari0N2b'i0O2b0i0P2d0i0Q7fv_listi0R8hyp_listi0S3lmpi0T1oi0U1qi0V2q0i0W2q1i0X2q2i0Y2r'i0Z2r2i0[3ridi0\4rid1i0]4rid2i0^6stridei0_1vi0`1wi0a1xi0b1np%0p%1p%2p&0p&1p&2p;6p;1p;2p;4p;3p;9p;7p;5p;=p;8p;:p;<g039Mk628Tg00=Dj1;Tg00=ij1STg00mdk10ITg00KVj23Tg01Ybj2_Tg00<gR0j20Tg02[ik11CTg00>Gj1FTg00>lR1j26Tg015mk10~Tg016Kk10{Tg01<;R2j27Tg03:Pk40dTg01=Gj1kTg02N6j2OTg00Adk10bTg00n[R3j2:Tg01Vnk10XTg02eFS00j2^Tg02^Rk11BTg00lbk427Tg00o8k221Tg00omk11~Tg0351k31}k20[Tg00BdS01k10@Tg00D^k11qTg00E<k11oTg00Egk211Tg00GPk11eTg00Fmk20|Tg00H]k21_Tg00I?k20?Tg00IYk21\Tg00JEk31ZTg00Jdk41YTg014@k41WTg03;Bk31UTg03;kk11STg017Pk31RTg02Tck21PTg02Udk31OTg02Vck21NTg02Wfk31KTg02Xgk21JTg02Yik21ITg00ZEk21GTg02F5k21FTg02Gnk11ETg00:ij3CTg00;CR4j2?Tg00?GR5j1ETg01WLk20YTg00?fk20wTg00Cbk11DTg03<Lm90vTg00BDj35Tg01YAk20VTg00Wcj1eTg013Bk20:Tg01ZBk20UTg01Zik20TTg01[Pk20STg01\6k20RTg01\\k20eTg013_k20cTg03=Ok31ATg022?k21@Tg01f7k20tTg03>0k625Tg02Iok124Tg02<Kj2>Tg00fWk220Tg02D?k30QTg00WCk20]Tg016nk10\Tg01:Ck41|Tg01:ak61zTg007nk40rTg002kk40qTg01;Bk11tTg01?Ck605Tg01?Wk20<Tg02Zkk21sTg019Ik11rTg01A0k117Tg01Afk116Tg009mk31pTg02\_k10nTg02]Zk11nTg01@9k10NTg03?8k31mTg03?\k21lTg03@<k11kTg03@fk210Tg03APk21jTg03B:k30`Tg03Bdk11cTg03CLk41bTg03D2k71aTg001Wk60ZTg011Pk21`Tg02S4R6j2DTg02<kR7j1ATg010hk21^Tg011mk31]Tg01mok31[Tg01Eik402Tg03Dak103Tg01XVk40iTg03EFk30=Tg02E@j4jTg03Eck51VTg01I4k409Tg03F\k10hTg03G^m=0mTg033Xk40pTg0025k31TTg00L2k21fTg00g6k31gTg00gSk41hTg02bQk51iTg00CDk21QTg00H2j4dTg00LLj7zTg00N8k80ATg004Kk612Tg01Wmk313Tg00@Ok30OTg00A8k218Tg00D@k40oTg01Bbk31MTg00FJk30^Tg01CEk31LTg00MTk719Tg03H^k41uTg022hk31vTg01J3k61wTg00M0k71xTg03I?m:1yTg03J0m<1HTg01IOk61{Tg01<Xk11:Tg02dVk30xTg02SLk31=Tg01EDm<1<Tg02?Om<22Tg03J]k723Tg00hGR8g00P;R9f0R:41Tp=G%;:#;p>0W%;:#;#;#;p>0Hg00SbR;9C9:p=]&17:$16p=a1?;:p=I%;:#;#;#;#;#;#;#;p>0>f2R<f1R='301f:p=|%F:#Fp>15%k==5<:p=qg02e`S02f4R>f3R?A5<=:Cjp=QB1g89:p=810=:,0<p>0;P8P9P=P:H1hp>0gg02Abg02FoP<P=P:I1ip>0f10=:9C9<p=L10<=/3:p==AC9<=/6:p=Y16=:,6<p=@%F:#F#F#Fp>0G13=:,6<p>0810<=/0:p>0D20?9:p=XAC9=:p=<13;:p=221Q9:p=Z20|9:p=WP9P=g00PYR@P:Cdp=}P<g00N\RAg00O;RBPBg00O[RCP9P=P@P:Cdg00Q@RDFzp=9P>PAPBPBPCP?PAPBPBPCP<PDFzP=P:L0Ap=Ng00Q`REg00SBRF7C:p>0jP?PAPBPBPCP<P=P:L0Ap>06P9P>P?P<P=P:J12p={1?=:,6<p>0720w9:p=JB139=:p=`B0O9=:p=PB0O9=::0O9<p=Hg00TeRGg00V0RH-18=;5:p=wP9P<P=P:H0op=V2119:p=UB1M9=:p=bB0^9=:p=1P<PAPBPBPCP9P=g01]XRIP:CdPDFzp=[B1L9=:p=Mf6RJPAPBPBPCf5RKP>P?PAPBPBPCP<P=P:L0AL0Ap=4P9P9P>P?P<H0oP=P:H0op=vP<PAPBPBPCP9P=g00V\RLP:CdPDFzp=fP>PAPBPBPCP?PAPBPBPCP9P<P@P=CdPDFzP:K19p=u13;<1?=:'6p=tQ02P<P=P:Cjp=B13<=/6:p=RP9B0^9<=P@P:Cdp>0JP>PAPBPBPCP?P<P=PAPBPBPCP:PDFzL0Ap=sP9P=g00T@R@P:H1up>0uB139<=>0O9:p=TB1v9=:p>0EB0O9=:018Hp>0CA5G=:p>1?A5G=:95G<p>0aP=PAPBPBPCP:J1wp>1>PJPAPBPBPCPKP>P?PAPBPBPCP9P<PIB0^9=:CdPDFzL0Ap=gP9P<PIB0^9=:Cdp>26P<PAPBPBPCP=P:K1xp>0sP9P=PIP:Cdp=rg02ACRI1><=;C:p=hACI=:p>1;PIP?P<g01^?S03P=P:J12p>0_A5<=:,>?p=oAC8=:p=x20<=:9C?<p>0FP8g01JWRHP>P?P<P=J05=CK:p=m1_=:=C9;p>0P10?</3=/6:p>1413;=/6:p>0Bg01MGg01N?7C:p>0M10>?/3<1_=:=C9;'6p=pA5<=:95>?p=KP9P;P=P0P3P2g01lLRMg027HS04g03KbRNP:N:1yp>1dP9P;P<P0P3P2PMQ04PNg03LCS05P=P:N<1Hp>0}P=PAPBPBPCP:J1{p>0l%A:,0=p>0KQ02&1::80x=p>0LA5<=:95>?95JKp=yB1=<=:9C>?p=c17=:,0<p=iP?PAPBPBPCP<P=PAPBPBPCP:PDFzK19p>0zg00UQS06/D:p=\PIP9P6P7P4g02hgRDQ06P;P?P<P=P:N<1<p>04Q0210>?$1:80xKB1=<=:5CJp=l10:;p=~PIPIP9P9P5P7P7P?g03M2P<P=P:N<22p>1XPIP9P6P7P4PDPKP>P?P<P=P:N<1<p>0kP9P=PLP:Cdp>0yPJPKP>P?P<P=P:H09H09p>0110<==C9:p=nQ02PKP>P?P<P=P:K23p>00p,2stRLp,2m1RDp,1bR4#GR7p,1rS07p,2MRS08p,2HrS09J28%;@S0:#;R6#;S0;#;S0<$0WS0=$0WR5$0HRA#SRNQ07$0IRM'3S0>1_MNR2#]S0?Q07#aR3,0MR0p,2rcRO$1CS0@'3S0A%I3S0B&0HA#SRA%;@#F#;#F#;$0H$0>#SRP/3M5|0S0C[S0DQ0B%;@#F$15#;#F$0H$0>#SRQ/3M9|0P[S0E'6S0F'6S0G'6S0H'6P1Q0>Q0HQ0;$0~RR$0{RSQ02PDp,2P0RT%S6RU'7RVp,6strideRWH0dS0IPDPVPS%k;S0J1OR<RX1OR=RY1OR:RZ&0bSR[5qSS0K5qSS0L5qSDQp,1oS0M%84R\Q0<#SR]p,3idxR^,:WS0N40;R_%F@R`$0XS0O'0S0P-0g7S0Q80fLS0RQ0MQ0:$0XS0S,0_S0T-0g7S0U80fLS0VQ0MQ0T%S@R_'0S0W-0g7S0X80fLS0Yp,1BS0Z?LM\S0[Q0>A=TW0S0\Q0AQ0C'6S0]'6S0^'6S0_'6S0`7YZS0a7YYS0b7YX3@XVS,^SX_S,^SXuSS0c'^RXP:Q0>Q0HP1Q0?Q0GPXP:Q0?Q0GP1Q0AQ0FPXP:Q0AQ0FP1Q0DQ0EPXP:Q0DQ0E&1BO%F`S0d#FS0e#F$15$0G$0GRY#;$0G$0G#;$0W$0H$0>$0>#SQ0@'3S0fQ0@%FY$0G$0G#;$0W$0H$0>$0>#SS0g408PLP4Q07Q09H27Q0[PWP^Q0ZQ0N80D]S0h#XQ0h,<TRYeRZPY221L4R4#XQ0Z/<4R4eRaP4p,2mr$1~Rb#X1<WbRbeRcPbp,2B0S0i:1}\]Rd%2]S0j1_\]S0k#2S0l[Re20[MNRf%2M%2N%22Rg[[Rh20[W]Ri%2WQ0j1_W]S0m#2Rj[[Rk&0bGRl&0@GRG%Z=S0n&1q9Rm&1o9RnPn%W]Ro2119@Rp'}&1eBRB20|9;Rq=9npS0oDN21_nCRCP:P<20?EFS0p21\:<$0jdB1Z9;=H1YRFb9b:b;X0913]:%2=RE[^09P:PWp,3S16RrO2b5b7b4b8b6b<b=PZPYPaP4PcPbPdPePfPhPiPkPlPGQ0nPmPnQ0oPBQ0oH06PCPFb9b:b;X09%2:S0qPE[^09P:P^p,3IDXO2b5b7b4b8b6b<b=H1WQ0N#210^_,:W10\]Rs?=:3XI9p,4SPANQ0N1:W_Rt'0RuB1UW^_D{A=su3PtQ0N/0:==s3XI9P:PW&1SWD{Q0N/0W==s3Q08B1ROLDS0rP121POLS0sB1OOLDS0t21NODS0uB1KOLDS0v21JLDS0w21ILDS0x'6S0y'6S0z'6S0{'6S0|PXP:Q0sQ0|P1Q0tQ0{PXP:Q0tQ0{P1Q0uQ0zPXP:Q0uQ0zP1Q0vQ0yPXP:Q0vQ0yP1Q0wQ0xPXP:Q0wQ0xP:P7Q07Q09p,2HkS0}O4Q02PDPMP3H0dS0~B07E=3g02iI21GL701F<&1E=3CPD10M?PS%k<P[DQ%2<%S5S10,?<3@[[`0_9`0T9S11'6P1Q0~Q11PXP:Q0~Q11Q02PDPMP3PVPWP=PZPYPaP4PcPbPdPePfPhPiPkQ06#ES12#ES13#ES14#ER5#ERE#JS15&0X@-0Y9Rt%J5S16'`Q12#JS17Q06-0w9S18'PS193H/wlPG%Z>R5&1D9Ru7V<S1:%ZKS1;?V?uRv7V=S1<PmPn%U`S1=%U6Rw'bS1>99nqS1?PBPnQ0:#URxQ0:#F#URy,1pS1@5[nPBPn%WNRz=9npS1APBPnQ1=99noS1BPBPnPn1}qyPB11xoS1CQ1>'1S1D%WUS1E'MS1F99npDNF4F4PCPFb9b:b;X09X19X29X39X>91:<?S1G#2S1H10=KS1I,<<13N<S1J13]KS1Kf8R{#2S1Lf7R|/:{:0DJ]S1M/7U,3K[[[[[^09^19^29^39^>9P:P\P^PWQ0ZPMfSS1NfTS1OfcS1PPrQ0iO:b5b7b4b8b6b<b=13MVePZPYPaP4PcPbPdPePfPhPiPkQ16Q19'P/wlS1QPGP5P<%ZJS1RP=PvDvS1SPmPn%;`S1T#US1U,1w9[npS1VPBPnA9nzwS1WPBPnA9noxS1XPBPnQ1U/1oQ1=,bxS1Y/1xS1Z'1=9nyS1[PB11poRvQ1Y'1S1\Q1E'MR5/1x11wyS1]59nF4F4PCPFb9b:b;X09X19X29X39X>9X@9AL:?KS1^13N>S1_13]?R}10{]1:>KS1`/0>R~;=|S1a10>]S1b1:KJS1c'0S1d/7US1e10|{S1f7=K[[[[^09^19^29^39^>9^@9P:P\P3PMP^PWQ0ZQ1OQ1PPrfQO:b5b7b4b8b6b<b=A=VW0eN90vQ0IP=Q0N,0sRs/7UR0P;PZPYPaP4PcPbPdPePfPhPiPkQ14#JS1gQ13#JS1hQ18'PS1i'PQ15Q19'P/wl'wS1jPGQ1:Q1;9Vu?7V=S1kPmPnQ1Y99nqS1lPBPnQ0d#US1m99nzS1nPBPnQ1XPBPnQ1Z,1v=9nwS1oPBPnQ0oPBPnPnPqP5Afn5wDuH06F4F4PCPFb9b:b;X09X19X29X39X>91:=<S1p#2S1q13NKS1r10?]S1s?=~JS1t%2>S1u10K]S1v1:J|S1w'0S1x/7UR~?t~{[[\}[[^09^19^29^39^>9P:PMP3P^PWP\Q1OfdPrfRS1yQ0iO:b5b7b4b8b6b<b=p,4HDR0O410M0S1zQ0J=5S[S1{5BDS1|Q10#I9R;;S1}'6P1Q1|Q1}PXP:Q1|Q1}Q02PDPVPW%S`R`,7TR0P`PKPZPYPaP4PcPbPdPePfPhPiPkPlPGQ0nPmQ1E,MpR~%W`R5,MpRv59nPCPFb9b:b;X0917:U17:`'3^09P:PTO1b5b7b4b8b6b<b=PZPYPaP4PcPbPdPePfPhPiPkPlPG%Z<S1~?V=uPmPnQ1XPBPn11~x:0Jv5DsPCPFb9b:b;X09X1913]=17=`17=U/0<7=`[^09^19P:PWPTPrO3b5b7b4b8b6b<b=N90vQ02PDP0P`H0dPDP0P`P:PZPYPaP4PcPbPdPePfPhPiPkPlPGPuPmA9nq5PCPFb9b:b;%2`P:b5b7b4b8b6b<b=PZPYPaP4PcPbPdPePfPhPiPk20VW]S20%]]RT#eS2120:W]S22,:]Q0m5LW[S2320UW]S24%I]S25Q0m>07j]S26[S2720TW]S281?];S29Q0m,?]Q0m<08;[S2:20SW]S2;Q22#]\TS2<20RW]S2=Q0m/<W\TS2>Q0320eW]RjePj20VMN%]NRj#e20:MNS2?,:N=LM2[20UMN%INS2@B07g2NRg[20TMN1?N;1?N2@082;[20SMNQ2?#]\j20RMN1<2M\jQ0320eMNRvePv20V\]S2AQ2120:\]S2B,:]Q0k5L\[S2C20U\]S2DQ25Q0lQ0k<07]Rv[S0l20T\]S2EQ29Q0k,?]Q0k<08;[S2F20S\]S2GQ2B#]\TS2H20R\]S2IQ0k/<\\TS2JQ0320e\]R~eP~P>g015GS2K20c;]+0?Q25eS2LO1Pvf;S2MQ2K20c;N+0?Q2@eO1PgfBS2@Q2LO1Q26%EES26#ES2N#ES2O#ES2P#ES2Q#ERE#ES2R#ERg#ERv#ES2S#JS2T%JvRvQ0:20Y9_20Y9;S2U+0uS2V61A9R~%JgS2W%JES2XQ2O#JS2OQ26#JS26Q15Q17'P5T~3H3T3H21@9]S2YQ18+0ES2ZQ2S#E#JS2SQ2T,`tS2[Q0:Q2U-0ut61A9RE/`vQ2Q#JS2QQ2P#JS2P,`tQ2N#JS2NQ26Q15Q16'P5Tt5TE3H3H5Tt+0C+0tS2\Q2R#JRgQ2QQ16Q1gQ1h3HS2R'P+0CQ2PQ2R'PS2R-0CgS2]Q2\Q2[1`tvQ2WQ2XQ2OQ26Q15,`tS2^Q18'P5TE5Tt5Tt5TE3HQ2ZQ2SQ2TQ2WQ2XQ2PQ2N,`~Q26Q1g'P3H3H9T~v3H+0C+0tR~Q2]Q2QQ2R'P-0CgQ2\01?l40a80a~40a40aPGf<R~#ZP{PuP>PuDvP<f:Rg#ZS2\9VuJP=f9Rv#ZS2]PKPuP?Q2M#Z9Vu|DvDvPmPnPnA[noq-1>nS2RPBPnPwQ0<#U,boQ1UFgPBPnPnA[nzq-1>nPBPnQ0;#US0;Q0e#U,bz%F6#US0eFgPBPnPnQ2RPBPnPxQ0d#;#US0d,boQ1mFgPBPnQ1lPBPnPnQ0;>26pwPBPnPnAfnqyS2QPBQ0;/1yR6%WPRE59n%WQS2ZQ0;59n60snH06PBPnPnQ2QPB%WAS2Q99n6Q0;99nE60snH06PBPnPnQ0e/rqPBPnPnQ0;,}zPBPnPnQ1m/rqPBPnPnQ1U/rqPBPnQ1XPBPn11woQ1Z'1=9nyPBPnPn1}qwPBQ1\/M5S1Z/15Q2Q59nQ2ZQ1Z59n60snDNF4DNDNDNDNF4DNF4F4PCPFb9b:b;X09X19X29X39X>9X@9XQ9XR9XS9XP9Xk9Xl9g00lERz\TS2Z1:]~RE=L>J[Pz\j1:N~=Lvg[Q2ZAL>Ev[Q1`#2Q2M=L>|%Ivf=RE/0g13QE7|P[%Igf>S2QQ2M'0Q2Q,3P7|A[f?S2S#]RPQ2S,3N13]~Q2S/0]Q2Q,:E/0Ef@Rj3=%2jS2TQ2QQ2S/:j80D]/7`R6/0`13Q67|A[[[\P\P[[[[[[[[[^09^19^29^39^>9^@9^Q9^R9^S9^P9^k9^l9P:Q2BQ2?Q22P2PMQ0mQ0kP3P\P^PWQ0ZPvQ2SfES2?fofpfrfsf{S2Xp+01@S2Wp,4SMODS2[p,3B16S2_PrfmQ0iOJb5bNbZbXQ0h/7`R2/0`13Q27|Aeb}b|b{bbbXbabWbhbgbfbZbYbebdbcb`bNb?b7b4b8b6b<b=100`13Q07|AeJ25&0@SRA&24`RQ9hS:R2ABD0:'6S0hXmARP'^Q00PAPPPXP:Q0hP11>S=S2`01;QABD0=RPPXP:AhS?QABD0>Q01PSPX^DP^C2PK1>S[R201;QABD0[P2PIp-0R2P:g014kS2aPzn0110b00020010000S2bXJIPQP=H0_Pz220X:S2cb?WDWCQ01PSA5S<:RP=hSQA5S?=S2d9BD0PX]D]CP:A5S=[R6=hSQA5S<[S2e9BD0A5S?[S2f,>SPIP2P:PzQ2bn0110b0002001010bS2bXJIPQP=H0_PzQ2cb?WDWCQ01PSA5SJPRP=hSQQ2d95S|S2d9BD0PX]D]CP:A5SK6R6=hSQQ2e95SJS2e9BD0PSPSP|Q2fCoPIP2P:PzQ2bn0110b0002001010bXJIPQP=H0_PzQ2cb?WDWCQ01PSA5SgP=hSQPDP0PSQ2MQ2dDQPX]D]CP:A5Sv6=hSQPDP0PSPgQ2eDQPSQ0cQ2MPSQ0IPDPVPSQ0J1ORER6Q0L5qSDQQ0RQ0b7Y63@XVS,^SX_SP|PSQ0IPDPVPSQ0J1OR~R61OR{RXQ0K5qS5qSDQQ0RQ0VQ0a7YX7Y63@XVSP?13:`9R_:S0a17s=:0QL7S0KQ0020]89R6g01KPRX&0\XS0bP6PXg000DS0LP8g00jWS0cP9g00kNRPH1|S2eP8Q0cg00k0S2dP9PPg00kgJ1zS01PXH0rS2bQ0LQ2eQ01PXH0qS2fP=&1tLS2gJ0520<X:S2h3CS2i%G=/x7S2j%8=S2k17s>S2lQ2lQ2kQ1T#;S2m#SRP'0S2n'?3R3@XMX'^XL6PzP:Q2iQ2jQ2k17sJS2lQ2lQ2n'?3R3@XMX,^XQ00PXQ0bP6PXQ2bQ2fP<Q2gJ05Q2h3C%G</x7%8<S2j17s|S2kQ2kQ2j/0P'?3R3@XMXPzP:Q0bP6PXQ2bQ2fP>Q2gJ05Q2h3C%G>/x7%8>S2h17svS2kQ2kQ2h/0P'?3R3@P1Q0bP6PXQ2bQ2fPKQ2gJ05PXP=H0F%GK/x7%8KS2k17sgS2h'3Q2hQ2k/0P'?3@PzP:Q0bP6PXQ2bQ2fP|Q2gJ05PXP?H0F%G{/x7%8{S2g17sES2f'3Q2fQ2g/0P'?3@P1%Gv/x7%8vS2fQ2Q,7sS2gQ2gQ2f/0P'?3RPzP:Q2M#G/x7%8~S2gfAS2f,7sS2bQ2bQ2g/0P'?3RQ08Q0rP1Q0sQ0|PzP:Q0sQ0|P121sOLS0r&0\HS2bP8Q0cQ2dPHH0rS2gP8Q0cQ2dPHH0qS2dP=&1rLS0c20<H:S0bEm&0I=RO#I20PON&17=S2hPOQ2h$16S2hQ0@g00R@Q2h81pO$0jH14+0B3@[^KH`0[8S2kQ2bQ2gQ2dP?Q0c20<H<EmQ2bQ2gQ2dP<Q0c20<H=S2jEm1xK?#e&0IK%aKS2l'0&0n?&0I?%a?&0nK3=3|[[[`0ZH`0]8^sH`0\8S2ng02jCR8&0\8P6P8Q0LQ2eQ01P8H0rQ0LQ2eQ01P8H0qP=&1nLJ05P8P:H0FQ2bQ2gQ2d%G?Q0cQ0bEmS01%8?R8#2S2eP8PN%a:S0L20P8N&0N:$0MRO#e&0n:&0I:/08'33@H143@XKH,^H[_0M^T6S2oQ2iQ01Q2eQ0L9=8]20P8]3@7@OXKH,^H[^MX^L6S2i'6S01'6S2e'6S2pPzP=Q0rQ2pP1Q2kQ2ePzP:Q2kQ2eP1Q2nQ01PzP:Q2nQ01P1Q2oQ2iPzP:Q2oQ2iP:Q1yfNfJS1yO3Q2bQ2gQ2dQ1N#GQ0cQ0bEmQ1N#8R8P8P]Q0LP8P]Dp+0B7@OXKH,^HQ00PHQ2bQ2gQ2dQ1O#GQ0cQ0bEmQ1O#8R8P8P]Q0LP8P]Dp+0B7@OXKHPzP:Q2bQ2gQ2dfVS1O#GQ0cQ0bEmQ1O#8R8P8P]Q0LP8P]Dp+0B7@OP1Q2bQ2gQ2dfWS0L#GQ0cQ2jEm&0N=$0MQ0L#8RO#2POP]Q2hPOP]Dp3@PzP:Q2bQ2gQ2dfY#GQ0c20<H?Em&0N>$0MfZS0c#8RO#2POP]%a>POP]Dp3@P1&0NK$0Mf[#8ROPOP]Q2lPOP]Dp+0BPzP:&0N|$0Mf^#8ROPOP]%a{POP]Dp+0BP1f_#8RO#2POP]%avPOP]DpPzP:fa#8#2fb#8ROP]%a~POP]DpP1Q1P#8RO%aE7=]20PO]PzP:fe#8Q2S#a7=]ff#800P]PcPb20[\]%2\Pe[fi#8RO00[]%2OQ0jfk#8/_]#2[[PiPkPlPGPuPmQ2RPCPFb9b:b;Q2ZP:b5b7b4b8b6:1mW]Q0m#]S0j21l]WRO[R8Q0j\ORO'6P1P8POPzP:P=Q2[O11::],<WS2[XI9S0j,^9Q00P9Q0jPzP:Q2[P91:=]S0j1::^1:<^S00,:]'<Z0^9&1k9S1PQ1P+0]S1P$0bQ1P$0@P9P<P9P^&0b9DK&0@9Q05P:P=2109@S0521j9]S1P60`9Q0:-109R@60`9S2lQ1PQ05>0`9@60`9R@Q03Q0p21d_=g03MV-0]9&1c9+0]$0@P9Q04Q2l:0}_:B0}_:@H1bc0S$0jdK1ac0Qc0RQ0j/:^1:=^,:]R@'<ePWP:J0ZQ0N/<@Q00P9Q20Q23Q24Q27Q28Q2:Q2;Q2<Q2=Q2>Q22P9Q0mP9fz#800V]Q21Q2X#8R@20:@],:]1_@]3L[20U@]Q25f|S21#8S0m/_]R@?t@][Q0m00T]Q29f}S0m#8S25/_]R@,?]@08@;[Q2500S]f~S25#8R@00:]#]\T20R@]Q2W#8R@/_]/<@\T20:@]P9p+01AS29#8/_]P9Q2AQ2CQ2DQ0lQ2EQ2FQ2GQ2HQ2IQ2JQ2BP9Q0kP9PKQ2LO1Q0q@07:]PEQ2LO1Q1L@07{]Q2?Q2LO1Q2T@07j]PcPbQ2OQ2N,`tQ2VQ26Q2^Q16Q1i3H3T3HQ10-1@9Q18+0EQ0<$0X-0Y9R@Q2PQ2YQ2O+0EQ2U-0u@Q2N'`Q2YQ26+0EQ2YQ16+0EQ2YQ1h+0EQ17,`@'P3H3H3T+0C+0t01?lPG%Z|Q2]7VgP<Q1;P=%Z{P>Q2\P?Q1RDvDvPmPnPnQ2RPBPnQ1mQ1T#F#U,boQ1=FgPBPnPnQ2RPBPnQ1UQ2m#U,boQ0;FgPBPnPnQ0e/bo,rxPBPnPnQ0;/rqPBPnPnPnQ1UQ1m/1o1bxp'1/MyR@Q1U%WP'19fn@DuPBPnPnPn%W_R@PyA9ny5DuPBPnPnQ1=/rqPB20ln~DNF4DNDNF4PCPFb9b:b;X09X19X29X39X>9X@9XQ9XR9XS9XP9XE2Q2Z1:]gRT=LJ?[Q2ZALJT{[1:v],<?%]v1:K>:0Dv]/7|RT10{P,?T5R{13{`9R_{%]{Q2f[[[[[[[^09^19^29^39^>9^@9^Q9^R9^S9^P9^E2P:PzPJPEfMS2ZP~P\p+01NS1U#8p+01SS1mPKPWP^Q2MQ2@fLS0;Q1OQ29p+01RS1OQ2_OBb5b6bNbYbWbsc0XbbbXbabWbhbrc0WbgbfbZbYbebKc0Vbdbcb`bNb?c0`bzY07Z0U9P=P:O2n200100000012110a000c0PXHOXy8P=P:O2n2001000000121000000bAWvW\P=P:O2n2001000000121000000W?W[P=P:O2n2001000000121000000W?WOP=P:O2n2001000000121000000W?WHP=P:O2n2001000000121000000W?Z0YHP=P:O2n200100000012110a000bJY0AW\P=P:O2n2001000000121000000W?W[P=P:O2n2011000000121000000W?WOP=P:O2n2011000000121000000W?WHP=P:O2n2011000000121000000WHY0@P=P:O2n2001000000121000000b?Y04Y06P=P:O2n2001000000121000000W?Y03P=P:O2n2001000000121000000W?XMXP=P:O2n200100000012110a000W?Z0N6P=P:O2n200100000012110a000W?Q0K#eR6eY05Xp9Q0aP6[^p9P=PDP0PSP~PSP{PSP>P[DKDQP1%20S0aPSPSPEPSPvPSPKP[DKCo-0K0Q0:#SR6Q0=#SRX+1`RHPSPSQ2QPSPgPSPJP[DKCo,D:&0\SR8%A=S0:,00-0LDROPSPSQ2SPSQ2MPSP|P[FyP=Dc[^AI3RQ0IPDPVPSQ0JPSQ2Q,ORRT#kS0KPS1ORgRP#kS0r1ORJS2p=qS[DKDQQ0RQ0VQ0YQ2pQ0`3Y7YP7YT3@P:Q0aPSPSPjPSP~PSP{P[DKCo-0K0PSPSQ2fPSPEPSPvP[DKCoS2p,D:P8POPSPSQ2@PSQ2QPSPgP[FyR~P=Dc[^AI7RHP1Q2p#A==0H1>S~,D:P8POPSPSfCS2pPSQ2SPSQ2MP[FyS2kP=Dc[^AIQ0IPDPVPSQ0JQ2@,ORR~PSQ0KPSQ0rP[DK5qSDQQ0RQ0VQ0YQ0`7YP7YT7Y~3@P:Q2k,>S#A==0HPSPSQ2?PSQ2fPSPEP[DKCo,D:P8POPSPSfFS2kPSQ2@PSQ2QP[FyP=Dc[^AI17s`S0r,0MRO#2Q2?=5S[S0K,>SS2e#AS2n==OHS01Q2k=5S[S2o,>SR~,D:S2iP8Q0:,0O-0LDS2[PSfG=5S[S2_P=Dc[^AIRT'6PZPYPaP4PcPbPdPePfPhPiPkQ16Q1gQ193H/wlS2mPGQ1:%Z?S2R7V=S1TPmPnQ1?PBPnQ1APBPnQ1BPBPnA9nqxS2\PBQ1D/M5,1pS1;99nqF4F4PCPFb9b:b;X09X19X29X39Q1H13N=RN13]>RPQ1uQ1x=i>`#2[[[[^09^19^29^39P:P^PWP\PMQ2Xp+01LPrQ0iO8b5b7b4b8b6b<b=Q01PTPZPYPaP4PcPbPdPePfPhPiPk21^6XS01%I6S2]%2X%IH[S2P[S17%26RTQ2aB1]6X=UWiS2YQ2a%2H[^iTS26P=Q2K20c;6+0?Q2]eO1S2]Q2PQ15Q16Q1hQ19'PS1h3H/wlS16PGQ1:Q1RPKPuP?PuDv7V=S1:PmPnPn20ln{PnQ0eQ0g#W'}H0zS1RPBPnQ1@Q0e59nS0ePBPnQ1APBPnQ1BPBPnQ1CQ1>Q1='1'1=9nyS1@PBPnQ1;%W6RTQ0=$0~S0=61[9S1980J@DsF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0g:08JKS0gQ1I/3JS1IQ1JQ1KQ1vQ1w/0J;={S1vQ1M=iK`?=_H[[[[[^09^19^29^39^>9^@9^E2P:Q0fQ0@P3P^PWP\PMQ29p+01Gp+01OS2KPrQ21O<b5b4b7b4b8b]b^b6b<b=Q2iPIfHRX=5S[S2N,>SS2U,D:P8Q2[PSfIS2[=5S[S2OP=Dc]BP=Q2_,>SS0<#\P?Q06PZPYPaP4PcPbQ14#\%I`S1020?9;S2VQ14P`%X`S2^H04PSPSfKS1iP[CoS2T#\Q2T#AR;#IS2LQ2VQ2TP;%X;H04P?H02Q2LPSPSQ0;P[CoS0;$03Q0;#AS2L#2PdPePfPhPiPkPlPGPuPmAfnq5PCPFb9b:b;Q10P:b5b7b4b8bGbFH0ib6b<b=PSPXPSfDR;A5Sj[S10DKS2T,>S#\eO2P8PDP0Q06#AS1LPSQ2TQ06FlPZPYPaP4PcPbQ0;#\Q2L#IS2TQ2VQ0;Q2LQ2L#XH04P>H02Q2TQ2Z=5S[S2Z,>SS2T$03Q2T#A#2PdPePfPhPiPkQ1gQ185Tt/wlS18PGQ1<PmPnQ1]9[npS2TPBPnQ1WPBPnQ1XPBPnQ1Z/1q11yoS2LQ1Y'1S0;/M5,1wPqFgF4PCPFb9b:b;X09X19X29X39X>9AL:?>S0kQ1_Q1sQ1`'0/7`S1s#~10|]S2BQ1`'0S1`=iJ`#~'<\}[[^09^19^29^39^>9P:P\PMP^PWQ0Zp+01CS2JQ1OPrO8b5b7b4b8bGbFb6b<b=%~0S2I%~OS2H'<RtePtQ2IP820LD:S2IPSQ1iH0FXI9P=Q2HP:D{b?P8PDPOQ1LPSQ2OQ06Flec0IWB%E:S2HQ2O,>SS1i'DPZPYPaP4PcPb%E>S2GQ12'D%A>Rt/0_/?_S2FQ2G10:_Z0a9S2GPtO1Q2GP>Pt%XtH1XQ12P_%X_S2GJ0kP?H02S2EQ2F&03KS0l%AK#2S2DPdPePfPhPiPkPlPGPuP=Q0n9Vu=P=PuDvPmPnPnQ0d,}qPBPnPnQ0d/1@00y@PB20ln?DNDNPCPFb9b:b;X09XE2S0dQ0q10=_/?_P?[[^09^E2S0qP:P8PDPO%EgS0n#AS2CPSQ1N=5S[Q0nFl%AgS1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q0K9BDO17s6S2i,0MRt#2Q2@=5S[S2@,>SS2A#A==tHS22Q2p=5S[S2p,>SS2>,D:S2=P8Q0:,0t-0LDS2<PSA5S;[S2;P=Dc[^AIS2:'6PZPYPaP4PcPbPdPePfPhPiPkQ2mPGQ1TPmPnQ1?PBPnQ1APBPnQ1BPBPnQ2\PBQ1D/MT,1pS2899nqF4F4PCPFb9b:b;X09X19X29X39Q1HQ1uQ1x=i>6#2[\P\N[^09^19^29^39P:P^PWP\PMQ21p+01MPrQ0iO8b5b7b4b8b6b<b=Q22Q2:PZPYPaP4PcPbPdPePfPhPiPkQ01Q17Q2YQ26Q2]Q2PQ16PGQ1:PmPnQ1RPBPnQ0ePBPnQ1APBPnQ1BPBPnQ1@PBPnQ28Q1980J@DsF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0gQ1IQ1JQ1KQ1vQ1M=iK6?=_H[[[[[^09^19^29^39^>9^@9^E2P:Q0fQ0@P3P^PWP\PMp+01BS2:p+01HS22p+01PS27PrQ0mO<b5b4b7b4b8b]b^b6b<b=Q2=PIQ2e,D:P8Q2<PSQ2oP=Dc]BP=Q2;,>S#\P>Q12PZPYPaP4PcPbQ12Q14'D1?_`S2<Q12P_Q2GQ14P`Q2^J0kQ2U#\Q2U#AS2G#IS24Q2VQ2UQ2GQ2G#XH04P?H02Q24Q1i$03Q1i#AS24#2PdPePfPhPiPkPlPGPuPmAfn@5PCPFb9b:b;Q2<P:b5b7b4b8bGbFH0ib6b<b=Q12PSQ2[PSQ2?Q2f=5S[S2<DKS2G,>S'DeO2P8PDP0Q12#AS2UPSQ2GQ12FlPZPYPaP4PcPbQ1i#\Q24#IS12Q2VQ1iQ24Q24#XH04P>H02Q12Q1y=5S[S12,>SS24$03Q24#AS24#2PdPePfPhPiPkQ18PGQ1<PmPnQ2TPBPnQ1WPBPnQ1XPBPnQ1Z/1@Q0;/MT,1wPqFgF4PCPFb9b:b;X09X19X29X39X>9Q0kQ1_Q1sQ1`=iJ6#~7n_\}[[^09^19^29^39^>9P:P\PMP^PWQ0Zp+01DQ1mPrO8b5b7b4b8bGbFb6b<b=100_S1m%~tS1i'<S2GeQ2GQ1mP8Q2IPSPXH0FXI9P=Q1iP:D{b?P8PDPtQ1LPSQ2oQ06Flec0JWBQ2H/D~PZPYPaP4PcPbQ2EQ2FQ0lQ2DPdPePfPhPiPkQ0dQ0qP:P8PDPtQ2CPSfP=5S[Q0nFlQ1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q2@9BDt17s_S2=,0MRs#2Q2S=5S[S1i,>S#A==sHS1mQ10,>S,D:S2GP8Q0:,0s-0LDS0:PSQ2<P=Dc[^AIS23'6PZPYPaP4PcPbPdPePfPhPiPkQ2mPGQ1TPmPnQ1?PBPnQ1APBPnQ1BPBPnQ2\PBQ1D/M@,1pS1D99nqF4F4PCPFb9b:b;X09X19X29X39Q1HQ1uQ1x=i>_#2[\P\N[^09^19^29^39P:P^PWP\PMQ0mQ1UPrQ0iO8b5b7b4b8b6b<b=Q1mQ23PZPYPaP4PcPbPdPePfPhPiPkQ01Q17Q2YQ26Q2]Q2PQ16PGQ1:PmPnQ1RPBPnQ0ePBPnQ1APBPnQ1BPBPnQ1@PBPnQ1DQ1980J@DsF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0gQ1IQ1JQ1KQ1vQ1M=iK_?=_H[[[[[^09^19^29^39^>9^@9^E2P:Q0fQ0@P3P^PWP\PMQ2Jp+01Ip+01QS0@PrQ25O<b5b4b7b4b8b]b^b6b<b=Q2GPIQ2A,D:P8Q0:PSQ2pP=Dc]BP=Q2<,>S#\PKQ13PZPYPaP4PcPbQ13Q14'D1?6`S0:Q13P6%X6Q14P`Q2^J0kQ2e#\Q2n#IRHQ2VQ2eQ2nQ2n#XH04P?H02PH&03~%A~RH#2PdPePfPhPiPkPlPGPuPmAfnT5PCPFb9b:b;Q0:P:b5b7b4b8bGbFH0ib6b<b=Q13PSQ1yPSQ2kQ2@DKS2k,>S'DeO2P8PDP0Q13#APSQ2kQ13FlPZPYPaP4PcPb%\~%IHS13Q2VP~PH%XHH04P>H02Q13Q0<$03Q0<#AS0<#2PdPePfPhPiPkQ18PGQ1<PmPnQ2TPBPnQ1WPBPnQ1XPBPnQ1Z/1TQ0;/M@,1wPqFgF4PCPFb9b:b;X09X19X29X39X>9Q0kQ1_Q1sQ1`=iJ_#~7n6\}[[^09^19^29^39^>9P:P\PMP^PWQ0Zp+01Ep+01TPrO8b5b7b4b8bGbFb6b<b=1006RH%~sS0k'<R~eP~PHP8Q2IPSQ2?H0FXI9P=Q0kP:D{b?P8PDPsQ1LPSQ2pQ06Flec0KWBQ2HQ2>'DPZPYPaP4PcPbQ2EQ2FQ0lQ2DPdPePfPhPiPkQ0dQ0qP:P8PDPsQ2CPSQ2ZQ0nFlQ1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q1i9BDsQ0IPDPVPSQ0JPS1ORXS0I#kS1iPS1OR;RH#kS2GPS1ORjR~#kS1NP[FyDQS0nQ0RQ0I'<S0IQ0V/<HS0VQ0Y/<~S0YQ0`'6S0R'6S2Z'6R~'6Q0cQ0nP~PSPXPDPVPSQ0JPSP:PSQ2?,OR#kQ2f,OR=qS[RRDKDQXLSPSP;PDPVPSQ0JPSQ2[PSP:PRDKDQXLSPSPjPDPVPSQ0JPSQ2[PSQ2?PSP:P[FyDQXLSg03N>$0@R[Q0=$0{P8[R8P1P>P?P<B0=S=:CjPKP>P?P<CjPKP>1>S<-0K?P=Cj'6R1[P>P?P<P=CjP>P?Q2`-0K<P:Cj'6PKP>P?B0=S<=Cj[RRPJPKP>B0=S?<Cj\1P>P?P<P=P:I1VP:n2001000000120000000XoAXnAXT9WqWtR1PR^oA^nA^T9^q8^t[R[P:Q02PDPVQ1{Q2OQ0KQ2<60=S60=SR8Q1{9BDVQ1{,>S-0KV=BD8R8PDQ1zPVQ1{Q0LPZPYPaP4PcPbPdPePfPhPiPkQ18PGQ1<PmPn11px9[nyRyPBPnQ1APBPnQ1BPBPnQ1F,1pQ2LQ1>'1Q1E'MRR'rDsF4PCPFb9b:b;X09X19X29X39X>9AL>:=R~Q1eQ2BQ1c'0/7URU5n?\P\N[^09^19^29^39^>9P:Q0ZP^PWP\PMQ29Q27PrO8b5b7b4b8b6b<b=Q1z/<VeJ00P1P[P:Q02PDQ2U,0VRVQ12Q2oQ2@60=SRHQ129BDVQ24,0V=BDHRHPDPOPVQ12P>PZPYPaP4PcPbPdPePfPhPiPkQ18PGQ1<PmPnPyPBPnQ1APBPnQ1BPBPnQ1;11R@RR'rDsF4PCPFb9b:b;X09X19X29X39X>9Q1d/7`10U_RU5n?\P\N\~^09^19^29^39^>9P:Q0ZP^PWP\PMQ2:Q0@PrO8b5b7b4b8b6b<b=1<OVeJ00P1P[P:Q02PDQ2U,0VRVQ2_Q2pQ2_9BDVQ0<,0VQ2p5BDR[PDPtPVQ2_P>PZPYPaP4PcPbPdPePfPhPiPkQ18PGQ1<PmPnPyPBPnQ1APBPnQ1BPBPnQ2811R@RR'rDsF4PCPFb9b:b;X09X19X29X39X>9Q1d/7610U_RU5n?\P\N\~^09^19^29^39^>9P:Q0ZP^PWP\PMQ2JQ1OPrO8R>b5b7b4b8b6b<b=1<tVeJ00PDPsQ2U,0VRVQ2pP?PZPYPaP4PcPbPdPePfPhPiPkQ18PGQ1<PmPnPyPBPnQ1APBPnQ1BPBPnQ1DPRP@FgF4PCPFb9b:b;X09X19X29X39X>9Q1d/7_10U_5n?\P\N\~^09^19^29^39^>9P>b5b7b4b8b6b<b=1<sVeJ00P[eH09O6b?PHeH09O6b?P8eH09O6b?Q1N&0hjJ0ZQ2G&0h;J0ZQ1i&0hXJ0ZQ0IQ2ZPLPDQ0MQ0QQ07PXQ08p,2UARXQ09Q0}PZPYPaP4PcPbPdPePfPhPiPkQ1jPGQ1kPmPnQ1lPBPnQ1nPBPnQ1XPBPnQ1oPBPnQ0oPBPnPnPqQ1Y,1o,1pR8Q0O#WRH'1R[Afn[wDuH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1uQ1w:0;K]RVQ0O'0R>?t>{[[\}[[^09^19^29^39^>9P:PMP3P^PWP\Q25Q2KPrQ21Q0iO:R>b5b7b4b8b6b<b=Q0Q#8R~?t~3ePZPYPaP4PcPbPdPePfPhPiPkPlPGQ1~Q2R7V=RNPmQ1Z=[n[PCPFb9b:b;X09X19X29Q1p:0D:]R[/7`Q1p:0;:]RPQ0O3L^09^19^29P:P^PWP\O3RUb5b7b4b8b6b<b=Q0rQ0P'<Q0rB0QL7:#eXI9R7PEP`PZPYPaP4PcPbPdPePfPhPiPkPlPGPuPmPnA9n@5RRPn1}55H0zPCPFb9b:b;13_`Ry@08``P:b5b7b4b8b6b<b=O2Q0PP:D{b?Q0Q#G>0QL~#eePDPOQ0P,0MQ2NP<PZPYPaP4PcPbPdPePfPhPiPkPlPGQ1TPmQ1;Q1>,1o,1xRO/1H,1p5[nPCPFb9b:b;X09X19X29X39Q1G:0D=]RH/7`Q1G:0;=]R]Q0O60;:5n:^09^19^29^39P:P^PWP\PMO4R1b5b7b4b8b6b<b=J0010M~Q2N5BDeN=0mQ0VQ0RPLPDQ0MQ0UQ07P;Q08PXQ09Q0}PZPYPaP4PcPbPdPePfPhPiPkQ1jPGQ1kPmPnQ1lPBPnQ1nPBPnQ1XPBPnQ1oPBPnQ0oPBPnPnPqQ0S#WR;,18R8Afn8wDuH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1uQ0S,0VRV?tV{[[\}[[^09^19^29^39^>9P>b5b7b4b8b6b<b=Q0U#8R~?t~3ePZPYPaP4PcPbPdPePfPhPiPkPlPGPNPmQ1\/MT=[n8PCPFb9b:b;X09X19X2917[6Q0S,0PRP'<^09^19^29PUb5b7b4b8b6b<b=Q2iQ0T'<Q2iP7PEP6PZPYPaP4PcPbPdPePfPhPiPkPlPGPuPmPnPnP@PTA9nT5DuPCPFb9b:b;136`9R_6P:b5b7b4b8b6b<b=O2Q0TP:D{b?Q0U#G>0QL~#eePDPtQ0T,0MQ2;P=PZPYPaP4PcPbPdPePfPhPiPkPlPGQ1TPmQ2811O;R;,1p5[nPCPFb9b:b;X09X19X29X3917H6Q0S,0]R],0:5n:^09^19^29^39P1b5b7b4b8b6b<b=J0010M~Q2;5BDeN=0mQ0YQ0`PLPDQ0MQ0XQ07PjQ08PXQ09Q0}PZPYPaP4PcPbPdPePfPhPiPkQ1jPGQ1kPmPnQ1lPBPnQ1nPBPnQ1XPBPnQ1oPBPnQ0oPBPnPnPq118@R8Afn8wDuH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1u10V_RV?tV{[[\}[[^09^19^29^39^>9P>b5b7b4b8b6b<b=Q0X#8R>?t>3ePZPYPaP4PcPbPdPePfPhPiPkPlPGPNPmQ1\/M@=[n8PCPFb9b:b;X09X19X2917[_?LP_^09^19^29PUb5b7b4b8b6b<b=Q2=Q0W'<Q2=P7PEP_PZPYPaP4PcPbPdPePfPhPiPkPlPGPuPmPnPnP@P@PRDuPCPFb9b:b;AR__yP:b5b7b4b8b6b<b=O2Q0WP:D{b?Q0X#G>0QL>#eePDPsQ0W,0MQ10P:PZPYPaP4PcPbPdPePfPhPiPkPlPGQ1TPmQ1D11;@,1p5[nPCPFb9b:b;X09X19X29X3917H_B0;:]_5n:^09^19^29^39P1b5b7b4b8b6b<b=J0010M>Q105BDeN=0mQ0[Q0_fxQ0>Q0^Q22Q0\Q0]PZPYPaP4PcPbPdPePfPhPiPkQ1QPGQ1SPmPnQ1VPBPnQ1WPBPnQ1XPBPnQ1[PBQ1\/1xQ1]59nF4F4PCPFb9b:b;X09X19X29X39X>9X@9Q1^Q1_Q1aQ1dQ1f7=K[\}[[^09^19^29^39^>9^@9P:P\P3PMP^PWQ0ZQ2WQ2KPrQ21O:b5b7b4b8b6b<b=Q0\eQ0AQ0CQ2WQ2XPZPYPaP4PcPbPdPePfPhPiPkQ15Q1gQ1h3H/wlPGQ1kPmPnPnQ1=,bwRm,}qPBPnQ1nPBPnA9nowPBPnPnQ1C11mw<0JpPBPnQ2\PBPn20yqpDsDNF4DNPCPFb9b:b;X09X19X29X39X>91:?<#2Q1rQ1KQ1b1:JK/0J;=?%2K%IK[[[[[^09^19^29^39^>9P:PMPWP^P\P3Q25Q2KPrQ21Q0iO:b5b7b4b8b6b<b=Q0BeO1H09K01K01K01K01c0Dc0Ec0FY0HWOP=P:O2n2001000010121000000W?WHP=P:O2n2001000010121000000b?c08H0pH0pH0pWDWCPSPEPSPvPSPKPSP=P:DKDK=hSQPDP0PSQ2QPSPgPSPJPSP<P=FyDQPSPSQ2SPSQ2MPSP|PSP?P<FyCoPIP2P:PzPIP2P:PzPIP2P:PzPIP2P:PzQ2an0110b00020010000n0110b0002001010bn0110b0002001010bn0110b0002001010bXJIPQP=H0_PzQ2cb?WDWCXUAZ0OSP=P:O2n10110101020121100101XUAXVSP=P:O2n10110101020121100101XUAX_SP=P:O2n10110101020121100101XUAXuSP=P:O2n10110101020121100101P=P:O2WDWCP=P:O2n2001000010121000000W?XmAP=P:O2n200100001012110a000bJc0BWHY0GP=P:O2n2001000010121000000bTc0CW~Y02P=P:O2n2001000010121000000brY0>Y0LP=P:O2n2001000010121000000W?W\P=P:O2n2001000010121000000W?W[P=P:O2n2001000010121000000W?WOP=P:O2n2001000010121000000W?WHP=P:O2n2001000010121000000b?bjbjc0?bxbwY0=Y0<P=P:O2n2001000010121000000W?Y0;P=P:O2n2001000010121000000W?Y0:P=P:O2n2001000010121000000W?Y09P=P:O2n2001000010121000000b?o"). Qed.
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Lemma rmalloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Lemma rfast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ].
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
End FASTFACTS.

End CANSEC1.
