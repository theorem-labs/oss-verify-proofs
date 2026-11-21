(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (wr8_comm, rconc_b, rsk_nonneg and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMalloc_fp () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Plain:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps@insert_insert_eqC59OSSVerify5KrLib6Malloc9MallocRep<s_shadow_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepCget_shadow_wr8_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@insert_insert_neC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C35stdpp4base6insertI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5Plain:RMallocRep9rmrep_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp:rsk_nonnegC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rmrep_wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_A=ticks_ok_wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_A:rmrep_wr32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib5Plain:RMalloc_fp8wr8_commC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib5Plain:RF_enframe@renframe_off_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RF_enframeArenframe_tail_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rc59OSSVerify5KrLib5Plain:RMalloc_fp8rwr8_repC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib5Plain:RMalloc_fp9rwr16_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp=wr16_wr8_commC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z7div_posC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib5Plain:RMalloc_fp9rwr32_repC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp=wr32_wr8_commC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC59OSSVerify5KrLib6Malloc@F_malloc_enframe9land_le_lC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp7rconc_bC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5Plain;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib5Plain<RMallocKit_A;rpres_writeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRepArmrep_shadow_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Malloc9MallocRep;b8_unsignedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRepCrreserved_disjoint1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg@ref_seg_rom_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep@rmrep_meta_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fpCrreserved_disjoint2C1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_add_distr_lC56Stdlib6ZArith6BinInt1Z7mul_1_rC59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib5Plain:RMallocRepBrwr_at_bytes_existC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z6divideI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_A:b8_of_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fp:rrdv_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC59OSSVerify5KrLib6Malloc=F_malloc_free;bytes_at_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib;setoid_ring<Ring_polynom3Mon00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib5Plain:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib6Malloc9Malloc_fp@round_up_pg_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9mf_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A;fact_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>lowbit_testbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_fast;lowbit_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A=mf_free_clearC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A7mf_hdr0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_AAmf_slots_completeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RMalloc_fpArget_meta_rec_st2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g _ ref_reserved).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x26000 <= b) /\ (b + n <= 0x26000 \/ 0x59000 <= b).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "h04__x1h14__x2h21Hh32H0h42Hnh57__arithh64__ffh78__varmaph85__with91bh:1np;3p;2p;1p;4p;7p;8p-1p10000R0p4p7210R1p8p1000Dp4p70R2p10019p4p710R3p8P2p1001Wp4p710R4p8P2p10025R5p4p710R6p8P2P5p4p7210p8P2p1002RR5p4p710R7p8P2P5p4p7210R5p8P2p1002kR8p4p710p8P2p1003Dp4p73110R2p8p1003Vp4p70R9p1004Kp4p710p8P9P4p8P9P6p8P9P8p4p741110R8p8P9P1p8P9P0p4p73110R9p8P3P7p8P3P5p8p1004gR1p4p73101R6p1005AR:p4p73110p8P6p1005ZR;p4p73110p8P6p10066p4p710p8P6p1006IR<p4p7201p8P6p1006[p4p7201p8P6P9p8P6p1006mR9p4p73110p8P6p1007AR=p4p73110p8P6p1007[p4p7201p8P1p4p710R6P:p4p710p8P6P;p4p710p8P6P7p8P6P5p8P6P0p4p710p8P6P9p4p710p8P6P=p4p710p8p1007nR=p4p710R6P3p8P6P7p8P6P5p8P6P2p8P=p4p741110R=p1008Bp4p73101R2p8P2P4p8P8P1p4p7511100R4p8P4P8p8p1008^p4p741110R8P1p4p76111100R4p8P4P8p8p10096p4p741110R8P1p4p771111100R4p8P4P8p8p1009Vp4p741110R8P1p4p7:1111111100R1p8P1P8p8P<p4p7200R<P=p8P=P<p8g009mj3]Tg00:ij3FTg00;Cj2ATg00;_j3LTg00<gj2>Tg00=Dj10Tg00=ij1;Tg00>Gj17Tg00>lj23Tg00?Gj15Tg00?fj2:Tg00@Oj3=Tg00A8j2DTg00Adj1XTg00BDj3CTg00Bdj1WTg00CDj2VTg00Cbj1UTg00D@j4QTg00D^j1PTg00E<j1OTg00Egj2?Tg00FJj3MTg00Fmj26Tg00GPj1KTg00H2j4@Tg00H]j2JTg00I?j2RTg00IYj2ITg00JEj3STg00Jdj4TTg00KVj2HTg00L2j2\Tg00LLj7GTg00M0j7[Tg00MTj7ZTg00N8j8YTf0R<#0#0p=B%0<#0#0#0p=9%0<#0#0#0#0#0#0#0p=8f3R=f2R8'Hf1R1/H<'\p=1P8g00N\R4g00O;R2P2g00O[R6g00P;R5P1g00PYP<C@g00Q@R7FGp=2P8P4P2P2P6P1P<F[p=4P8P4P2P2P6P1P<FZp=<P1P4P2P2P6P<P7FGp=NP=P4P2P2P6P8P1P<GYp=Eg00Q`R4g00R@?]1<g00SBR73Fg00SbR3/A1AL=811>=8R9g00T@R0#0R;#0R:#B#9#8#;R>%7:R:#0#9#8#;R?P=C1P9P?%7:R:#0#9#8#;R@P=C1P9P@%7:#9#8#;R:P=C1P9P:%00#7#7#B#7#9#8#;R9P=C1'3'3'3g00TeRAg00UQ#5#5RB#5RC#5RD#5RE#5,:51:5E1:5BRB5=55=5g00V0RE'D1:5D1:5C==5B5=5/DE%XA5CA3C%WAP51V58P1%U5CQ%P5%O5RA1?50R01?5;R;5M5RE165>52ARB165?RC=2A054AA2AEC165@RC=2A0RD54AA2AECRC165:RF=2A054AA2AEF1659=2A0R054A5<A5<A5<A%K2R2PAP51653g00V\P;C@,NAP2A4ABDA4AC05<ACECE1JA6P<P81R471I<8=F47dAS531CTb6b7b8X05X151><1R7P>P?P<C1P7P?P@P<C1P7P@P:P<C1P7P:P9P<C1'3'3'31A381>8=R=P>P@P8C1P=P@P9P8C1'3[[^05^15P<f4f5P1P8O4b5b3W4W2X:5X95o"). Qed.

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
  bytes_at psegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read psegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
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
  rw_cells psegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= ATOP
  /\ (G + 40 <= 0x10000 \/ 0x26000 <= G) /\ (G + 40 <= 0x26000 \/ 0x59000 <= G)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "p'0h01Hh14rid'h22r'h32r0h44rid0h51ri001rh64__x1h74__x2h84__x3h94__x4h:4__x5h;4__x6h<2arh=5ATOPRh>7__arithh?4__ffh@4__p1hA8__varmaphB5__withC4__x7hD1ahE2H0hF3Hr'hG1bhH2ghhI2r1hJ2r2hK4rid1hL4rid2hM1khN2H6hO4__p2hP4__x8hQ4__x9hR1oi011ohS3ridhT2CahU3DA1hV3DA2hW2H1hX3HrahY3LRahZ2NKh[3RFah\4RaALh]4RaB0h^3RaCh_3Sa1h`2_Hha3H10hb2H2hc2H3hd2H4he2H5hf2H7hg2H8hh2H9hi3_H0hj6__sat3hk6__sat4hl1ehm1ghn3rgaho1zhp4DISJhq2Eghr1Ghs2HGht2Hahu3Heqhv3Hk'hw3Hkkhx3LR'hy2MRhz2MSh{2NEh|3Sa0h}3SaLh~2WFi022WRi033_H1i043_H2i052a0i063arai075heq_Gi082kki091mi0:2sti0;1xp%0p%1p%2p&0p&1p;1p;3p;2p;4p;6p;8p;Bp;7g00=Dj19Tg015mk10aTg016Kk10]Tg016nS00k10KTg017Pk30kTg02k:k21=Tg00o8k208Tg025Pk210Tg02l9k20~Tg02m9k40{Tg00>Gj1MTg00=ij1RTg00<gj20Tg02[ik11XTg007nk40STg002kk40QTg00mdj11Tg00Wcj1mTg02\_j1GTg00KVj23Tg02mok60xTg02Tck20LTg02Udk30\Tg02Vck20ZTg02Wfk30YTg02Xgk20XTg02Yik20WTg02Zkk20mTg01A0j1QTg01Afj1VTg019Ij1NTg00:iS01j34Tg00WCk21DTg01:Ck41<Tg01:ak61:Tg02]Zj1cTg00>lR0j22Tg01;Bk107Tg01?Wk20OTg00;Cj2@Tg01T[j2_Tg02eFR1j2[Tg02o5k60}Tg01@9k100Tg0305k80zTg0316k10yTg02^Rk10wTg00I?j2~Tg00?Gj1JTg00?fk20[Tg00Adk10vTg00Bdk10uTg00Cbk10tTg00D^k10sTg00E<k10rTg00Egk20qTg00GPk11\Tg00Fmk20pTg00H]k21[Tg00IYk21ZTg00JEk31WTg00Jdk41VTg032:k41STg00lbk41QTg001Wk60BmB1Ak71BTg033Ck21PTg033Xk40UTg0342k41OTg01Vnk11MTg01WLk21LTg022?k20ITg00n[j2jTg0351k31Gk21FTg01Ybj2HTg01YAk20iTg013Bk203Tg01ZBk20hTg01Zik20bTg01[Pk20gTg01\6k20fTg01\\k20dTg013_k21ETg01f7k20GTg01J3k61CTg035bk21;Tg004Kk61>Tg02P\k61?Tg00fWk21@Tg01I4j4qTg01?Cj6xTg00L2S02j2wTg009mk30eTg0025k30jTg00g6k318Tg00@Ok30@Tg00A8k20cTg00BDk317Tg00CDk21KTg00D@k40VTg00FJk316Tg00H2k40?Tg00LLk70DTg00N8k80ATg01Wmk30nTg022hk315Tg01Bbk314Tg01IOk61TTg00MTk71UTg00M0k713Tf0R2#9#9p>0<%92#9#9#9p>0;%M2#Mp>0l%92#9#9#9#9#9#9#9p>01g01JWR300O2p=Cf5R4g00hGR5P3f4R6f3R7f2R8f1R9#NEx;42p=8g01MGR:&002g01N?R;34p>0P%Q2#Vp=E13781392'wp=71389/22,27,26p=l1[32p=513461378'w1[52,29'2p=<g00SbR<f7R='@f6R>/3413671389'w/22'2'2p==1292,28p=F1@<2p=O1067/381392'wp=a13671389'w/22p>0og00P;R?1H92;4<p=X1089/32p=Ag00R@R@@0e92p>1Jg00Q`RAg00SBRB742,29p>1I13<9/22p=IP5P3P6P7P8P9Ex=442p=>%Q9#V,08/32p=T1389/w2p>0RP6g02jCRCP7P8P9P2Exp=|20OC2p>0>B0j5?2p=eB185?2p=613<2p=?1392,28p>0E1H89=4?</22p=DP6g01KPRDP7P8P9P2Exp>0613671089/32'2,24,2>p=;1[52,29p>121@<71389/22'2p>11g000DREPCP7P8P9%c2Exp>05g036c/j2p=vg037]/02p=uA4E92,28p=hA4789/22p=\PEPCP6P7P8P9Ex=442p>0`1@92,28p>041_9294E8p>0_P5P3P7P8B0j5?9P2Exp>0220878109254?p=b%m9/22p>0|&009=4:;#m/22p=d1@<9/22p>0^1078/39/22p=W1@<71H89=4?</22'2p=`%Q2#V,09p=kA4:2;#mp>0FB0e@92=4ABp=S%M2#M#M#Mp=t1389/22p>0MA4?92p=Z20[?2p=KB0@?92p=]B0@?92g00V0R@+0cp=Yg00TeR;@1792p=L21K?2p=pP?P?P6P7P8H0VP9P2H0Vp=g20q?2p=^20p?2p=rB16?92p=:P?P9g00V\P2H0?p>0=P9g00N\R:g00O;RFPFg00O[RGP2g00Q@RHK0Dp=}P4P:PFPFPGP6P:PFPFPGP?P7g00PYRIP8H0?PHK0DP9P2L0Ap=nA4A2Bp>1Y20889=4?2p>1R1[52p>1NB0n?92p>0JB15?92p=zP?P8P9P2H0Vp=fB14?92p>0:P8P:PFPFPGP?P9g01]XRJP2H0?PHK0Dp=yP8P:PFPFPGP?P9PIP2H0?PHK0Dp=BP9P:PFPFPGP2J1Tp>0HP8P:PFPFPGP9P2K1Up=sP>P:PFPFPGP4P6P7P:PFPFPGP8P9P2L0AL0Ap=P109294?8p=i20c2@p>1HP?P9PJP2H0?p>0NP7P:PFPFPGP8P9P2L0Ap=oP6P:PFPFPGP7P:PFPFPGP8PHK0DP9P2L0Ap>0TA4?2<p>0CB0@?92:0@?8p=UB0n?89>0@?2p={P8P:PFPFPGP9P2K13p>091392,w8p>19g00i^g00T@RH#9S03#9RJ#9S04#9R@$0<RI$0a$0]Q04$0a$0]$0K[p,2rcRK@0k8921=7920868P?g02e`P6P221047-0~4H0{P2Q03#MS05#9$0<#RRL,02RM&1XKRNPM&0<I$0;RI$0;#RRO&0lJ#9$0;$01#RRPP2PMPP%9H$0l$0<#M$0;$01#RRMP2&0K3RQP5g00jWRRg00k0RSP3H0SRTP5PRPSP3H0QRUP9P=%C2RVE8RW&0P9RX106LS06%18RY%E8S07,0YRZP6C7[[^23^15PW&0P2RW#mR[%G2R\P8108LR]%12R^%E2R_'0R`'3DlX33#5X45E<G=PKP4P6P7P8P9J0xP8B0kK46P020LK>B0\K>420ZK4B0YK>420X>420W>43F3F%O8S0813]NP]POPPP8P]PPPMP8PQPTPUP9f9R]PVE8RaP>PLPYPZP>Da\X[^23^15PaP[P\P6Q06/3`DlX33#5X45E<I0o3FP2f8Ra-0LKB0\K]a20ZKaB0YK]a20X]a20W]a3F3FP9f:Rb-0LKP0f;Rc-0mKPQPTPUP9f=RdPVE8%19S09#OS0:Q09%RIRI'XS0;%Q9ReQ09%VeRe;ANRfQ0901Je+1I'I3FRg[^53^S5PQPTPUP7f?Rh#NRi%C8RjE>PQPTPUP8f@Rk#NRl%C9RmE>A4547#m%14Rn%E4S0<'0S0=%G7%17%G4S0>7T740R[Ro[[^J3^L5^I3^K521D5?Rp&0KCRqPpPEP5PRP?g00kNRrH1<RsP5PRPSP?Prg00kgJ1:RrPCH0SRSPEPsPrPCH0QRRP9%cdD|&0>2Rt34PQPTPU%e7RuPiPVE>Ri%67Rv#?RwAAvI_10^v:0E[\9DvI3FRx'2X53#5[^<C]D&0KDRyPpPEPsPrPDH0SRzPEPsPrPDH0QRrP9&07dI0620OD2Rs34PWPw%R@R@,0vP_1Xv@DlR@,2iX53#5[^HD^Gp'23FP=10=LRiPNPiPOPPP=PiPPPMP=PQPTPUP9f>S0?PVE8Ri10cLRvPYPZPcC7\X[^23^15PiP[P\P]P]PLP`F;X33#5X45E<G=P220mKdPQPTPUP9PlPVE>Pg[^53^S5PQPTPUP7fBRl#NRiPjE>PQPTPUP8fCRw#NRWPmE>Po[[^J3^L5^I3^K5PpPSPRP9%ckD|=4qtPQPTPUPuPiPVE>R{/2xX53#5[^<C^DpPpPzPrP9&07kI06=4ys12{@X53#5[^HD^Gp'23FP0PQPTPUP9fAR{PVE8Pg[^53^S5PQPTPUP7PWPjE>PQPTPUP8fDR|PmE8Po[[^J3^L5^I3^K5PpPSPRP9%c{D|=4qtPQPTPUPuPWPVE>R}/2xX53#5[^<C^DpPpPzPrP9&07{I06=4ys12}@X53#5[^HD^Gp3FPcPvPNPvPOPPPcC7S0@PvPPPMPcC7S0APQPTPUP9PiPVE>Ri10hLRvPYPZPhC7\X[^23^15PiP[P\PdPdPLP`F;X33#5X45+123FH11P2PQPTPUP9PWPVE>Pg[^53^S5PQPTPUP7fFS0B#NRgPjE>PQPTPUP8fGRW#NRiPmE>Po[[^J3^L5^I3^K5PpPSPRP9%c|D|=4qtPQPTPUPuPgPVE>R}/2xX53#5[^<C^DpPpPzPrP9&07|I06=4ys12}@X53#5[^HD^Gp3FP0PQPTPUP7PiPjE>PQPTPUP8fHR}PmE8Po[[^J3^L5^I3^K5PpPSPRP9fER~#cD|=4qtPQPTPUPuPiPVE>Ri/2xX53#5[^<C^DpPpPzPrP9&07~I06=4ys12i@X53#5[^HD^Gp'2PhPvPNPvPOPPPhPvPPPMPhPQPTPUP9PgPVE>Rg10wLRvPYPZPwC7\X[^23^15PgP[P\P{P{PLP`F;X33#5X45E<G=P2PQPTPUP7fIRgPjE8PQPTPUP8fJRj#NRiPmE>Po[[^J3^L5^I3^K5PpPSPRP9%c}D|=4qtPQPTPUPuPiPVE>Ru/2xX53#5[^<C^DpPpPzPrP9&07}I06=4ys12u@X53#5[^HD^Gp'2P1PEPqPSPRP8PjH05&0>9Rpg038VRD,@2,I2Ru%v2#uR@,_8Rs7h}C\XM?,[?X<C,[CXDEPwPvPNPvPOPPPwPvPPPMPwPQPTPUP9PiPVE>Ri10WLRvPYPZPWC7\X[^23^15PiP[P\P~P~PLP`F;X33#5X45E<G=PwPqPSPRP8fLRiH05PpAhujsC\XM?,[?X<C,[CP1PCPqPSPRP7fMRsH05PpfKRy1_7@5huC\XM?,[?X<CPWPvPNPvPOPPPWPvPPPMPWPQPTPUP9fNRvPVE8Rr10yLRzPYPZPyC7\X[^23^15PrP[P\PgPgPLP`F;X33#5X45E<G=P2PqPSPRP4fORrH05Pp1_4@9husC\XM?,[?P1P?PqPSPRP>fPRpH05&0>81_>@9huvC\XM?PyPzPNPzPOPPPyPzPPPMPyPQPTPUP9fRRzPVE8Rx10rLRtPYPZPrC7\X[^23^15PxP[P\PsPsPLP`F;X33#5X45E<G=P2PqPSPRPaPzH05&0>61_a@9hupC\P0PqPSPRP]fSRu#c&0>4J0`1@9D,I9fQR@%v9#u,_]3hPrPtPNPtPOPPPrPtPPPMPrPQPTPUP9fVS0CPVE8Rt10uLRxPYPZPuC7\X[^23^15PtP[P\P@P@PLP`F;X33#5X45E<G=P2PqPSPRPcfURR#c&0>=J0`%?6S0D@046DfTS0Ef<RS%v6#u'_3hP0%?4S0F@044D%v4#u:0_RdPuPxPNPxPOPPPuPxPPPMPuPQPTPUP9fZS0GPVE8RxfWRqPLPYPZPqDa\X[^23^15PxP[P\PRPRPLP`F;X33#5X45E<G=P2%?=S0H@04=DfXRD%va#u80_kPKf[S0IP{PdPzP4J0}PQPTPUPlf\Rx#NH02PVPxPlP^%6lRtCb%?t10tIP_%O^13`N9D^I5F[Ro9DtIDlC\X53#5P1P3PQPTPUPwf]R1#NH02PVP1PwP^%6wRtCb%?t10tIP_ADtIoDlC\X53PD10DLRtPNPtPOPPPDPtPPPMPDPQPTPUP9f_S0J#NS0KPVE>S0L10xLRtPYPZPxC7\X[^23^15Q0LP[P\Q0GQ0GPLP`F;X33#5X45E<G=P2PQPTPUP~Q0KH02PVQ0JP~P^%6~R^Cb%?^10^IP_AD^IoDlC\P0PQPTPUQ0B#ef`R^PmE8P^Q0BQ09Q0B#6RmCb%?m10mIPeQ0:Q0;;Ff-0|X9DmIDlPxPtPNPtPOPPPxPtPPPMPxPQPTPUP9fcRxPVE8Rt10^LRmPYPZP^C7\X[^23^15PtP[P\f^S0;Q0;PLP`F;X33#5X45E<G=P2PQPTPU%e}fbRt%C7E8PxPg%16Rf%6gReCb%?e10eI%E6Ro%OfS0:1XfI10foS0K/3N3F,d69DeIDlP0fdRePjPn%6jRoCbPoPIQ0<1XnIS0<Q0=<0EN-0^n,d49DoICW,IoP^PmPNPmPOPPP^PmPPPMP^PQPTPUP9fgS0LPVE8R^10eLRmPYPZPeC7\X[^23^15P^P[P\PtPtPLP`F;X33#5X45E<G=P2ffR^Pi%1=S0M%6iCb%6sRoPoPI%EaS0N%1aS0OQ0OPIQ0OQ0N;ANC`,da9DoICW'IP0%6vRo#?PoPI%E]S0P%1]S0QQ0QPIQ0QQ0P'0S0R/3NC`,d]9DoICWPePmPNPmPOPPPePmPPPMPePQPTPUP9fkS0SPVE8RmfhRo/0LRnPYPZPoC7\X[^23^15PmP[P\P^P^PLP`F;X33#5X45E<G=P2%6p#?%6@RmPI%ESRf%1SS0TQ0TPIQ0T?AfNC`,dS9DmICWP0%6zRm%EdS0U7AI%1dRfPfPIQ0U=AfNC`,dd9DmIPoPnPNPnPOPPPoPnPPPMPoPQPTPUP9foRnPVE8RmflRf/0LR_PYPZPfC7\X[^23^15PmP[P\fjRmPmPLP`F;X33#5X45E<G=P2Q0E#6%Eh7AI%6R%1kRm1XmIS0V1kmk<0EN+0^,dk7DIP0Q0C#6/XI%1{RkPkPIATk{NS0WC`,d{PfP_PNP_POPPPfP_PPPMPfPQPTPUP9fsS0XPVE8R_fpR{/0LRkPYPZP{C7\X[^23^15P_P[P\fnS0YQ0YPLP`F;X33#5X45E<G=P2%6D/XI%1|S0ZQ0ZPIQ0Z/k|S0[/3NC`,d|P0&00~$0F%1~S0\Q0\PIQ0\/k~S0]/3NC`P{PkPNPkPOPPP{PkPPPMP{PQPTPUP9fwRkPVE8RDftR_/0LRmPYPZP_C7\X[^23^15PDP[P\frS0^Q0^PLP`F;X33#5X45E<G=P2&0PWS0_#m%1}RDPDPIATD}NC`P0%1gRD#OATDgN9DDIP_PmPNPmPOPPP_PmPPPMP_PQPTPUP9f{S0`PVE8RmfxRD/0LR}PYPZPDC7\X[^23^15PmP[P\fvS0aQ0aPLP`F;X33#5X45E<G=P2%1y#O%1iRyATyiN7DIP0%1sRy/XIATysNPDP}PNP}POPPPDP}PPPMPDPQPTPUP9p+01@S0bPVE8R}f|S0cPLPYPZQ0cDa\X[^23^15P}P[P\fzR}P}PLP`F;X33#5X45E<G=P2%1r/XI%1p?TpNPKp+01AS0dP^PtP@PkQ0GPsL0z%G@%1@%6^'0'3PnQ0L#ePzPvO3%1zRvPvPI%QzRsPv%VsRsPN1SvsCW'IC`P0%1uRs#O%QuRuPs%VuRuPN1SsuCW'I9DsIf~Rs10sLRuPNPuPOPPPsPuPPPMPsPQPTPUP9p+01FS0ePVE8Rup+01CRv/0LRkPYPZPvC7\X[^23^15PuP[P\Q0dQ0dPLP`F;X33#5X45E<G=P2%1R#OQ0C#1RuQ0C#QRpPu%VpRpPN1SupCW'I7DIP0%1qRp/XI%QqRuPp%VuRuPN1SpuCW'IPvPkPNPkPOPPPvPkPPPMPvPQPTPUP9p+01JS0fPVE8Rvp+01GRk/0LRuPYPZPkC7\X[^23^15PvP[P\p+01ES0gQ0gPLP`F;X33#5X45E<G=P2fY#1/XIQ0G#QRvQ0G#1Rp%VvRvPN1SpvCW'IP0Q0I#QRv#?Q0I#1Rp%VvRvPN1SpvCWPkPuPNPuPOPPPkPuPPPMPkPQPTPUP9p+01NS0hPVE8Rkp+01KS0i/0LRuPYPZQ0iC7\X[^23^15PkP[P\p+01IS0jQ0jPLP`F;X33#5X45E<G=P2%Q1#?Q0;#1R1Q0;#ERkPN1S1kCWP0Q0J#1RkQ0J#ER1;AN1Sk1Q0iPuPNPuPOPPQ0iPuPPPMQ0iPQPTPUP9p+01RS0kPVE8Rup+01OS0lPLPYPZQ0lDa\X[^23^15PuP[P\p+01MS0mQ0mPLP`F;X33#5X45E<G=P2faRu#1?TuN%1t%Et'S%1xRt%QxRx#VRuP2&0yx13xu&0wKS0n%MHRK#MS0o#t#t#tRx#9#t#t#9$0<$0;$01$01#R%Mx#t#t#9$0<$0;$01$01#R,3N80MNS0pp+01US0qp+01SS0r+08Rx,~?p+01PR1/ZxRxePxg00UQRx#JRk#JS0s#KS0t%KkS0u20[?xRx']'Y&0v;Rk'L&0u;S0v&0t?R;P8%p8P9P;Dg&0s?S0w&0r?RvPv%9KS0x#^Rp%rIR}':S0y20q?HRy&1\FRiPvPv20p?<RmPpPi20=my,}vS0zEnEn21[vGS0{P2P81~AB21Z28$1YdB1W?<9H1VS0|b?bAbBX6?X7?AA9I2%?8Q08[[^6?^7?P2Q0c#6Q0L#ERBPqQ0IO4b>c07b=b0H1S10tuRuPOPPPtPuPPPMPtC7I0oP0%1eR0/keRtPOPPP0C7PtPPPMP0C7P1101LR0PNP0POPPP1P0PPPMP1PQPTPUP9p+01WPVE8R1p+01TR0/0LS0cPYPZP0C7\X[^23^15P1P[P\Q0kQ0kPLP`F;X33#5X45E<G=P2%1^R1/k^POPPP1C7Q0L#1R1PBPPPMP1DaPEf}R1fuS0k#v#uRB'_S08p+01YS0}fiRt#1S0~%6s'0Q0a#v#uS10'0Ru81R2XmEP?p+01XRq0081S11/0B1Z2uXo?P?%1o%61'0RAQ10,02/ZuXo?10ABRA,~?Q11PqP1PoPeH1QJ0BQ08-08qPqP1PBPQ%CoRB21P32XRQP3%CtS08=4QVZ0;3Po1~QBH0UPTPUP1%NqH02PeJ0BH1OJ0Bp+01VS11PfJ0BQ0r/ZA%O0Q0c/3NS10Q0cPOPPP0C7S12Q0cPPPMP0C7S13PQPTPUP9p+01[PVE8S14PqPLPYPZPqDa\X[^23^15S15Q14P[P\Q11Q11PLP`F;X33#5X45S16$1NS17'2S18'2S19'2S1:'2Q0nQ0pp-0Rq&1MH-1L?RHQ0s#JRZ#JS0s#KRA+0J%KZS1;Q0t20I?LS1<Q0u'z/]xS1=']S1>']S1?'Y/LkQ0v%p7P8P;P9%p6S1@?f6;DgQ0wPv%^JRJQ05#^RZ':Q0x#9S1A#9#RR1#rS1B%rLRBQ03#^Ro+0:':':9yvyS03PiPv20=mJ,}vS1CPiPvABvmZS1DPiPvABvmoS1E20Hv>5svPiQ0zFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?W@10871jL9,015i2%O7Q0FQ0D/2=%O6[[[[^6?^7?^8?^9?^@qP2Q1A#M#9#M#RRu,@DQ0d#6S0FQ0S#1S0DPDQ11P8PrQ0JP{O9b>b=Q10Q1:Q0nQ0pQ1?,]AS1?$1H/LkQ0vP;P8%p4S1:P9Q1@%p>S107f7DgQ0wPvPv1:ZpQ1B%^KRK-0:B':':-0NyPiPvPvQ0o#^Rr,:ZPoPiPvPvQ0yPrPiPv20Hva%ruS0y-0=K,}v5svPi1:yBS0o=BvoS0zCoEnEnI0TQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?X@q10761jL8,015i2AA6>8AA>I=B04]4uQ06/34[[[[^6?^7?^8?^9?^:?^;?^@qP2%?DQ0S#ES06Q0FQ0DPDPNQ11P8PjQ0IP{O;b>b=Q12Q19Q0nQ0pQ0b#6Q0;81GIS19%?IRjQ0F/HI#?[S12Q0D01FIS1FQ0D#?fm#1S1G/HIS1H#?\j[S1I%1f00iIS1J&0CIRj#mS1KQ1GQ1G003I,jIQ1H3i[S1HQ1G00hIS1G%OIS1LQ0Y#1S1M/HIS1NQ1N/@I'I[S1NQ1M00bIS1M1@I<S1O%1nS1P/HIS1Q,@IQ1Q<0E<[S1QQ1P00gIS1R%1{S1S003I$0C\jS1TQ1S00fIS1UfqS1V#1S1W/HIQ1W'Z\jS1Xg01^?S1YQ1W00dIS1ZeS1[Q1Zp+01H#600iIS1\Q1KQ0j#6S1]Q1]003I,jIQ1]/HI3i[S1KQ1]00hIS1]Q1LQ0f#6S0f/HIS1^Q1^/@I'I[S1^Q0f00bIS1_Q1OQ0i#6S0i/HIS1`,@IQ1`<0E<[S1OQ0i00gIS0ip+01LS1`#6S1a003I$0C\jS1bQ1a00fIS1aQ0m#6S1c/HIQ1c'Z\jS1dQ1YQ1c00dIS1YeS1eQ1YP6g015G21E<I'~Q1LeS1LO1S1fQ0h#6S1g/HIR<1@<I'IS1hPcQ1LO1S1LfyS1i#1/HIR<1@<I'IS1jQ0s#JS0s#JS1k#JS1l#JS1m#JR<#JS1n#KS1o%K<S1pQ0s#KR<;UA'YS0sQ1n#JS1n#JS1q#JS1r#KS1sQ1q#KS1qQ1n#KS1nQ1m#KS1mQ1k#KS1kQ0u']3U3UQ04#R-0I?/zxS0uQ1r#JS1r#KS1tQ1s-0JHS1uQ1oQ1pQ1l#KS1lQ1kQ1<Q1;'z']5{H5{H3U5{H'Y+0GS1vQ1vQ1uQ1q-0JHQ1nQ1mQ1k={Hx5{H5{H3US1uQ0uQ1tQ1sQ1nQ1pQ1lQ1</zA7U<3U3U'Y+0G/Lk'L'L'LQ0v%p=S0u%p]7f7P8Q1:P9Q1@%pa?f>;7f]DgS1sQ0wPvPvPvP:PFPFPGAyv}mJ1CRGPiQ1A#^S1A-0:}/:r9yvZCoS1nPiPvPvPGPiQ05#M#^-0:}Q04#^RG':9yvJCoS04PiPvQ03PiPv1:JpRF%rPR:5Bv%rMS1p=BvJ609vS1lPiPv%rOS1w9BvFABv:J609vS1xPiPvAyvGmS1yPiPvQ1CPiPvAyvrmS1zPiPv1:Z}=BvpS1{PiPvQ1DPiPvQ1EQ0y-0=o,}v5svS1EPiQ0oQ1w5BvABv:y609vCoFPFPFPFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?XP?XQ?g00lERF\jS1w1jI]Rj=i6>[S1|Q1wAi6ja[S1w10641jL7,015i8S1}P4P=PPPMP4DaS1~P>PaPOPPP>DaS20&0CcS21%OaS22&0CSS23AAcISS24%?SS251@cu,IcS26Q0@[[[[[[[[[[[^6?^7?^8?^9?^:?^;?^C?^P?^Q?P2p+01Q#6S0@003IQ0`#1Rj003I1HjIQ0@/HIQ0`#EQ0@PjQ0jp+01fS0@PaQ0?PlPwP|Q0IQ0JQ0LQ0SPnQ0dODS0db>bEbNp+01cR|/0LRjPOPPP|C7ebabhbgbfbNbebdbcbbbWbEb0bjbkb=Q13Q18Q0nQ0pQ19Q12Q1FQ1IQ1JQ1HQ1GQ1NQ1MQ1QQ1RQ1TQ1UQ1XQ1[Q1ZQ1\Q1KQ1]Q1^Q1_Q1OQ0iQ1bQ1aQ1dQ1eQ1YQ1fQ1hQ1LQ1jQ0sQ1vQ1vQ1uQ05#R-0I?/zA,]x20I?I/zxQ1r#J#KQ1tQ1qQ1oQ1mQ1k']3U3U'Y+0G+0G/Lk'L'L'LQ0vQ1sQ0wPvQ1nPiPvQ04PiPvQ03PiPvQ1lPiPvQ1xPiPvQ1yPiPvQ1CPiPvQ1zPiPvQ1{PiPvQ1DPiPvQ1EPiQ0o=Bv:Q1p=Bvy609vCoFPFPFPFPFPQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?XP?XQ?Q1|Q1wQ1}Q1~Q20Q21Q22Q23Q24Q25Q26Q0A[[[[[[[[[[[^6?^7?^8?^9?^:?^;?^C?^P?^Q?Q0db>bEbNPjPPPMP|C7ebabhbgbfbNbebdbcbbbWbEb0bjbkb=Q15Q17Q1421;82%G8/ZYp+01D#e9456S17P5Q0g#eS0gPQPTPUP2p+01`#NRY%C4R|E>PF]FX15PQPTPUQ0gp+01_Rj%C6E8PQPTPUQ0ePYH02%C>RY94Q2XRQP2%C{R:PfJ1>A4Q:|Q01PQQ1V#CR:%CaR|94Q9PF[P2A4Q:YQ0^#C%C=R:54QPQP3Q00P3P3P2P2P_n10110100021010000XlQQ0X#CP|P2J1?Q0X=43aA43_]P2Q0k=43bP3PcPFX53P3PcPQPTPUQ0m#ep+01gR|PVE8p+01hQ0hQ09Q1gCbQ0l#6Q077AI&007$0FQ0:Q0<%1>S07/k>Rf/3N%G=Q0M%60'0'3Q0OQ0N'SQ0RPOPPQ0QC7%1bRN/kbPPPMPNC7%CcRN%CW54QPF]F]V]U][]Y]^]\]]]Z]_]T]XXn3PQPTPUQ1`#eQ0@PNE8P|Q0mQ0TQ1cCbQ1gQ0U7AIQ0?$00$0F%1h#OQ0VQ0W%Gl%1lQ0r#6'0'3%1w%Ew'SQ0[POPPQ0ZC7Q0]PPPMQ0\C7Q0B#CRM=4QMP~Q0_P]P2O1-1@FbuWFWVWUW[WYW^W\W]WZW_WTWXQ0aP9Q0^Q0YP^Q0;Q0GQ0CPRQ0EPwPhQ0?P4NB1AQ0aP2J0BbWWEP2O1bEW0P2O1W0n2002101000000101A4Q2:PF[XRQPYO1P21~Q:O1b0bFWFP4P2P7K1BW0Q17#mR:eP:Q0jP4P6Q0gPnP7Q0SP2O7Q0K%GnQ1P%G67Tn40RQ02Q0=%G{'3Q1SQ0>7T{p+01\RnPLQ07PfPnDaP2Q1V#G,3fQ0nQ0pQ1;Q1>5{H,YA/LkQ0vQ0u9f;6P8Q1:P9Q109f;7DgQ0wPvPv1:oKRfQ1APiPv1:prRnQ1B20:BJ':':9yvyR:PiPvQ1A=BvnPiPvABvmJ20Hv]Rm5svPi20HvbRnABvfy609vCoFPEnQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?X@qXOqAA98>104>Rf1jL6,01R1'0RY,Z910>=RF,3a1I>bB19Sf6[[[[^6?^7?^8?^9?^:?^;?^C?^@q^OqP2Q0Q9AjLp+01BRf/@u%G_Q0f%1_RSPfQ0PQ0QPjP8PcPzQ1iO=b>b=W0P2O1Q1WQ1V%G>3TQ0nQ0pQ1?,Y</LkQ0vQ10?f7;P8Q1@P9P;P=Q0uP=Q1:DgDgQ0wPvPv1:pGQ0x#M#^RpPiPvPv20NpoPiPvP:PiPv1:r}R}=BvGPiPvQ0y-0=J,}v9svmPiQ0z>09vnCoFPI0TEnQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?XC?X@qXOqAA74>1Z=81Z8Y10=IRI/3aB04c>u104LRa@0R>d[[[[[^6?^7?^8?^9?^:?^;?^C?^@q^OqP2Q0R/3j%?f%G]%E_Q0fPSPfQ0QPjP8P>PcPeQ1iO>b>b=W0P2O1n200100000021100011000bRb{bxXvXWFX23X15P5Q16%esRsP3PQPTPUQ0bp+01Z#NH02PVQ0q,3\Q0q?AL`5F[C\X33PtPQPTPUPsQ0}Q08E8&00t$0FRs%GtQ0cQ0~/kt'380M0R0'2fePsP0P@Q0nQ0p20JH<Q1<Q0t'z=UAx'YQ1;Q1='],Y</Lk'LQ0vQ1@P8P;P9Q1:Q107f7DgQ0wPvPv1:KrRrQ1B20:BZ':':-0NoPiPvPvPyPrPiPvPvP}PJPiPvQ1DQ0y-0=Z,}v5svPiABvyo1:oB1:KJ5Bv5svCoEnEnI0TQ0{Q0|b?bAbBX6?X7?X8?X9?X:?X;?1084=i91107>,3913I4Q0H@04=u13aF:0M64[[[[^6?^7?^8?^9?^:?^;?P2Q0FPDQ06Q0DQ11Q0S#GP8PgQ0IP{O:b>b=CqCqH0UH0UCqCqCqCqCqbsWVWUP9P2O2n2001000010121000000b0W[Y04P9P2O2n2001000010121000000W0Y03P9P2O2n2001000010121000000W0WiP9P2O2n2001000010121000000W0W`P9P2O2n2001000010121000000c05bYW^W\P9P2O2n2001000010121000000W0W]P9P2O2n2001000010121000000W0WZP9P2O2n2001000010121000000W0W}P9P2O2n2001000010121000000W0W_P9P2O2n2001000010121000000W0W|P9P2O2n2001000010121000000W0WTP9P2O2n2001000010121000000W0WXP9P2O2n2001000010121000000W0Xn3P9P2O2n200100001012110;000blWqWwP9P2O2n2001000010121000000W0WtP9P2O2n2001000010121000000W0Z08?P9P2O2n200100001012110;000W0Z06CP9P2O2n200100001012110;000W0XDEP9P2O2n200100001012110;000WiWpP9P2O2n2011000010121000000W0Y02P9P2O2n2011000010121000000W0W`P9P2O2n2011000010121000000b0W`W~P9P2O2n2001000010121000000b0CqbrWzWyXmEY09Y0:o"). Qed.

(* [comment removed for export] *)
Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x26000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x26000 \/ 0x59000 <= r_base r).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"] "h01rh11Hh21ah33ridh42H0h52arh61bh72ghh82r1h92r2h:4rid1h;4rid2h<2Hnh=2_Hh>4__x1h?4__x2h@4__x3hA5ATOPRhB2H1hC2H2hD2H3hE2HrhF3RB0hG4RBALhH3RBChI3RFrhJ3RL0hK2WFhL2WRhM3_H0hN7__arithhO4__ffhP8__varmaphQ5__withR1mhS1qhT2r0hU2stp&0p;1p;3p;2p;4p;6p;7p;8g00=Dj12Tg015mj1oTg016Kj1fTg016nj1XTg017Pk30HTg02Tcj2]Tg02Udj3nTg02Vcj2lTg02Wfj3rTg02Xgj2uTg02Yij2eTg007nj4bTg002kj4aTg019Ij1:Tg01?Wj2MTg00=ij1GTg00mdj10Tg00<gj2=Tg02[ik10<Tg00>Gj1<Tg00>lR0j21Tg02Zkj2pTg01A0j1>Tg01Afj1?Tg00:ij38Tg00Wcj1dTg02\_j1cTg00WCk20OTg01:Ck40NTg01:ak60MTg02]Zj1WTg0025k30LTg00g6k30KTg01@9k10GTg00KVj26Tg01;Bj1VTg01YAk20ETg013Bj2YTg00n[j2qTg01Ybj2FTg01ZBk20DTg00;Cj2QTg01Zik20ATg01[Pk20@Tg01\6k20>Tg013_k20=Tg00I?j2mTg02^Rk10;Tg01Vnk10:Tg01WLk208Tg00?Gj1STg00?fj2NTg01Wmj3kTg00@Oj3OTg00A8k207Tg01f7j2jTg00Adk106Tg00BDk305Tg00Bdk104Tg00Cbk103Tg00CDk202Tg00D@j4iTg00D^k101Tg00E<k100Tg00Fmj2hTg01J3j6~Tg00GPk109Tg00Egj2ZTg01Bbj3}Tg00FJj3|Tg00H2j4[Tg00H]j2{Tg00IYk20?Tg00JEk30BTg00Jdk40CTg032:j4yTg01I4j4UTg01?Cj6tTg00L2j2xTg009mj3vTg02eFk20ITg00LLj7wTg00N8k80JTf0R1#2#2p=Rf2R2f1R3/11'1p=9f5R4g00hGR5g01JWR6f4R7f3R8P2P3Et;81p=4%21#2#2#2p=K%>1#?p=7g00SbR9/Q1p=5%>1#?,=3p=;%<1#<p=g%21#2#2#2#2#2#2#2p=J16821631'xp=31623/11p=Ag00P;R:1F23;89/11p=@1F31=8:9p=L1=78/62g00Q`R;g00R@R<?v31g00SBR=38'1p=B1693/11p=Cf7R>f6R?P4P7P8P2P3Et;81p=E1691p=`1=23/61p=_20I61p=D1=82/63/11p=H%?1,=3p>0FAv<31=8;=p=sA8:19p=\%<1#<#<#<p=IP:P3g01]XP1C[p=^P3g00N\R<g00O;R@P@g00O[RAP1g00Q@Fwp=PP8P<P@P@PAP2P3P1L0Jp=TA8;1=p=zg00i^g00T@RB#2RC#2RD#2RE#2RF#RRG#o#f%oE#f#X[p,2rcRE@0H82P01]E7AnE781lE8ArE781u781e783939%X6RHP5g00jWRIg00k0RJP6CbRKP5PIPJP6CaRLP8%:41M62RME4%RG#KRG#GRN%08RO%78RP,=ORQ&0<ERR%5PRP%07RS/;7RT%KG#GRG%gD#2#K#J#GRDPSC3[PTPD%2B#g#R#<#K#J#GRTPSC3\P'13A9@ON3A[P11]E?AnE>?1lE?ArE>?1u>?1e>?3939PHPKPLP?f8R?#:1M64E4P2f9R>,]EP0f:,pEPHPKPLP3f<RO#:1M61RPE4%03RS#51LSN%>3RUPS%?URUPRPSPUDB'C39RU[^06^35PHPKPLP8f>#:RSPME4PHPKPLP2f?RV#:RW1M63RXE4A8548#d%04/;4%c8PQ%c4C3[RQ[[^96^;5^86^:520O5:RYg02jCRZ%XZR[PYPZg000DR\P5PIP:g00kNR]H0NR^P5PIPJP:P]g00kgJ0MR]PZCbRJP\P^P]PZCaRIP3%WO1MZ1R_GEPHPKPLB0L5:8R`PSPPE4RSB0K5:8Ra#`Rb%71Rc9_aNg01MG&0G1g01N?38Rd#d%c1%01/=a'6'19@aN39Re'1X06#D[]5]2g01KPRf%XfRgPYPfP\P^P]PfCbRhP\P^P]PfCaR]P3%VO1Mf1R^GEPa%GFRFPc1LaFCH99dbRd,1SX06#D[]7^6Y'139%0?RSPS%7?R?PR%5?R?%0>Rb/;>RFPGPDPbC3[PFPDPTPbC3\?'1CH9@SN5ANP11pEOPHPKPLP3PWPPE4PU[^06^35PHPKPLP8fARW#:RSPME4PHPKPLP2fBR?#:RbPXE4PQ[[^96^;5^86^:5P[PYPZPJPIP3%WVP_GEPHPKPLP`PSPPE4RS/1eX06#D[^5Z^2YPgPYPfPhP]P3%VVP^GE11SdX06#D[^7f^6Y'139P0PHPKPLP3f@RS#:PPE4PU[^06^35PHPKPLP8PbPME4PHPKPLP2fCRF#:PXE4PQ[[^96^;5^86^:5P[PYPZPJPIP3%WSP_GEPHPKPLP`PbPPE4Ra/1eX06#D[^5Z^2YPgPYPfPhP]P3%VSP^GE11adX06#D[^7f^6Y39%0ORaPa%7OROPR%5OROf=Rc#0R\/;cRcPGPDP\C3[PcPDPTP\C3\O'1CH9@aN5ANP1PHPKPLP3PbPPE4PU[^06^35PHPKPLP8fERU#:RbPME4PHPKPLP2fFRM#:PXE4PQ[[^96^;5^86^:5P[PYPZPJPIP3%WFP_GEPHPKPLP`PbPPE4RP/1eX06#D[^5Z^2YPgPYPfPhP]P3%VFP^GE11PdX06#D[^7f^6Y39P3PSPVP>O3%0VRY#51LYN%>VRVPY%?VRVPRPYPVDB'C39P0%0SRV#5%>SRSPV%?SRSPRPVPSDB'C9@VN%0WRVPV%7WRWPR%5WRW%0?RS/;?R?PGPDPSC3[P?PDPTPSC3\W'1CH9@VN5ANP1%5S%0FRS%>FRVPS%?VRVPRPSPVDB'C7@NP0fDRV#0RS/LN%>VRVPS%?VRVPRPSPVDB'C%0URVPV%7URUPR%5URU%0MRS/;MRMPGPDPSC3[PMPDPTPSC3\U'1CH9@VN5ANP11LSNfGRS#>RV%0SRU%?VRVPRPUPVDB'CP0fHRV#>RU#`%0VRV%?URUPRPVPUDBfIRU#0RVPV%7URUPR%5URUfJRM#0RW%>MRM+0FR?PGPDPWC3[P?PDPTPWC3\U'1CH9@VN5ANP1%`MfKRM#0RV%7MRMPRPVPMDBP0fLRM#0RV%7MRM;_R1sVMfMRM#0RVPV%7MRMPR%5MRMfNRU#0RW/;URUPGPDPWC3[PUPDPTPWC3\M'1CH9@VN5ANP116URfORU#0%7U'sfPRU#0RV,6N1LVNRM%7URU=_VRRW%5URUfQR?#0RY%7?R?'=RfPGPDPYC3RP[RdPfPDPTPYC3Rf\UR^'1R]'1Rh'120EVN%\NRV#d1YYN,qN1FYN'=98:Y[20DYN%5NRgfRRZ#0Re/FNRb1QbN'C[20AeN1QN9fSRb#0R`/FNRL,QN16L9'1[20@`NfTRL#0RK/YN#\\V20>KNfURH#0R_/FN=8:_\V1Y_NP:fV#0/FNP:P4g015G20=9N'mPgeO11Q1N,C1&0;E%<BRE#<#I#I#IRg#2#I#I#2#R#K#J#J#G%<g#I#I#2#R#K#J#J#G,6R7ARg00TeRR&0:B-08:Rgg00UQR4#SRI#SRJ#SR[,N:RQ5k:1N:JRJ9k:g1N:4R45O:5O:%S[,N:AO:QJ5O:1N:I=O:4g00V0+07'j'j&06R405&04RP:P:&03:RRP2202:8CiP3PRCi&01:&00:RRPRPRP<P@P@PA1h:NR<1h:9R4'^,PRE~&09@R@1Z:BRB%2E,Z:9}:<1Z:CRC5|:'^,PRCTP@PR1^C4,PRP@PRP:P4g00V\PBC[,PRP@P:P<g00PYPBC[,PRCTCTCT1{RAP1P21m;=20?12#zdB0B:93H0CbObPbQX>:X?:X@:g00lE\V1qN8/=298:3[%\2%5216N8[[[^>:^?:^@:P1P7P8fZ#0P>PFPSO6bNbAb4bTbSbDbCbBb4b1PMPhP>PWP]P3PdP^PYP?P3P1CyR?11PfRfP01;eZRZPGPDPeC3RPPZPDPTPeC3Re1;`bRbPGPDP`C3P11;KLPGPDPKC3RK1;_HPDPTP_C3R_P3W4W1P3P1O2n2001000000120000000b2X<UP?PfP0PPPePbPDPTP`C3P1P1X4_X1KP3P1O2n2001000000120000000b2X<UCUCUCUCUWIWHP3P1O2n2001000000121000000W1WJP3P1O2n2001000000121000000W1WGP3P1O2n2001000000121000000W1WFP3P1O2n2001000000121000000b2WMWLP3P1O2n2011000000121000000W1W=P3P1O2n2011000000121000000b1WEW=WKP3P1O2n2001000010121000000W1X06X35WRWUo"). Qed.

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
    wr_at psegs m1 (P0 - 4) stride
    /\ bytes_at psegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= ATOP
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x26000 <= r_base r).
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_fp ()) ["CANSEC1"; "SLOT"] "p'0h04__x1h14__x2h24__x3h34__x4h47__sat18h57__arithh6:heq_strideh77__sat17h87__sat19h94__ffh:8__varmaph;5__with<5heq_Bh=6heq_P0h>4__x5h?1Hh@4__x6hA1ihB2HihC3LbshD3YbshE4__p1hF3Hi0hG4cstrhH2_HhI1zhJ1ehK1rhL1bi001bhM2ghhN2H0hO3_H0hP5__x10hQ4__x7hR4__x8hS4__x9hT1ahU1li011lhV2x1hW3H10hX3H12hY2H5hZ2H6h[3_H1h\3_H2h]7__sat20h^7__sat21h_2x2h`2H1ha3H11hb3H13hc2H2hd2H3he2H4hf2H7hg2H8hh2H9hi2Hahj4SPANhk5__x11hl5__x12hm2bshn3bs1ho3bs2hp1dhq1mhr2r0hs2r1ht4segshu2x3hv3AL'hw5ATOPRhx2CBhy1Dhz1Eh{3H14h|3H15h}3H16h~2HBi023HWri033Hb'i042Hci052Hdi062Hfi072Hqi082NGi092R4i0:3RALi0;2RCi0<3RI1i0=3RI2i0>2SHi0?2SKi0@3WF'i0A2WGi0B3WR3i0C3WRsi0D2Y1i0E2Y2i0F2Y3i0G2Y4i0H2YBi0I3YB0i0J3YB1i0K3YB2i0L3_H3i0M2ari0N2b'i0O2b0i0P2d0i0Q7fv_listi0R8hyp_listi0S3lmpi0T1oi0U1qi0V2q0i0W2q1i0X2q2i0Y2r'i0Z2r2i0[3ridi0\4rid1i0]4rid2i0^6stridei0_1vi0`1wi0a1xi0b1np%0p%1p%2p&0p&1p&2p;6p;1p;2p;4p;3p;9p;7p;5p;=p;8p;:p;<g039Mk628Tg00=Dj1<Tg00=ij1RTg00mdk10ITg00KVj23Tg01Ybj2_Tg00<gR0j20Tg02[ik11CTg00>Gj1LTg00>lR1j26Tg015mk10~Tg016Kk10{Tg01<;R2j27Tg03:Pk40dTg01=Gj1kTg02N6j2NTg00Adk10bTg00n[R3j2:Tg01Vnk10XTg02eFS00j2\Tg02^Rk11BTg00lbk427Tg00o8k221Tg00omk11~Tg0351k31}k20[Tg00BdS01k10@Tg00D^k11qTg00E<k11oTg00Egk211Tg00GPk11eTg00Fmk20|Tg00H]k21_Tg00I?k20?Tg00IYk21\Tg00JEk31ZTg00Jdk41YTg014@k41WTg03;Bk31UTg03;kk11STg017Pk31RTg02Tck21PTg02Udk31OTg02Vck21NTg02Wfk31KTg02Xgk21JTg02Yik21ITg00ZEk21GTg02F5k21FTg02Gnk11ETg00:ij3CTg00;CR4j2?Tg00?GR5j1DTg01WLk20YTg00?fk20wTg00Cbk11DTg03<Lm90vTg00BDj35Tg01YAk20WTg00Wcj1eTg013Bk20:Tg01ZBk20VTg01Zik20UTg01[Pk20TTg01\6k20STg01\\k20eTg013_k20cTg03=Ok31ATg022?k21@Tg01f7k20tTg03>0k625Tg02Iok124Tg02<Kj2>Tg00fWk220Tg02D?k30RTg00WCk20]Tg016nk10\Tg01:Ck41|Tg01:ak61zTg007nk40rTg002kk40qTg01;Bk11tTg01?Ck605Tg01?Wk20<Tg02Zkk21sTg019Ik11rTg01A0k117Tg01Afk116Tg009mk31pTg02\_k10nTg02]Zk11nTg01@9k10OTg03?8k31mTg03?\k21lTg03@<k11kTg03@fk210Tg03APk21jTg03B:k30`Tg03Bdk11cTg03CLk41bTg03D2k71aTg001Wk60ZTg011Pk21`Tg02S4R6j2ETg02<kR7j1ATg010hk21^Tg011mk31]Tg01mok31[Tg01Eik402Tg03Dak103Tg01XVk40iTg03EFk30=Tg02E@j4jTg03Eck51VTg01I4k409Tg03F\k10hTg03G^m=0mTg033Xk40pTg0025k31TTg00L2k21fTg00g6k31gTg00gSk41hTg02bQk51iTg00CDk21QTg00H2j4dTg00LLj7yTg00N8k80ATg004Kk612Tg01Wmk313Tg00@Ok30PTg00A8k218Tg00D@k40oTg01Bbk31MTg00FJk30^Tg01CEk31LTg00MTk719Tg03H^k41uTg022hk31vTg01J3k61wTg00M0k71xTg03I?m:1yTg03J0m<1HTg01IOk61{Tg01<Xk11:Tg02dVk30xTg02SLk31=Tg01EDm<1<Tg02?Om<22Tg03J]k723Tg00hGR8g00P;R9f0R:41Tp=F%<:#<p>0K%<:#<#<#<p>0Hg00SbR;9C9:p=^&17:$16p=a1?;:p=H%<:#<#<#<#<#<#<#<p>0>f2R<f1R='301f:p=|%L:#Lp>15%k==5<:p=qg02e`S02f4R>f3R?A5<=:Cjp=QB1g89:p=810=:,0<p>0;P8P9P=P:H1hp>0gg02Abg02FoP<P=P:I1ip>0f10=:9C9<p=J10<=/3:p==AC9<=/6:p=Z16=:,6<p=@%L:#L#L#Lp>0G13=:,6<p>0810<=/0:p>0D20?9:p=XAC9=:p=;13;:p=221Q9:p=Y20|9:p=TP9P=g00PYR@P:Cdp=}P<g00N\RAg00O;RBPBg00O[RCP9P=P@P:Cdg00Q@RDFyp=9P>PAPBPBPCP?PAPBPBPCP<PDFyP=P:L0Ap=Mg00Q`REg00SBRF7C:p>0jP?PAPBPBPCP<P=P:L0Ap>06P9P>P?P<P=P:J12p={1?=:,6<p>0720w9:p=IB139=:p=`B0P9=:p=PB0P9=::0P9<p=Gg00TeRGg00V0RH-18=;5:p=vP9P<P=P:H0op=V2119:p=UB1M9=:p=bB0^9=:p=1P<PAPBPBPCP9P=g01]XRIP:CdPDFyp=[B1L9=:p=Of6RJPAPBPBPCf5RKP>P?PAPBPBPCP<P=P:L0AL0Ap=4P9P9P>P?P<H0oP=P:H0op=uP<PAPBPBPCP9P=g00V\RLP:CdPDFyp=fP>PAPBPBPCP?PAPBPBPCP9P<P@P=CdPDFyP:K19p=t13;<1?=:'6p=sQ02P<P=P:Cjp=B13<=/6:p=SP9B0^9<=P@P:Cdp>0JP>PAPBPBPCP?P<P=PAPBPBPCP:PDFyL0Ap=zP9P=g00T@S03P:H1up>0uB139<=>0P9:p=WB1v9=:p>0EB0P9=:018Hp>0CA5G=:p>1?A5G=:95G<p>0aP=PAPBPBPCP:J1wp>1>PJPAPBPBPCPKP>P?PAPBPBPCP9P<PIB0^9=:CdPDFyL0Ap=gP9P<PIB0^9=:Cdp>26P<PAPBPBPCP=P:K1xp>0sP9P=PIP:Cdp=rg02ACRI1><=;C:p=hACI=:p>1;PIP?P<g01^?S04P=P:J12p>0_A5<=:,>?p=oAC8=:p=w20<=:9C?<p>0FP8g01JWRHP>P?P<P=J05=CK:p=m1_=:=C9;p>0Q10?</3=/6:p>1413;=/6:p>0Bg01MGg01N?7C:p>0N10>?/3<1_=:=C9;'6p=pA5<=:95>?p=KP9P;P=P0P3P2g01lLR@g027HS05g03KbRMP:N:1yp>1dP9P;P<P0P3P2P@Q05PMg03LCS06P=P:N<1Hp>0}P=PAPBPBPCP:J1{p>0l%A:,0=p>0LQ02&1::80x=p>0MA5<=:95>?95JKp=xB1=<=:9C>?p=c17=:,0<p=iP?PAPBPBPCP<P=PAPBPBPCP:PDFyK19p>0zg00UQS07/E:p=]PIP9P6P7P4g02hgRDQ07P;P?P<P=P:N<1<p>04Q0210>?$1:80xKB1=<=:5CJp=l10:;p=~PIPIP9P9P5P7P7P?g03M2P<P=P:N<22p>1XPIP9P6P7P4PDPKP>P?P<P=P:N<1<p>0kP9P=PLP:Cdp>0yPJPKP>P?P<P=P:H09H09p>0110<==C9:p=nQ02PKP>P?P<P=P:K23p>00p,2stRLp,2m1RDp,1bR4#FR7p,1rS08p,2MRS09p,2HrS0:J28Q03#<S0;#<R6#<S0<#<S0=$0KS0>$0KR5$0HRA#RRMQ08$0IR@'3S0?1_@MR2#^S0@Q08#aR3,0@R0p,2rcRN$1CS0A'3S0B%H3S0C&0HA#RRA%L6S0D#L#<$0H$0>#RRO/3@5|0S0E[S0FQ0CQ03#<$15$0K#L$0H$0>#RRP/3@9|0O[S0G'6S0H'6S0I'6S0J'6P1Q0?Q0JQ0<$0~RQ$0{RRQ02PDp,2P0RS%R6RT'7RUp,6strideRVH0dS0KPDPUPR%k;S0L1NQ<RW1NQ=RX1NQ:RY&0bRRZ5qRS0M5qRS0N5qRDQp,1oS0O%84R[Q0=#RR\p,3idxR],:VS0P40;R^Q03#LR_$0XS0Q'0S0R-0g7S0S80fLS0TQ0OQ0;$0XS0U,0^S0V-0g7S0W80fLS0XQ0OQ0VQ03#RR^'0S0Y-0g7S0Z80fLS0[p,1BS0\?J@[S0]Q0?A=SV0S0^Q0BQ0E'6S0_'6S0`'6S0a'6S0b7ZYS0c7ZXS0d7ZW3@XVR,\RX_R,\RXuRS0e'\RWP:Q0?Q0JP1Q0@Q0IPWP:Q0@Q0IP1Q0BQ0HPWP:Q0BQ0HP1Q0FQ0GPWP:Q0FQ0G&1BN%L_S0f#LS0g#L$15$0G$0GRX#<$0G$0G#<$0K$0H$0>$0>#RQ0A'3S0hQ0A%LX$0G$0G#<$0K$0H$0>$0>#RS0i408PLP4Q08Q0:H27Q0]PVP]Q0\Q0P80D\S0j#XQ0j,;SRXeRYPX221L4R4#XQ0\/;4R4eR`P4p,2mr$1~Ra#X1;VaRaeRbPap,2B0S0k:1}[\Rc%2\S0l1_[\S0m#2Rd[Re20[@MRf%2@%2M%22Rg[[Rh20[V\Ri%2VQ0l1_V\Rj#2Rk[[Rl&0bGRm&0@GRG%Y=S0n&1q9Rn&1o9RoPo%T\RpQ03-119Rq'}&1eBRB20|9;Rr=9oqS0oDM21_oCRCP:P<20?EFS0p21\:<$0jdB1Z9;=H1YRFb9b:b;X0913\:%2=RE[^09P:PVp,3S16RsO2b5b7b4b8b6b<b=PYPXP`P4PbPaPcPePfPhPiPlPmPGQ0nPnPoQ0oPBQ0oH06PCPFb9b:b;X09%2:S0qPE[^09P:P]p,3IDXO2b5b7b4b8b6b<b=H1WQ0P#210]^,:V10[\Rt?=:3XI9p,4SPANQ0P1:V^Ru'0RvB1UV]^D{A=tv3PuQ0P/0:==t3XI9P:PV&1SVD{Q0P/0V==t3Q09B1RNLDS0rP121PNLS0sB1ONLDS0t21NNDS0uB1KNLDS0v21JLDS0w21ILDS0x'6S0y'6S0z'6S0{'6S0|PWP:Q0sQ0|P1Q0tQ0{PWP:Q0tQ0{P1Q0uQ0zPWP:Q0uQ0zP1Q0vQ0yPWP:Q0vQ0yP1Q0wQ0xPWP:Q0wQ0xP:P7Q08Q0:p,2HkS0}O4Q02PDP@P3H0dS0~B07E=3g02iI21GL701F<&1E=3CPD10@?PR%k<PZDQ%2<%R5S10,?<3@[[`0_9`0T9S11'6P1Q0~Q11PWP:Q0~Q11Q02PDP@P3PUPVP=PYPXP`P4PbPaPcPePfPhPiPlQ07#DS12#DS13#DS14#DR5#DRE#IS15Q03$0X-0Y9Ru%I5S16'`Q12#IS17Q07-0w9S18'PS193G/vmPG%Y>R5&1D9Rv7V<S1:%YKS1;?V?vRw7V=S1<PnPo%U_S1=%U6R6'bS1>99orS1?PBPoQ0;#URxQ0;#L#URy,1qS1@5[oPBPo%TMRz=9oqS1APBPoQ1=99opS1BPBPoPo1}ryPB11xpS1CQ1>'1S1D%TTS1E'OS1F99oqDMF4F4PCPFb9b:b;X09X19X29X39X>91:<?S1G#2S1H10=KS1I,;<13M<S1J13\KS1Kf8R{#2S1Lf7R|/:{:0DJ\S1M/7T,3K[[[[[^09^19^29^39^>9P:P[P]PVQ0\P@fSS1NfTS1OfcS1PPsQ0kO:b5b7b4b8b6b<b=13@UePYPXP`P4PbPaPcPePfPhPiPlQ16Q19'P/vmS1QPGP5P<%YJS1RP=PwDuS1SPnPo%<_S1T#US1U,169[oqS1VPBPoA9oz6S1WPBPoA9opxS1XPBPoQ1U/1pQ1=,bxS1Y/1xS1Z'1=9oyS1[PB11qpRwQ1Y'1S1\Q1E'OR5/1x116yS1]59oF4F4PCPFb9b:b;X09X19X29X39X>9X@9AJ:?KS1^13M>S1_13\?R}10{\1:>KS1`/0>R~;=|S1a10>\S1b1:KJS1c'0S1d/7TS1e10|{S1f7=K[[[[^09^19^29^39^>9^@9P:P[P3P@P]PVQ0\Q1OQ1PPsfQO:b5b7b4b8b6b<b=A=UV0eN90vQ0KP=Q0P,0tRt/7TR0P;PYPXP`P4PbPaPcPePfPhPiPlQ14#IS1gQ13#IS1hQ18'PS1i'PQ15Q19'P/vm'vS1jPGQ1:Q1;9Vv?7V=S1kPnPoQ1Y99orS1lPBPoQ0f#US1m99ozS1nPBPoQ1XPBPoQ1Z,1w=9o6S1oPBPoQ0oPBPoPoPrP5Afo56DtH06F4F4PCPFb9b:b;X09X19X29X39X>91:=<S1p#2S1q13MKS1r10?\S1s?=~JS1t%2>S1u10K\S1v1:J|S1w'0S1x/7TR~?s~{[[\}[[^09^19^29^39^>9P:P@P3P]PVP[Q1OfdPsfRS1yQ0kO:b5b7b4b8b6b<b=p,4HDR0O410@0S1zQ0L=5RZS1{5BDS1|Q10#H9S;;S1}'6P1Q1|Q1}PWP:Q1|Q1}Q02PDPUPV%R_R_,7SR0P_PKPYPXP`P4PbPaPcPePfPhPiPlPmPGQ0nPnQ1E,OqR~%T_R5,OqRw59oPCPFb9b:b;X0917:T17:_'3^09P:PSO1b5b7b4b8b6b<b=PYPXP`P4PbPaPcPePfPhPiPlPmPG%Y<S1~?V=vPnPoQ1XPBPo11~x:0Jw5DzPCPFb9b:b;X09X1913\=17=_17=T/0<7=_[^09^19P:PVPSPsO3b5b7b4b8b6b<b=N90vQ02PDP0P_H0dPDP0P_P:PYPXP`P4PbPaPcPePfPhPiPlPmPGPvPnA9or5PCPFb9b:b;%2_P:b5b7b4b8b6b<b=PYPXP`P4PbPaPcPePfPhPiPl20WV\S20%^\RS#eS2120:V\S22,:\=JVj[S2320VV\S24%H\S25B07kj\S26[S2720UV\S281?\;S291?\j@08j;[S2:20TV\S2;Q22#^\SS2<20SV\S2=1;jV\SS2>Q0420eV\RkePk20W@M%^MRk#e20:@MS2?,:M=J@2[20V@M%HMRwB07g2MRg[20U@M1?M;1?M2@082;[20T@MQ2?#^\k20S@M1;2@\kQ0420e@MR~eP~20W[\S2@Q2120:[\S2A,:\Q0m5J[[S2B20V[\S2CQ25Q0m>07d\Rd[S2D20U[\S2EQ29Q0m,?\Q0m<08;[S2F20T[\S2GQ2A#^\SS2H20S[\S2IQ0m/;[\SS2JQ0420e[\R~eP~P>g015GS2K20c;\+0?Q25eS2LO1Pdf;S2MQ2K20c;M+0?PweO1PgfBS2NQ2LO1Q26%DES26#DS2O#DRE#DS2P#DS2Q#DRg#DS2R#DRw#DRd#DS2S#IS2T%IdRdQ0;20Y9^20Y9;S2U+0uS2V61A9R~%IwS2W%IgS2X%IES2YQ26#IS26Q15Q17'P5W~3G3W3G21@9\S2ZQ18+0ES2[Q2S#D#IS2SQ2T,`uS2\Q0;Q2U-0uu61A9RE/`dQ2Q#IS2QQ2P#IS2P,`uQ2O#IS2OQ26Q15Q16'P5Wu5WE3G3G5Wu+0C+0tRgQ2R#IRwQ2QQ16Q1gQ1h3GS2R'P+0CQ2PQ2R'PS2R-0CwS2]Q2\1`udQ2WQ2XQ2YQ26Q15,`uS2^Q18'P5WE5Wu5Wu5WE3GQ2[Q2SQ2TQ2WQ2XQ2PQ2O,`~Q26Q1g'P3G3G9W~d3G+0C+0tR~Q2]Q2QQ2R'P-0Cw21?gm40a80a~80ag40aPGf<Rg#YP{PvP>PvDuP<f:R~#YS2]9VvJP=f9Rw#YS2RPKPvP?Q2M#Y9Vv|DuDuPnPoPoA[opr-1>oS2QPBPoP6Q0=#U,bpQ1UFgPBPoPoA[ozr-1>oPBPoQ0<#US0<Q0g#U,bzQ0D#US0DFgPBPoPoQ2QPBPoPxQ0f#<#US0f,bpQ1mFgPBPoQ1lPBPoPoQ0<>26q6PBPoPoAforyS0gPBQ0</1yRd%TORE59o%TPS2[Q0<59o60soH06PBPoPoQ0gPB%TAS0g99odQ0<99oE60soH06PBPoPoQ0D/rrPBPoPoQ0<,}zPBPoPoQ1m/rrPBPoPoQ1U/rrPBPoQ1XPBPo116pQ1Z'1=9oyPBPoPo1}r6PBQ1\/O5S1Z/15Q0g59oQ2[Q1Z59o60soDMF4DMDMDMDMF4DMF4F4PCPFb9b:b;X09X19X29X39X>9X@9XQ9XR9XS9XP9Xk9Xl9g00lERz\SS2[1:\gRE=J>J[Pz\k1:Mg=Jw~[Q2[AJ>Ew[Q1`#2Q2M=J>|%Hwf=RE/0~13PE7|O[%H~f>S0gQ2M'0Q0g,3O7|A[f?S2S#^ROQ2S,3M13\gQ2S/0\Q0g,:E/0Ef@Rk3=%2kS2TQ0gQ2S/:k80D\/7_Rd/0_13Pd7|A[[[\O\O[[[[[[[[[^09^19^29^39^>9^@9^Q9^R9^S9^P9^k9^l9P:Q2AQ2?Q22P2P@PjQ0mP3P[P]PVQ0\PwQ2SfES2?fofpfrfsf{S2Xp+01@S2Wp,4SMODS2\p,3B16S2_PsfmQ0kOJb5bNbZbXQ0j/7_R2/0_13P27|Aeb}b|b{bbbXbabWbhbgbfbZbYbebdbcb`bNb?b7b4b8b6b<b=100_13P07|AeJ25&0@RRA&24_RP9hR:R2ABD0:'6S0jXmARO'\Q00PAPOPWP:Q0jP11>R=S2`01;PABD0=ROPWP:AhR?PABD0>Q01PRPW^DO^C2PK1>RZR201;PABD0ZP2PIp-0R2P:g014kS2aPzn0110b00020010000S2bXJIPPP=H0_Pz220W:S2cb?WDWCQ01PRA5R<:RO=hRPA5R?=S2d9BD0PW]D]CP:A5R=ZRd=hRPA5R<ZS2e9BD0A5R?ZS2f,>RPIP2P:PzQ2bn0110b0002001010bS2bXJIPPP=H0_PzQ2cb?WDWCQ01PRA5RJORO=hRPQ2d95R|S2d9BD0PW]D]CP:A5RKdRd=hRPQ2e95RJS2e9BD0PRPRP|Q2fCoPIP2P:PzQ2bn0110b0002001010bXJIPPP=H0_PzQ2cb?WDWCQ01PRA5R~O=hRPPDP0PRQ2MQ2dDQPW]D]CP:A5Rwd=hRPPDP0PRP~Q2eDQPRQ0eQ2MPRQ0KPDPUPRQ0L1NQERdQ0N5qRDQQ0TQ0d7Zd3@XVR,\RX_RP|PRQ0KPDPUPRQ0L1NQgRd1NQ{RWQ0M5qR5qRDQQ0TQ0XQ0c7ZW7Zd3@XVRP?13:_9S^:S0c17t=:0RL7S0MQ0020]89Rdg01KPRW&0\WS0dPdPWg000DS0NP8g00jWS0eP9g00kNROH1|S2eP8Q0eg00k0S2dP9POg00kgJ1zS01PWH0rS2bQ0NQ2eQ01PWH0qS2fP=&1tLS2gJ0520<W:S2h3CS2i%F=/w7S2j%8=S2k17t>S2lQ2lQ2kQ1T#<S2m#RRO'0S2n'?3S3@XMW'\XLdPzP:Q2iQ2jQ2k17tJS2lQ2lQ2n'?3S3@XMW,\WQ00PWQ0dPdPWQ2bQ2fP<Q2gJ05Q2h3C%F</w7%8<S2j17t|S2kQ2kQ2j/0O'?3S3@XMWPzP:Q0dPdPWQ2bQ2fP>Q2gJ05Q2h3C%F>/w7%8>S2h17twS2kQ2kQ2h/0O'?3S3@P1Q0dPdPWQ2bQ2fPKQ2gJ05PWP=H0F%FK/w7%8KS2k17t~S2h'3Q2hQ2k/0O'?3@PzP:Q0dPdPWQ2bQ2fP|Q2gJ05PWP?H0F%F{/w7%8{S2g17tES2f'3Q2fQ2g/0O'?3@P1%Fw/w7%8wS2fQ0g,7tS2gQ2gQ2f/0O'?3SPzP:Q2M#F/w7%8gS2gfAS2f,7tS2bQ2bQ2g/0O'?3SQ09Q0rP1Q0sQ0|PzP:Q0sQ0|P121sNLS0r&0\HS2bP8Q0eQ2dPHH0rS2gP8Q0eQ2dPHH0qS2dP=&1rLS0e20<H:S0dEm&0I=RN#H20QNM&17=S2hPNQ2h$16S2hQ0Ag00R@Q2h81pN$0jH14+0B3@[^KH`0[8S2kQ2bQ2gQ2dP?Q0e20<H<EmQ2bQ2gQ2dP<Q0e20<H=S2jEm1wK?#e&0IK%aKS2l'0&0n?&0I?%a?&0nK3=3|[[[`0ZH`0]8^sH`0\8S2ng02jCR8&0\8PdP8Q0NQ2eQ01P8H0rQ0NQ2eQ01P8H0qP=&1nLJ05P8P:H0FQ2bQ2gQ2d%F?Q0eQ0dEmS01%8?R8#2S2eP8PM%a:S0N20Q8M&0O:$0NRN#e&0n:&0I:/08'33@H143@XKH,\H[_0M^TdS2oQ2iQ01Q2eQ0N9=8\20Q8\3@7@NXKH,\H[^MW^LdS2i'6S01'6S2e'6S2pPzP=Q0rQ2pP1Q2kQ2ePzP:Q2kQ2eP1Q2nQ01PzP:Q2nQ01P1Q2oQ2iPzP:Q2oQ2iP:Q1yfNfJS1yO3Q2bQ2gQ2dQ1N#FQ0eQ0dEmQ1N#8R8P8P\Q0NP8P\Dp+0B7@NXKH,\HQ00PHQ2bQ2gQ2dQ1O#FQ0eQ0dEmQ1O#8R8P8P\Q0NP8P\Dp+0B7@NXKHPzP:Q2bQ2gQ2dfVS1O#FQ0eQ0dEmQ1O#8R8P8P\Q0NP8P\Dp+0B7@NP1Q2bQ2gQ2dfWS0N#FQ0eQ2jEm&0O=$0NQ0N#8RN#2PNP\Q2hPNP\Dp3@PzP:Q2bQ2gQ2dfY#FQ0e20<H?Em&0O>$0NfZS0e#8RN#2PNP\%a>PNP\Dp3@P1&0OK$0Nf[#8RNPNP\Q2lPNP\Dp+0BPzP:&0O|$0Nf^#8RNPNP\%a{PNP\Dp+0BP1f_#8RN#2PNP\%awPNP\DpPzP:fa#8#2fb#8RNP\%agPNP\DpP1Q1P#8RN%aE7=\20QN\PzP:fe#8Q2S#a7=\ff#800Q\PbPa20[[\%2[Pe[fi#8RN00[\%2NQ0lfk#8/_\#2[[PiPlPmPGPvPnQ2QPCPFb9b:b;Q2[P:b5b7b4b8b6:1mV\%^jS0l21l\VRN[R8Q0l\NRN'6P1P8PNPzP:P=Q2\O11::\,;VS2\XI9S0l,\9Q00P9Q0lPzP:Q2\P91:=\S0l1::]1:<]S00,:\';Z0^9&1k9S1PQ1P+0]S1P$0bQ1P$0@P9P<P9P]&0b9DK&0@9Q06P:P=Q03-109S0321j9\S0660`9Q0;-109S1P60`9S2lQ06Q03Q1P60`960`9S06Q04Q0p21d^=g03MV-0]9&1c9+0]$0@P9Q05Q2l:0}^:Q06:0}^:H1bc0S$0jdK1ac0Qc0RQ0l/:]1:=],:\S0l';ePVP:J0ZQ0PQ0l';Q00P9Q20Q23Q24Q27Q28Q2:Q2;Q2<Q2=Q2>Q22P9PjP9fz#800W\Q21Q2X#8Rj20:j\,:\1_j\3J[20Vj\Q25f|S21#8S22/_\Rj?sj\[Q2200U\Q29f}S22#8S25/_\Rj,?\@08j;[Q2500T\f~S25#8Rj00:\#^\S20Sj\Q2W#8Rj/_\/;j\S20:j\P9p+01AS29#8/_\P9Q2@Q2BQ2CQ2DQ2EQ2FQ2GQ2HQ2IQ2JQ2AP9Q0mP9PKQ2LO1Q0q@07:\PEQ2LO1Q1L@07{\Q2?Q2LO1Q2T@07k\PbPaQ2YQ2O,`uQ2VQ26Q2^Q16Q1i3G3W3GQ10-1@9Q18+0EQ0=$0X-0Y9RjQ2PQ2ZQ2Y+0EQ2U-0ujQ2O'`Q2ZQ26+0EQ2ZQ16+0EQ2ZQ1h+0EQ17,`j'P3G3G3W+0C+0t01?mPG%Y|Q2R7V~P<Q1;P=%Y{P>Q2]P?Q1RDuDuPnPoPoQ2QPBPoQ1mQ1T#L#U,bpQ1=FgPBPoPoQ2QPBPoQ1UQ2m#U,bpQ0<FgPBPoPoQ0D/bp,rxPBPoPoQ0</rrPBPoPoPoQ1UQ1m/1p1bxq'1/OyRjQ1U%TO'19fojDtPBPoPoPo%T^RjPyA9oy5DtPBPoPoQ1=/rrPB20logDMF4DMDMF4PCPFb9b:b;X09X19X29X39X>9X@9XQ9XR9XS9XP9XE2Q2[1:\~RS=JJ?[Q2[AJJS{[1:w\,;?%^w1:K>:0Dw\/7|RS10{O,?S5S{13{_9S^{%^{Q2f[[[[[[[^09^19^29^39^>9^@9^Q9^R9^S9^P9^E2P:PzPJPEfMS2[PgP[p+01NS1U#8p+01SS1mPKPVP]Q2MQ2NfLS0<Q1OQ29p+01RS1OQ2_OBb5b6bNbYbWbsc0XbbbXbabWbhbrc0WbgbfbZbYbebKc0Vbdbcb`bNb?c0`bzY07Z0U9P=P:O2n200100000012110a000c0PXHNXy8P=P:O2n2001000000121000000bAWvW\P=P:O2n2001000000121000000W?W[P=P:O2n2001000000121000000W?WOP=P:O2n2001000000121000000W?WHP=P:O2n2001000000121000000W?Z0YHP=P:O2n200100000012110a000bJY0AW\P=P:O2n2001000000121000000W?W[P=P:O2n2011000000121000000W?WOP=P:O2n2011000000121000000W?WHP=P:O2n2011000000121000000WHY0@P=P:O2n2001000000121000000b?Y04Y06P=P:O2n2001000000121000000W?Y03P=P:O2n2001000000121000000W?XMWP=P:O2n200100000012110a000W?Z0NdP=P:O2n200100000012110a000W?Q0M#eRdeY05Xp9Q0cPd[^p9P=PDP0PRPgPRP{PRP>PZDKDQP1%20S0cPRPRPEPRPwPRPKPZDKCo-0L0Q0;#RRdQ0>#RRW+1`RHPRPRQ0gPRP~PRPJPZDKCo,E:&0\RR8%A=S0;,00-0MDRNPRPRQ2SPRQ2MPRP|PZFxP=Dc[^AI3SQ0KPDPUPRQ0LPRQ0g,NQRS#kS0MPR1NQ~RO#kS0r1NQJS2p=qRZDKDQQ0TQ0XQ0[Q2pQ0b3Z7ZO7ZS3@P:Q0cPRPRPkPRPgPRP{PZDKCo-0L0PRPRQ2fPRPEPRPwPZDKCoS2p,E:P8PNPRPRQ2NPRQ0gPRP~PZFxRgP=Dc[^AI7SHP1Q2p#A==0H1>Rg,E:P8PNPRPRfCS2pPRQ2SPRQ2MPZFxS2kP=Dc[^AIQ0KPDPUPRQ0LQ2N,NQRgPRQ0MPRQ0rPZDK5qRDQQ0TQ0XQ0[Q0b7ZO7ZS7Zg3@P:Q2k,>R#A==0HPRPRQ2?PRQ2fPRPEPZDKCo,E:P8PNPRPRfFS2kPRQ2NPRQ0gPZFxP=Dc[^AI17t_S0r,0@RN#2Q2?=5RZS0M,>RS2e#AS2n==NHS01Q2k=5RZS2o,>RRg,E:S2iP8Q0;,0N-0MDS2\PRfG=5RZS2_P=Dc[^AIRS'6PYPXP`P4PbPaPcPePfPhPiPlQ16Q1gQ193G/vmS2mPGQ1:%Y?S2Q7V=S1TPnPoQ1?PBPoQ1APBPoQ1BPBPoA9orxS2]PBQ1D/O5,1qS1;99orF4F4PCPFb9b:b;X09X19X29X39Q1H13M=RM13\>ROQ1uQ1x=i>_#2[[[[^09^19^29^39P:P]PVP[P@Q2Xp+01LPsQ0kO8b5b7b4b8b6b<b=Q01PSPYPXP`P4PbPaPcPePfPhPiPl21^dWS01%HdS2R%2W%HH[S2P[S17%2dRSQ2aB1]dW=UWiS2ZQ2a%2H[^iSS26P=Q2K20c;d+0?Q2ReO1S2RQ2PQ15Q16Q1hQ19'PS1h3G/vmS16PGQ1:Q1RPKPvP?PvDu7V=S1:PnPoPo20lo{PoQ0DQ0i#T'}H0zS1RPBPoQ1@Q0D59oS0DPBPoQ1APBPoQ1BPBPoQ1CQ1>Q1='1'1=9oyS1@PBPoQ1;%TdRSQ0>$0~S0>61[9S1980JjDzF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0i:08JKS0iQ1I/3JS1IQ1JQ1KQ1vQ1w/0J;={S1vQ1M=iK_?=^H[[[[[^09^19^29^39^>9^@9^E2P:Q0hQ0AP3P]PVP[P@Q29p+01Gp+01OS2KPsQ21O<b5b4b7b4b8b]b^b6b<b=Q2iPIfHRW=5RZS2O,>RS2U,E:P8Q2\PRfIS2\=5RZS2YP=Dc]BP=Q2_,>RS0=#]P?Q07PYPXP`P4PbPaQ14#]%H_S1020?9;S2VQ14P_%X_S2^H04PRPRfKS1iPZCoS2T#]Q2T#AR;#HS2LQ2VQ2TP;%X;H04P?H02Q2LPRPRQ0<PZCoS0<$03Q0<#AS2L#2PcPePfPhPiPlPmPGPvPnAfor5PCPFb9b:b;Q10P:b5b7b4b8bGbFH0ib6b<b=PRPWPRfDR;A5RkZS10DKS2T,>R#]eO2P8PDP0Q07#AS1LPRQ2TQ07FlPYPXP`P4PbPaQ0<#]Q2L#HS2TQ2VQ0<Q2LQ2L#XH04P>H02Q2TQ2[=5RZS2[,>RS2T$03Q2T#A#2PcPePfPhPiPlQ1gQ185Wu/vmS18PGQ1<PnPoQ1]9[oqS2TPBPoQ1WPBPoQ1XPBPoQ1Z/1r11ypS2LQ1Y'1S0</O5,16PrFgF4PCPFb9b:b;X09X19X29X39X>9AJ:?>S0mQ1_Q1sQ1`'0/7_S1s#~10|\S2AQ1`'0S1`=iJ_#~';\}[[^09^19^29^39^>9P:P[P@P]PVQ0\p+01CS2JQ1OPsO8b5b7b4b8bGbFb6b<b=%~0S2I%~NS2H';RuePuQ2IP820MD:S2IPRQ1iH0FXI9P=Q2HP:D{b?P8PDPNQ1LPRQ2YQ07Flec0IWB%D:S2HQ2Y,>RS1i'EPYPXP`P4PbPa%D>S2GQ12'E%A>Ru/0^/?^S2FQ2G10:^Z0a9S2GPuO1Q2GP>Pu%XuH1XQ12P^%X^S2GJ0kP?H02S2EQ2F&03KS2D%AK#2S2CPcPePfPhPiPlPmPGPvP=Q0n9Vv=P=PvDuPnPoPoQ0f,}rPBPoPoQ0f/1j00yjPB20lo?DMDMPCPFb9b:b;X09XE2S0fQ0q10=^/?^P?[[^09^E2S0qP:P8PDPN%D~S0n#AS2BPRQ1N=5RZQ0nFl%A~S1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q0M9BDN17tdS2i,0@Ru#2Q2N=5RZS2N,>RS2@#A==uHS2>Q2p=5RZS2p,>RS2=,E:S2<P8Q0;,0u-0MDS2;PRA5R;ZS2:P=Dc[^AIS28'6PYPXP`P4PbPaPcPePfPhPiPlQ2mPGQ1TPnPoQ1?PBPoQ1APBPoQ1BPBPoQ2]PBQ1D/OS,1qS2799orF4F4PCPFb9b:b;X09X19X29X39Q1HQ1uQ1x=i>d#2[\O\M[^09^19^29^39P:P]PVP[P@Q21p+01MPsQ0kO8b5b7b4b8b6b<b=Q2>Q28PYPXP`P4PbPaPcPePfPhPiPlQ01Q17Q2ZQ26Q2RQ2PQ16PGQ1:PnPoQ1RPBPoQ0DPBPoQ1APBPoQ1BPBPoQ1@PBPoQ27Q1980JjDzF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0iQ1IQ1JQ1KQ1vQ1M=iKd?=^H[[[[[^09^19^29^39^>9^@9^E2P:Q0hQ0AP3P]PVP[P@p+01BS28p+01HS2>p+01PS24PsQ22O<b5b4b7b4b8b]b^b6b<b=Q2<PIQ2e,E:P8Q2;PRQ2oP=Dc]BP=Q2:,>R#]P>Q12PYPXP`P4PbPaQ12Q14'E1?^_S2;Q12P^Q2GQ14P_Q2^J0kQ2U#]Q2U#AS2G#HS23Q2VQ2UQ2GQ2G#XH04P?H02Q23Q1i$03Q1i#AS23#2PcPePfPhPiPlPmPGPvPnAfoj5PCPFb9b:b;Q2;P:b5b7b4b8bGbFH0ib6b<b=Q12PRQ2\PRQ2?Q2f=5RZS2;DKS2G,>R'EeO2P8PDP0Q12#AS2UPRQ2GQ12FlPYPXP`P4PbPaQ1i#]Q23#HS12Q2VQ1iQ23Q23#XH04P>H02Q12Q1y=5RZS12,>RS23$03Q23#AS23#2PcPePfPhPiPlQ18PGQ1<PnPoQ2TPBPoQ1WPBPoQ1XPBPoQ1Z/1jQ0</OS,16PrFgF4PCPFb9b:b;X09X19X29X39X>9Q0mQ1_Q1sQ1`=iJd#~7n^\}[[^09^19^29^39^>9P:P[P@P]PVQ0\p+01DQ1mPsO8b5b7b4b8bGbFb6b<b=100^S1m%~uS1i';S2GeQ2GQ1mP8Q2IPRPWH0FXI9P=Q1iP:D{b?P8PDPuQ1LPRQ2oQ07Flec0JWBQ2H/EgPYPXP`P4PbPaQ2EQ2FQ2DQ2CPcPePfPhPiPlQ0fQ0qP:P8PDPuQ2BPRfP=5RZQ0nFlQ1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q2N9BDu17t^S2<,0@Rt#2Q2S=5RZS1i,>R#A==tHS1mQ10,>R,E:S2GP8Q0;,0t-0MDS0;PRQ2;P=Dc[^AIS20'6PYPXP`P4PbPaPcPePfPhPiPlQ2mPGQ1TPnPoQ1?PBPoQ1APBPoQ1BPBPoQ2]PBQ1D/Oj,1qS1D99orF4F4PCPFb9b:b;X09X19X29X39Q1HQ1uQ1x=i>^#2[\O\M[^09^19^29^39P:P]PVP[P@Q22Q1UPsQ0kO8b5b7b4b8b6b<b=Q1mQ20PYPXP`P4PbPaPcPePfPhPiPlQ01Q17Q2ZQ26Q2RQ2PQ16PGQ1:PnPoQ1RPBPoQ0DPBPoQ1APBPoQ1BPBPoQ1@PBPoQ1DQ1980JjDzF4F4PCPFb9b:b;X09X19X29X39X>9X@9XE2Q0iQ1IQ1JQ1KQ1vQ1M=iK^?=^H[[[[[^09^19^29^39^>9^@9^E2P:Q0hQ0AP3P]PVP[P@Q2Jp+01Ip+01QS0APsQ25O<b5b4b7b4b8b]b^b6b<b=Q2GPIQ2@,E:P8Q0;PRQ2pP=Dc]BP=Q2;,>R#]PKQ13PYPXP`P4PbPaQ13Q14'E1?d_S0;Q13Pd%XdQ14P_Q2^J0kQ2e#]Q2n#HRHQ2VQ2eQ2nQ2n#XH04P?H02PH&03g%AgRH#2PcPePfPhPiPlPmPGPvPnAfoS5PCPFb9b:b;Q0;P:b5b7b4b8bGbFH0ib6b<b=Q13PRQ1yPRQ2kQ2NDKS2k,>R'EeO2P8PDP0Q13#APRQ2kQ13FlPYPXP`P4PbPa%]g%HHS13Q2VPgPH%XHH04P>H02Q13Q0=$03Q0=#AS0=#2PcPePfPhPiPlQ18PGQ1<PnPoQ2TPBPoQ1WPBPoQ1XPBPoQ1Z/1SQ0</Oj,16PrFgF4PCPFb9b:b;X09X19X29X39X>9Q0mQ1_Q1sQ1`=iJ^#~7nd\}[[^09^19^29^39^>9P:P[P@P]PVQ0\p+01Ep+01TPsO8b5b7b4b8bGbFb6b<b=100dRH%~tS0m';RgePgPHP8Q2IPRQ2?H0FXI9P=Q0mP:D{b?P8PDPtQ1LPRQ2pQ07Flec0KWBQ2HQ2='EPYPXP`P4PbPaQ2EQ2FQ2DQ2CPcPePfPhPiPlQ0fQ0qP:P8PDPtQ2BPRQ2[Q0nFlQ1NP>PKO4b5b7b4b8bGbFb6b<b=WBXAIP:O1n0110b0002011110bP:O1WBXAIK01Q1i9BDtQ0KPDPUPRQ0LPR1NQWS0K#kS1iPR1NQ;RH#kS2GPR1NQkRg#kS1NPZFxDQS0nQ0TQ0K';S0KQ0X/;HS0XQ0[/;gS0[Q0b'6S0T'6S2['6Rg'6Q0eQ0nPgPRPWPDPUPRQ0LPRP:PRQ2?,NQ#kQ2f,NQ=qRZRQDKDQXLRPRP;PDPUPRQ0LPRQ2\PRP:PQDKDQXLRPRPkPDPUPRQ0LPRQ2\PRQ2?PRP:PZFxDQXLRg03N>$0@RZQ0>$0{P8[R8P1P>P?P<B0=R=:CjPKP>P?P<CjPKP>1>R<-0L?P=Cj'6R1[P>P?P<P=CjP>P?Q2`-0L<P:Cj'6PKP>P?B0=R<=Cj[RQPJPKP>B0=R?<Cj\1P>P?P<P=P:I1VP:n2001000000120000000XoAXnAXT9WqWtR1PQ^oA^nA^T9^q8^tZRZP:Q02PDPUQ1{Q2YQ0MQ2;60=R60=RR8Q1{9BDUQ1{,>R-0LU=BD8R8PDQ1zPUQ1{Q0NPYPXP`P4PbPaPcPePfPhPiPlQ18PGQ1<PnPo11qx9[oyRyPBPoQ1APBPoQ1BPBPoQ1F,1qQ2LQ1>'1Q1E'ORQ'rDzF4PCPFb9b:b;X09X19X29X39X>9AJ>:=RgQ1eQ2AQ1c'0/7TRT5n?\O\M[^09^19^29^39^>9P:Q0\P]PVP[P@Q29Q24PsO8b5b7b4b8b6b<b=Q1z/;UeJ00P1PZP:Q02PDQ2U,0URUQ12Q2oQ2N60=RRHQ129BDUQ23,0U=BDHRHPDPNPUQ12P>PYPXP`P4PbPaPcPePfPhPiPlQ18PGQ1<PnPoPyPBPoQ1APBPoQ1BPBPoQ1;11QjRQ'rDzF4PCPFb9b:b;X09X19X29X39X>9Q1d/7_10T^RT5n?\O\M\g^09^19^29^39^>9P:Q0\P]PVP[P@Q28Q0APsO8b5b7b4b8b6b<b=1;NUeJ00P1PZP:Q02PDQ2U,0URUQ2_Q2pQ2_9BDUQ0=,0UQ2p5BDRZPDPuPUQ2_P>PYPXP`P4PbPaPcPePfPhPiPlQ18PGQ1<PnPoPyPBPoQ1APBPoQ1BPBPoQ2711QjRQ'rDzF4PCPFb9b:b;X09X19X29X39X>9Q1d/7d10T^RT5n?\O\M\g^09^19^29^39^>9P:Q0\P]PVP[P@Q2JQ1OPsO8R>b5b7b4b8b6b<b=1;uUeJ00PDPtQ2U,0URUQ2pP?PYPXP`P4PbPaPcPePfPhPiPlQ18PGQ1<PnPoPyPBPoQ1APBPoQ1BPBPoQ1DPQPjFgF4PCPFb9b:b;X09X19X29X39X>9Q1d/7^10T^5n?\O\M\g^09^19^29^39^>9P>b5b7b4b8b6b<b=1;tUeJ00PZeH09O6b?PHeH09O6b?P8eH09O6b?Q1N&0hkJ0ZQ2G&0h;J0ZQ1i&0hWJ0ZQ0KQ2[PLPDQ0OQ0SQ08PWQ09p,2UARWQ0:Q0}PYPXP`P4PbPaPcPePfPhPiPlQ1jPGQ1kPnPoQ1lPBPoQ1nPBPoQ1XPBPoQ1oPBPoQ0oPBPoPoPrQ1Y,1p,1qR8Q0Q#TRH'1RZAfoZ6DtH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1uQ1w:0;K\RUQ0Q'0R>?s>{[[\}[[^09^19^29^39^>9P:P@P3P]PVP[Q25Q2KPsQ21Q0kO:R>b5b7b4b8b6b<b=Q0S#8Rg?sg3ePYPXP`P4PbPaPcPePfPhPiPlPmPGQ1~Q2Q7V=RMPnQ1Z=[oZPCPFb9b:b;X09X19X29Q1p:0D:\RZ/7_Q1p:0;:\ROQ0Q3J^09^19^29P:P]PVP[O3RTb5b7b4b8b6b<b=Q0rQ0R';Q0rB0RL7:#eXI9R7PEP_PYPXP`P4PbPaPcPePfPhPiPlPmPGPvPnPoA9oj5RQPo1}55H0zPCPFb9b:b;13^_Ry@08__P:b5b7b4b8b6b<b=O2Q0RP:D{b?Q0S#F>0RLg#eePDPNQ0R,0@Q2OP<PYPXP`P4PbPaPcPePfPhPiPlPmPGQ1TPnQ1;Q1>,1p,1xRN/1H,1q5[oPCPFb9b:b;X09X19X29X39Q1G:0D=\RH/7_Q1G:0;=\R\Q0Q60;:5n:^09^19^29^39P:P]PVP[P@O4R1b5b7b4b8b6b<b=J0010@gQ2O5BDeN=0mQ0XQ0TPLPDQ0OQ0WQ08P;Q09PWQ0:Q0}PYPXP`P4PbPaPcPePfPhPiPlQ1jPGQ1kPnPoQ1lPBPoQ1nPBPoQ1XPBPoQ1oPBPoQ0oPBPoPoPrQ0U#TR;,18R8Afo86DtH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1uQ0U,0URU?sU{[[\}[[^09^19^29^39^>9P>b5b7b4b8b6b<b=Q0W#8Rg?sg3ePYPXP`P4PbPaPcPePfPhPiPlPmPGPMPnQ1\/OS=[o8PCPFb9b:b;X09X19X2917ZdQ0U,0ORO';^09^19^29PTb5b7b4b8b6b<b=Q2iQ0V';Q2iP7PEPdPYPXP`P4PbPaPcPePfPhPiPlPmPGPvPnPoPoPjPSA9oS5DtPCPFb9b:b;13d_9S^dP:b5b7b4b8b6b<b=O2Q0VP:D{b?Q0W#F>0RLg#eePDPuQ0V,0@Q2:P=PYPXP`P4PbPaPcPePfPhPiPlPmPGQ1TPnQ2711N;R;,1q5[oPCPFb9b:b;X09X19X29X3917HdQ0U,0\R\,0:5n:^09^19^29^39P1b5b7b4b8b6b<b=J0010@gQ2:5BDeN=0mQ0[Q0bPLPDQ0OQ0ZQ08PkQ09PWQ0:Q0}PYPXP`P4PbPaPcPePfPhPiPlQ1jPGQ1kPnPoQ1lPBPoQ1nPBPoQ1XPBPoQ1oPBPoQ0oPBPoPoPr118jR8Afo86DtH06F4F4PCPFb9b:b;X09X19X29X39X>9Q1qQ1rQ1tQ1u10U^RU?sU{[[\}[[^09^19^29^39^>9P>b5b7b4b8b6b<b=Q0Z#8R>?s>3ePYPXP`P4PbPaPcPePfPhPiPlPmPGPMPnQ1\/Oj=[o8PCPFb9b:b;X09X19X2917Z^?JO^^09^19^29PTb5b7b4b8b6b<b=Q2<Q0Y';Q2<P7PEP^PYPXP`P4PbPaPcPePfPhPiPlPmPGPvPnPoPoPjPjPQDtPCPFb9b:b;AS^^yP:b5b7b4b8b6b<b=O2Q0YP:D{b?Q0Z#F>0RL>#eePDPtQ0Y,0@Q10P:PYPXP`P4PbPaPcPePfPhPiPlPmPGQ1TPnQ1D11;j,1q5[oPCPFb9b:b;X09X19X29X3917H^B0;:\^5n:^09^19^29^39P1b5b7b4b8b6b<b=J0010@>Q105BDeN=0mQ0]Q0afxQ0?Q0`Q2>Q0^Q0_PYPXP`P4PbPaPcPePfPhPiPlQ1QPGQ1SPnPoQ1VPBPoQ1WPBPoQ1XPBPoQ1[PBQ1\/1xQ1]59oF4F4PCPFb9b:b;X09X19X29X39X>9X@9Q1^Q1_Q1aQ1dQ1f7=K[\}[[^09^19^29^39^>9^@9P:P[P3P@P]PVQ0\Q2WQ2KPsQ21O:b5b7b4b8b6b<b=Q0^eQ0BQ0EQ2WQ2XPYPXP`P4PbPaPcPePfPhPiPlQ15Q1gQ1h3G/vmPGQ1kPnPoPoQ1=,b6Rn,}rPBPoQ1nPBPoA9op6PBPoPoQ1C11n6<0JqPBPoQ2]PBPo20yrqDzDMF4DMPCPFb9b:b;X09X19X29X39X>91:?<#2Q1rQ1KQ1b1:JK/0J;=?%2K%HK[[[[[^09^19^29^39^>9P:P@PVP]P[P3Q25Q2KPsQ21Q0kO:b5b7b4b8b6b<b=Q0CeO1H09K01K01K01K01c0Dc0Ec0FY0HWOP=P:O2n2001000010121000000W?WHP=P:O2n2001000010121000000b?c08H0pH0pH0pWDWCPRPEPRPwPRPKPRP=P:DKDK=hRPPDP0PRQ0gPRP~PRPJPRP<P=FxDQPRPRQ2SPRQ2MPRP|PRP?P<FxCoPIP2P:PzPIP2P:PzPIP2P:PzPIP2P:PzQ2an0110b00020010000n0110b0002001010bn0110b0002001010bn0110b0002001010bXJIPPP=H0_PzQ2cb?WDWCXUAZ0ORP=P:O2n10110101020121100101XUAXVRP=P:O2n10110101020121100101XUAX_RP=P:O2n10110101020121100101XUAXuRP=P:O2n10110101020121100101P=P:O2WDWCP=P:O2n2001000010121000000W?XmAP=P:O2n200100001012110a000bJc0BWHY0GP=P:O2n2001000010121000000bTc0CW~Y02P=P:O2n2001000010121000000brY0>Y0LP=P:O2n2001000010121000000W?W\P=P:O2n2001000010121000000W?W[P=P:O2n2001000010121000000W?WOP=P:O2n2001000010121000000W?WHP=P:O2n2001000010121000000b?bjbjc0?bxbwY0=Y0<P=P:O2n2001000010121000000W?Y0;P=P:O2n2001000010121000000W?Y0:P=P:O2n2001000010121000000W?Y09P=P:O2n2001000010121000000b?o"). Qed.
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
