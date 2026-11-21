(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (61 recorded proofs replaced by written proofs (wr8_proj, cells_wr8_other, cells_wr8_same and 58 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W9 ASlot_W13 ASlot_W14 ASlot_M4P.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M5P () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC47Corelib4Init9DatatypesBsurjective_pairingC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC45stdpp;list_basics4list9app_inj_1C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp4base6lookupC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Malloc9MallocRepCget_shadow_wr8_sameC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib6Malloc9ASlot_M5P?cells_wr8_otherC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib6Malloc9ASlot_M5P7hav_wr8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib6Malloc9MallocRepDget_shadow_wr8_otherC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib6Malloc9MallocRepCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Malloc9MallocRepBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:land_assocC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula09K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesc59OSSVerify5KrLib6Malloc9ASlot_M5PCcell_read_wr8_same'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc9zero_hdrsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z6eq_decc59OSSVerify5KrLib6Malloc9ASlot_M5P>cells_wr8_sameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07c59OSSVerify5KrLib6Malloc9ASlot_M5P>zh_cells_otherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC47Corelib4Init9Datatypes2idK59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P6zh_havC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PBzh_cell_read_otherC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC46Stdlib5Lists4List7existsbC35stdpp4base6decideC56Stdlib6ZArith6BinInt1Z6ltb_ltC35stdpp4base>Is_true_true_2C45stdpp;list_basics4list;filter_consC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6NArith6BinNat1N3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propc59OSSVerify5KrLib6Malloc9ASlot_M5PCexistsb_filter_gt12C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7comparec59OSSVerify5KrLib6Malloc9ASlot_M5P@stale_hav_add_geC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3divC59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep@size_class_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W13:enf0_st_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W137enf0_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4PAput_meta_wr8_commC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4PGput_meta_zero_hdrs_commC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P=rec_zero_hdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P6nt_stTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P6nt_stWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7zh_projC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P8ntW_projC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABFget_meta_rec_put_otherC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P8ntT_projC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlc59OSSVerify5KrLib6Malloc9ASlot_M5P?zh_shadow_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P;hav_wr8_anyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P<havp_wr8_anyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7ntW_havC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P@cells_wr8_other'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P?shadow_put_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P?ntW_cells_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P:nt_writtenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init5Logic2ex01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib6Malloc9ASlot_M5P?ntT_cells_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7ntT_havC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P>ticks_ok_same2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P?zh_cell_read_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P9szc_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P<ntW_ticks_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PGcell_read_wr8_same_landC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PDcell_read_wr8_other'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init5Logic4True01I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=add_le_mono_lC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z?mul_add_distr_lC56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_idemp_lC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC56Stdlib6ZArith6BinInt1Z9add_assocc59OSSVerify5KrLib6Malloc9ASlot_M5P9slot_geomC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib6Malloc<MallocKit_ABDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7ntT_recC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7X_mod16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P:smg_rec_mtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P<nt_tail_hypsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P6sm_recC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib6Malloc9ASlot_M4P:smg_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P:ntF_rec_mtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W148st_modelC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P8smg_projC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PIcell_read_hdr_havoc_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P=ntF_shadow_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P?cells_hdr_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PChav_hdr_havoc_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P@mask_upto_range'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz01C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib6Malloc9ASlot_M4P>smg_groups_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PBntT_cell_read_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PCntF_cell_read_otherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z7mul_0_rC59OSSVerify5KrLib6Malloc9ASlot_M4P9smg_slot0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P=smg_meta_slotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P:ntF_strideC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op206c59OSSVerify5KrLib6Malloc9ASlot_M5P9ntF_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5P7ntF_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PCntT_cell_read_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5PAntT_cell_read_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P?smg_grp_hdr_covC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7div_posc59OSSVerify5KrLib6Malloc9ASlot_M5P@ntT_shadow_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M4P@smg_shadow_otherC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma wr8_proj q v st :
  s_regions (wr8 q v st) = s_regions st /\ s_groups (wr8 q v st) = s_groups st /\ s_areas (wr8 q v st) = s_areas st
  /\ s_tick (wr8 q v st) = s_tick st /\ s_next_rid (wr8 q v st) = s_next_rid st /\ s_reserved (wr8 q v st) = s_reserved st
  /\ s_ctx (wr8 q v st) = s_ctx st /\ s_slots (wr8 q v st) = s_slots st /\ s_metas (wr8 q v st) = s_metas st.
Proof. repeat split; reflexivity. Qed.

Lemma cells_wr8_other st q v o : o <> snd q ->
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! o = (r_cells (get_shadow st (fst q))) !! o.
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cells_wr8_same st q v :
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! (snd q) = Some (Z.land v 255, s_tick st).
Proof. rewrite get_shadow_wr8_same. cbn [r_cells]. apply lookup_insert_eq. Qed.

Lemma hav_wr8 st q v : r_hav (get_shadow (wr8 q v st) (fst q)) = r_hav (get_shadow st (fst q))
  /\ r_havp (get_shadow (wr8 q v st) (fst q)) = r_havp (get_shadow st (fst q)).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

Lemma cells_wr8_other' st rid off v o : o <> off ->
  (r_cells (get_shadow (wr8 (rid, off) v st) rid)) !! o = (r_cells (get_shadow st rid)) !! o.
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

Lemma cell_read_wr8_other' st rid off v o : o <> off ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
  intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
  - apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

Lemma zh_proj : forall k i st,
  let st' := zero_hdrs p s i k st in
  s_regions st' = s_regions st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ s_ctx st' = s_ctx st /\ s_slots st' = s_slots st /\ s_metas st' = s_metas st.
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.

Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
  intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

Lemma zh_hav : forall k i st,
  r_hav (get_shadow (zero_hdrs p s i k st) (fst p)) = r_hav (get_shadow st (fst p))
  /\ r_havp (get_shadow (zero_hdrs p s i k st) (fst p)) = r_havp (get_shadow st (fst p)).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
  pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

Lemma zh_cells_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! o = (r_cells (get_shadow st (fst p))) !! o.
Proof.
  induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH by (intros j Hj; apply Ho; lia).
  pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.

Lemma zh_cells_at : 0 < s -> forall k i st j, i <= j < i + Z.of_nat k ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! (snd p + UNIT + j * s - 4) = Some (0, s_tick st).
Proof.
  intros HS. induction k as [|k IH]; intros i st j Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cells_other by (intros j' Hj'; nia).
    pose proof (cells_wr8_same st (aadd p (UNIT + i * s - 4)) 0) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. rewrite C. reflexivity.
  - rewrite (IH (i + 1) _ j) by lia. reflexivity.
Qed.

Lemma zh_cell_read_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
  intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
  destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma zh_ticks_ok : forall k i st, ticks_ok st -> ticks_ok (zero_hdrs p s i k st).
Proof. induction k as [|k IH]; intros i st TK; cbn [zero_hdrs]; [exact TK|]. apply IH. apply ticks_ok_wr8. exact TK. Qed.

Lemma zh_cell_read_at : 0 < s -> forall k i st j, ticks_ok st -> i <= j < i + Z.of_nat k ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) (snd p + UNIT + j * s - 4) = Known 0.
Proof.
  intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cell_read_other by (intros j' Hj'; nia).
    pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
  - apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

(* [comment removed for export] *)
Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) :
  (forall ch, f ch = true -> 12 < fst ch) ->
  existsb f (filter (fun ch : Z * N => Is_true (12 <? fst ch)) l) = existsb f l.
Proof.
  intros Hf. induction l as [|ch l IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
  destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
  intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
  replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
  apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

Lemma cell_read_hdr_havoc_other st b o :
  snd b mod 16 = 0 -> ~ (snd b <= o < snd b + 12) ->
  cell_read (get_shadow (hdr_havoc b st) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
  intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id].
    assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
    fold (get_shadow st (fst b)).
    destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma hav_hdr_havoc_other st b u : u <> snd b / 16 ->
  (r_hav (get_shadow (hdr_havoc b st) (fst b))) !! u = (r_hav (get_shadow st (fst b))) !! u.
Proof.
  intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cells_hdr_havoc st b : r_cells (get_shadow (hdr_havoc b st) (fst b)) = r_cells (get_shadow st (fst b))
  /\ r_havp (get_shadow (hdr_havoc b st) (fst b)) = r_havp (get_shadow st (fst b)).
Proof.
  unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate :=
  wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
      (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
  (r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.

Lemma pp_eq : pp st3 g b idx = p.
Proof. reflexivity. Qed.

Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

Lemma nest_model_eq :
  upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
  unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
  rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
  unfold upd_meta. rewrite rec_zero_hdrs.
  change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
  rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
  unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ntW_proj :
  s_regions nt_stW = s_regions st3 /\ s_groups nt_stW = s_groups st3 /\ s_areas nt_stW = s_areas st3
  /\ s_tick nt_stW = s_tick st3 /\ s_next_rid nt_stW = s_next_rid st3 /\ s_reserved nt_stW = s_reserved st3
  /\ s_ctx nt_stW = s_ctx st3 /\ s_slots nt_stW = s_slots st3.
Proof. repeat split; reflexivity. Qed.

Lemma ntT_proj :
  s_regions nt_stT = s_regions st3 /\ s_groups nt_stT = s_groups st3 /\ s_areas nt_stT = s_areas st3
  /\ s_tick nt_stT = s_tick st3 /\ s_next_rid nt_stT = s_next_rid st3 /\ s_reserved nt_stT = s_reserved st3
  /\ s_ctx nt_stT = s_ctx st3 /\ s_slots nt_stT = s_slots st3.
Proof.
  unfold nt_stT. destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
  unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
  change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
    with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
  destruct (decide (q = mm)) as [->|NE].
  - rewrite get_meta_rec_put_same, G0. reflexivity.
  - rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
  intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
  rewrite get_shadow_wr8_other by exact NE.
  change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
  unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

Lemma ntW_hav :
  r_hav (get_shadow nt_stW (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stW (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stW, enf0_st, wr16.
  split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

Lemma ntT_hav :
  r_hav (get_shadow nt_stT (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stT (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
  rewrite A, B. exact ntW_hav.
Qed.

(* [comment removed for export] *)
Definition nt_written (o : Z) : Prop :=
  o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

Lemma ntW_cells_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  (r_cells (get_shadow nt_stW (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

Lemma ntW_cell_read_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  cell_read (get_shadow nt_stW (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntT_cells_other o : ~ nt_written o ->
  (r_cells (get_shadow nt_stT (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
  rewrite zh_cells_other.
  2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
  unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

Lemma ntT_cell_read_other o : ~ nt_written o ->
  cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
  unfold nt_stW. apply ticks_ok_wr8.
  assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
  eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
  cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
  intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
  apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
  intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
  unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
  assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
                          (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
  assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
  assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
  assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
  destruct (Z.eq_dec k 3) as [->|N3].
  { eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
  rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite 2 cell_read_wr8_other' by lia.
  destruct (Z.eq_dec k 1) as [->|N1].
  { eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
  assert (k = 2) by lia. subst k.
  rewrite cell_read_wr8_other' by lia.
  eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slot_geom :
  m_mem (get_meta_rec st3 g) = Some b /\ (s_regions st3) !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ 0 <= snd b /\ snd b mod 16 = 0 /\ 0 <= idx /\ 16 <= strideg /\ strideg mod 16 = 0
  /\ X + strideg <= round_up_pg (r_len r) /\ 0 <= strideg * idx
  /\ (forall b' gh, (s_groups st3) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= X - 4 \/ X + strideg - 4 <= snd b').
Proof.
  destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
  fold strideg in Sspan, Ss16, Ssmod, Snogrp.
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  repeat (split; [first [assumption | unfold X; lia] |]).
  intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

Lemma X_mod16 : X mod 16 = 0.
Proof.
  destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
  unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
  rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

Lemma nt_tail_hyps :
  meta_slot nt_stT mm
  /\ get_meta_rec nt_stT mm = mkMeta None None None 0 0 0 0 0 0
  /\ (s_regions nt_stT) !! (fst p) = Some r
  /\ 0 <= snd p /\ snd p mod 16 = 0 /\ snd p + 16 <= round_up_pg (r_len r)
  /\ (s_groups nt_stT) !! p = None
  /\ (forall b' gh, (s_groups nt_stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b')
  /\ (forall o v t, snd p <= o < snd p + 12 -> (r_cells (get_shadow nt_stT (fst p))) !! o = Some (v, t) -> (t < s_tick nt_stT)%N)
  /\ s_tick nt_stT = s_tick st3.
Proof.
  destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  destruct ntT_proj as (PR & PG & PA & PT & _).
  split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
  split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
  split. { rewrite PR. exact Sreg. }
  split. { unfold p, X. cbn. lia. }
  split. { exact X_mod16. }
  split. { unfold p. cbn [snd]. lia. }
  split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
           destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
  split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
  split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
           rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
           eapply FRESH3; [| exact Hc]. lia. }
  exact PT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
  apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

Lemma ntF_cell_read_other o : ~ (X <= o < X + 12) ->
  cell_read (get_shadow stF (fst b)) o = cell_read (get_shadow nt_stT (fst b)) o.
Proof.
  intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
  intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
  intros RQ FIT. pose proof szc_range as SZR.
  destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  pose proof ntF_stride as STF.
  pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
  destruct ntT_proj as (PR & PG & PA & PT & _).
  constructor; rewrite ?STF.
  - rewrite ntF_rec_mt. reflexivity.
  - rewrite PF1, PR. exact Sreg.
  - exact Skind.
  - exact TP0.
  - exact TP16.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
  - lia.
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - exact RQ.
  - exact FIT.
  - intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
    + left. unfold p. cbn [snd]. lia.
    + rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right]. nia.
  - unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
    rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
  - unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
    apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
  - apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
  - rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

(* [comment removed for export] *)
Lemma ntF_span_cells o : X + 16 <= o < X + 16 + 16 * szc - 4 ->
  (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
  intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

Lemma ntF_span_hav o : X + 16 <= o -> (r_hav (get_shadow stF (fst b))) !! (o / 16) = (r_hav (get_shadow st3 (fst b))) !! (o / 16).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ntF_rdv13 o :
  (r_cells (get_shadow st3 (fst b))) !! (X + 13) = None ->
  (r_hav (get_shadow st3 (fst b))) !! ((X + 13) / 16) = None ->
  (r_havp (get_shadow st3 (fst b))) !! ((X + 13) / 4096) = None ->
  rdv pans_mem o stF (fst b, X + 13) = 0.
Proof.
  intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
  rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
  unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ntF_unknown off h : 0 <= off ->
  cell_read (get_shadow stF (fst b)) off = Unknown h ->
  grp_hdr_cov stF (fst b) off
  \/ (cell_read (get_shadow st3 (fst b)) off = Unknown h /\ ~ (X - 3 <= off < X) /\ ~ (exists j, 0 <= j <= cnt /\ off = X + 12 + j * (16 * szc))).
Proof.
  intros Ho Hc. pose proof szc_range as SZR.
  destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
  2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
  all: right; rewrite ntF_cell_read_other in Hc by lia.
  - destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E). nia.
    + exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
  - destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
      [destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
      assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
    + exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
      pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
      pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
      replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
      apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.


End CANSEC1.
