(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Exec RzCPS MState.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_return R_return_T R_return_A R_prim_lists RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_drain_defs RT_drain_pure RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo RT_drain_cdk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_drain_cfast () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53B23;R_prim_defs7ri_tailC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op203C69OSSVerify5KrLib2K53B238RT_state5batchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53B23=RT_drain_defs:cdeal_fullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_defs6dh_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4r_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4r_flC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_defs7dh_keepC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnK69OSSVerify5KrLib2K53B238RT_state5regst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_defs9cdeal_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast6dh_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238RT_state5regst00C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53B23=RT_drain_defs8cdeal_caC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K52AG;R_sizeclass>MaxCount_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K53B23;R_quar_defs?firstn_upd_snocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs7ri_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53B23;R_prim_defs7ri_coreC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B23;R_prim_defs6fl_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep3cpwC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53B236RT_rep7reg_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5r_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_glue_defs5farunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_kit5dk_rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs2faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_kit6dk_geoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237RT_geo06geo_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6reg_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state2caC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53B238RT_state7ca_initC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC69OSSVerify5KrLib2K53B23<RT_drain_cdk<dk_stk_wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_freelift:farun_lenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238RT_state4ckst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6kFaCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state8kUserCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout@K_HIGH_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4reg0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B238RT_state4ckst01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53B238RT_state5kUMapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib2K53B23<RT_drain_cdk6cd_geoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs4tsepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_defs4recpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk8cd_postDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk6cd_msDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk7cd_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6p_abegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast:dh_keep_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC69OSSVerify5KrLib2K53B23=RT_drain_defs6set_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep:consts_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep8prim_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep9cache_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep9chunk_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep7sec_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep8quar_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep7dep_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep6fs_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep6ia_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep:shadow_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep7vis_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_geo9dg_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs:inst_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;R_prim_defs9mm_gcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_thread<thread_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_poison8ps_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_prim_kit7rwc_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk5cd_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;cstat_allocC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib2K53B23<RT_drain_cdk=dk_stk_withinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239RT_freeA2<fl_c8_of_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk6cd_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast<ri_tail_normC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_kit8dk_auserC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdeallocEcdealloc_drain_A_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs6cacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdeallocEcdealloc_drain_A_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs6cstatsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_return5dest2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_return_T<rta_ret_postC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast:bv64_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_return_A=rta_fast_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_return_T:rta_tail_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc=cdealloc_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdeallocEcdealloc_drain_B_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc:compact_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk4W_CDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state6framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7rt_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238R_return<dest2_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List:length_appC56Stdlib6ZArith6BinInt1Z7compareC69OSSVerify5KrLib2K53B23;RT_freelift8shad_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237RT_fkit;fk_shad_le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237RT_fkit<fk_shad_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_rC69OSSVerify5KrLib2K53B23=RT_drain_defs4uregC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib2K53B23;R_prim_defs8round_faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib2K53B23<RT_drain_cdk<dest2_prefixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast<cd_reg_drainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art3=reg_rep_ureg'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk<cd_full_trueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast>cdeal_reg_fullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep:pclass_repC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@firstn_length_leC69OSSVerify5KrLib2K53Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z3injC46Stdlib5Lists4List7map_appC69OSSVerify5KrLib2K53B23<RT_drain_cdk;cpw_compactC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk:cache_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat7add_1_rc69OSSVerify5KrLib2K53B23>RT_drain_cfast=cdeal_ca_fullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art36set_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_freestate4ARTcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk5TZ_CDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk5cd_TZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk6cd_TZdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<RT_drain_cdk7cd_certC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_pure<cdeal_reg_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art37artc_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art39client_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art3?set_st_pr_same'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_drain_art3;recp_set_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffc69OSSVerify5KrLib2K53B23>RT_drain_cfast6zal_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;i_premappedC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib2K53B235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B238R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc>cdealloc_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc>drainhalf_retBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc9rta_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:R_cdealloc=cdealloc_retDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23>RT_drain_cfast8cf_smallC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238RT_state4rtsA00C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h04__x1h11rh21Hh32Hkh47__arithh54__ffh66__sat0h78__varmaph85__with91kh:1qh;1xp;2p;3p;1p;4p;6p;8p;7p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000np4p7210p1001Kp4p710p8g001ij28Tg002Ej22Tg002ej30Tg003?j23Tg003\j27Tg0049j25Tg004Vj2CTg005Gj21Tg005cj1=Tg006Cj1<Tg006cj2;Tg007Aj1:Tg007_j19Tg008Jj2LTg008mj2KTg009Pj44Tg00:;j1JTg00:]j6ITg00;Aj8BTg00;ej2@Tg00<Gj2ATg00<aj2?Tg00=Mj3>Tg00=lj4DTg00>^j3ETg00??j6FTg00?[j4GTg00@5j7HTf1R1g00@YR0g00A8R2P2g00AXR3f0R4g00B8FHp=6g00BXR5g00C6R6f2R7'8f3R8,27=051P5f4R9f5R:/34/78505X:51589P51289159:,3:/749059X151C891168116:f6R;,2:,16[[g00CTR:#=%<:1;51%:5%95R:P0P2P2P3P51L56R<g00D@g00Dg,K5R=C4,6:%J2P:P0P2P2P3P5P=g00ELP<C4,6:EIGB1@:3P4P7g00F3R:g00FSR3'A1?47=0:3dA>561CDb5b7b8X051864A0516g00G3[[^05P4P;P8O2b4b69E89P7P4EFCGW2W3X15X;5W9o"). Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Lemma ri_tail_norm : forall (m : mem) R rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3 ->
  ri_tail m R rand exh pad (bv_unsigned (Z_to_bv 64 nal)) (bv_unsigned (Z_to_bv 64 nfr)) (bv_unsigned (Z_to_bv 64 r0))
    (bv_unsigned (Z_to_bv 64 r1)) (bv_unsigned (Z_to_bv 64 r2)) (bv_unsigned (Z_to_bv 64 r3)).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h01bh11Rh23exhh31mh43nalh53nfrh63padh72r0h82r1h92r2h:2r3h;4randp;1p;;p;2p;6p;3p;4p100GPp4p7210g001KR0p4p710p8g00H<j18Tg00Haj1>Tg00I?j1=Tg00Ibj1ATg006Cj1GTg00JDl;<Tg00KCj20Tg00Kij1ETg003\j2CTg00LGj1BTg00M?j1@Tg00N7j1:Tg00NVj2?Tg00ONj11Tg00PFj29Tg005cj1FTg00Q0j17TP0j66Tg00R6j34Tg00RVj4DTg00SOR0f1R1f0R234p=2f4R3f3R4f2R5A4012540540540p=3g00TGP5P1P2CDp=5A40129405p=;g00Dg#8#8#8R6#8#8#8R7#>R8#=R9%>6#=R6#A[g00BXR:%G6f:R;f9R<f8R=f7R>f6R?f5R@P3P4P5P1P2M;<P9108?R?f<RAf;RB%E7'CR7%B;RC%@<RDg00U?#:#:#:/?=RE%12RF198?RG,08RH#1108@R@,98RI,08RJ#11083R3,98RK,08RL#11084R4,98RM,08RN#11085R5,98RO,08RP#1%F0R0'2RQ'2RR'2RS'2RT'2D335X09P9P@PCPDPE108>#1RU12FTD395A7X09P9P3PCPDPEPU%1?RT?;FSD395A7X09P9P4PCPDPEPU%1@RS12FR5;TD395A7X09P9P5PCPDPEPUPTPS%13RRPFPQD3D395A7X09P91081R1PCPDPEPUPTPSPR%1412F0D3D395A7X09P21981R2,08%71E6PP%75E6PN%74E6PL%73E6PJ%7@E6PH%7?E6PBP;P<P=P>PGPIPKPMPOP2M;<eUX::X9:X8:X7:X5:X4:W6X26X;9W1W3o"). Qed.

Lemma bv64_range : forall z, 0 <= bv_unsigned (Z_to_bv 64 z) < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h02Hah14__x1h21Xh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91zp;1p;2p;3p;4p;7p;8g00H<j11Tg00Haj1QTg00KCj27Tg00U^j2=Tg00PFj29Tg00VQj1CTg001ij22Tg00W:j23Tg00Kij18Tg00WUj2<Tg00X=j2;Tg00XZj3:Tg005cj1PTg006Cj1OTg006cj2NTg007Aj1FTg007_j1ETg008Jj24Tg008mj2BTg009Pj45Tg00Y>j3ATg00Yaj7@Tg00:;j1DTg00;Aj8?Tg00;ej2GTg00<Gj2HTg00<aj2>Tg002ej3ITg00=Mj3JTg00=lj4KTg005Gj2LTg00@5j7MTg00C6R0f0R1'Lp=0f1R2g00@YR3g00A8R4P4g00AXR5P1g00B8FMp=6g00BXR6g00DgR7#1R8#1#1#1#1#1R9#QR:17:1R;'=19:;R;#0%C:,2;'3%88R8%89R9'<1208%091;89R;,20[[%08R<g00ZER=A:892UW0%0;\=^0<g00CTR<#P%O<1N62%F6%E6R<P3P4P4P5P<P3P4P4P5P61460g00Za1B67R7C5,6<P6P7g00D@1468=A6:C5,6<F@R8%D4P8G?1G<5P1f2R<g00F3R5g00FSR8'H1>1<=I58dAJ602CKb4b7b8X16%01121;'3%02122;'3[^16P1f4,7:,9:f3O2b3b5b6b2W9o"). Qed.

(* [comment removed for export] *)
Definition dh_reg (c : Z) (r : regst) (l : list Z) (mfa' : Z) : regst :=
  mkReg (r_muser r) mfa' (r_st r) (r_fl r ++ skipn (dh_keep c) l).

Lemma cdeal_reg_full : forall c r l, cdeal_full c l = true -> cdeal_reg c r l = dh_reg c r l (dh_mfa c r).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h01Hh11bh21ch31lh41rp;1p;2p;3p;4p;6p100[Hp4p70R0g001KR1p4p710p8P0g00\BR0p4p710p8g006Cj1>Tg00\_j28Tg002ej30Tg00]cj17Tg00^_j29Tg00__j14Tg00`Xj13Tg00aQj12Tg00bRj35TP0j36Tg00c0j41Tg00<Gj2;TP1j6:Tg00clj3=Tg00doj4<Tg00BXR1g00f0R0%>1g00F3R2f2R3f0R4'8g00FSR530P2P5P2P0P4f3R5#7f4R6/95%45%35%26=513561C1R6P5n0100000020000=006X12%731953R2%43%33%25f1R6551561C1,;01856P4E:A=536P5P3P6P2C<500eW0W3W4W2o"). Qed.
Lemma cdeal_ca_full : forall c i l, cdeal_full c l = true -> cdeal_ca c i l = firstn (dh_keep c) l ++ [Z.of_nat i].
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h01Hh11bh21ch31ih41lp;1p;2p;3p;6g006Cj1;Tg00\_j23Tg002ej31Tg00aQj15Tg00flj36Tg00gKj14Tg005cj1:Tg00R6j32Tg00\Bj30Tg00<Gj28Tg001Kj67Tg00gkj39Tg00BXR0g00hm%;0R1g00F3R2f2R3f0R4'3g00FSR531P2P5P2P1P4f4#5=603R5P3n0100000020000f3R6#4%:0R7520R8500A0058511X12%56f1R2560%43=207500R0,811362P4E7A9632=110eW0W4W3W2o"). Qed.

Lemma dh_keep_eq : forall c, 1 <= c <= 31 -> Z.of_nat (dh_keep c) = MaxCount c - MaxCount c / 2 /\ (dh_keep c + Z.to_nat (MaxCount c / 2) = Z.to_nat (MaxCount c))%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with66__sat3h74__x2h81xh91Hh:4__p2h;4__p3h<4__p4h=4__p5h>4__p6h?4__x3h@4__x4hA4__x5hB2H3hC2H4hD2H5hE2HchF2M1hG2M2hH6__sat4hI6__sat6hJ6__sat7hK1chL1yhM1zhN2z3hO2z4hP2z5p&0p;1p;2p;3p;4p;5p;6p;<p;7p;8p;Bg00Kij1PTg00iLj1KTg005Gj24Tg00j1k206Tg00H<j1OTg00k6j10Tg002Ej2GTg00W:R0j22Tg00aQj1ZTg00gKR1j1ITg0049j2<Tg00l5j2:Tg00lRR2j1DTg00m2j2WTg002ej3Aj1^Tg004Vj2VTg005cj1tTg006Cj1rTg006cj2NTg007Aj1pTg007_j1nTg008Jj2]Tg008mj2JTg00:;j1hTg00;ej2gTg00<Gj2LTg00<aj2fTg00=Mj3eTg00=lj4dTg00mIj1cTg009Pj4QTg00mgk405Tg00nHk304Tg003?k203Tg00nkk502Tg00oWj4bTg0102j2aTg010cj4XTg011Aj3`Tg011dk200Tg001Kj6~Tg003\R3j2_Tg012Bj2{Tg012ej3yTg013Bl<uTg013gj2STg014Ij2FTg00N7j1CTg014cj1sTg015Aj2qTg015bj3MTg016Kj2\Tg0174j3oTg017Wj4vTg00@5j7[Tg018Bj6wTg00Yaj7mTg00;Aj8lTg001ij2zTg018fj2kTg019Cl<|Tg019hlB}Tg01:Nj3YTg01;7j2jTg00R6k301Tg01;cj7iTf2R4f1R5'4f0R6'2p=7g00BXR7g00C6R87A6p=9AA756p=51486p=1P4g00@YR9g00A8R:P:g00AXR;P7P5g00ZaP6CQg00B8R<F[p=3P5P9P:P:P;P6Ewp=>P4P9P:P:P;P5P6Fmp=8f3R=P9P:P:P;P4P5P6Glp=6P5P9P:P:P;P6P<F[p=E1z86p=B1k86p==P7g00hmR<P7P7P2f4R2P1P=g01<GP4P5P6M<|p=RP<P<P<P7P7P7g01=4P1P1P1P3g01=Tf5R3P2P=P4P5P6MB}p=x1\76p=@AY7569Y74p=;AY756p=Ug00CTR>g01>7,j5<016p=?P7P5g00ELP6CQp=HP4P9P:P:P;P5P6Fip=Tg00DgR9#P%K9R?#KR@#K#K#P,4677620656%O9RA#PRB%05RC%OA#O#O#PRD,4C371GCB#9'2P0%04R0140D57B1G0B#9%Z=R0#I%0=RC1<CBRE':'5%DE,W0%DC5A<'2P6%02RC14CD57B%03/GB#9f6RC#0R0/<BRE#1RF14E0RGP0PB1V0BRH%10%1BRIf8RJ#0RK/GB#1[[RLp-0RM%t>RN%r>R>1N75RO%p7RP%n7RQ1]7BRR1J79RS53Q1>Q=58QRT%h:R:1]78RU=3QSC61gQ;R;P6P4g00F3RVg00FSRW'L1f64=AVWdAe785CdRWb3b4b5X17W0A7B65RV%15[^17^0MP614KDPKP=O3RXb2b6PHPLPNP>%c7RYPPP7PUg00D@PRCQ,EQP;PWb3b4b5%BBP6b2b6RZH05P0PBP0PZPHPLPNP>POPPPQPTP:B047RS93QSC6P;PWb3b4b5X17X0M203B5,45\V^17^0MPXb2b6I02Cb12FGf7RG#0RF1<FBRX':RV#DRT#IRO/5V%DXRL,WTRH%DFRZ5A<R[P7PV1<KB,:K,56XM71L7VR\PO1VFB%1Ff9RO#0R]/GB#1\I[1aKB%1Kf:R^#0R_/<BR`#1Ra\I[PNP>P71N74RbP5PYCXPPPQ1>Q21J7ARY=3QS58QP:A`7SY93QUC6P;PWb3b4b5X17X77X0M1456,241:54#1[^17^77^0MP6PaP`P_P=O4b2b6bH-00VE~P[%=VR[%=XR_'_Ra%=FR4'5P<P7%^<P1%^7%I5%I6'5AA<561{563yXL<X8<PHPaPTP[P6X87R[%=6X87RTPVPVP\DRPLP_P[PTPXPX1L7XDRExPZP4P[PTPFPF1L7FDRM<u1S8F%BF154F'2%9497F8'F%=KP71<]BR],S8%B]%=]RK/5]'2%9K97]8'F%=`P7f;R`#0R]1<]B':R],S8%B]%=]RK/5]'2%9K97]8'Ff<R]#0RK1<KB':#=P7f=RK#0RF/VB%1Ff?RF#0/GB#1\I[f>#0R4/aB%14f@#0R4/<BRT#1R[\I[g00U?RZ#CRX#CR_#CRL#CR\#CRV#CRa#@RH%@\R\%s9,q7R9%@LRL5M7R1%@XRX1\7ZRZ3;3;%Ca#@Ra%@VRV;;XAM79VAM79\?;LZRL'URX,UH%@_=;1Z9;V\A;\1ZRZ,UVAM79H?;VLA;aHZ/?N'?,?X'?'?'?'?'?P>P7PbP5P71N72P=1N73CXCXPPPQPQ%KA,J7RA93QUP:PQA3QURP:1J7@R@93QUC6C6P:PQ1>QGA`7A@RP,HS,EQ58QA3QPU1HSU,EQ58Q5TQP:PQ1>QJ1HY@,EQ58QA3Q@U1HYU,EQ58Q5TQP:PQ1>QO1J7?R?/HA,EQ58QA3QAU1>Q^58Q5TQP:PQ1>Q`A3Q@A58QP:PQA3QRA1>Q]58QP:Ao7SY/H?,EQC6C6C6C6C6C6P;PWb3b4b5X17X77X?7X@7XA7X0MX:MX;MX<MX=MX>M%1=%1C\I[1:23RI,55,2C%9597I8'F15=C,2J14C8R8%9='2'F153C,2^128`'F14JG,2KA7BJF1_CG/5J[[[[[[^17^77^?7^@7^A7^0M^:M^;M^<M^=M^>MP6144DP[%9G%B4%BT1:4T#BPTP4PGP3P=P5P2PCPJPOP`OAb2bIbJbPbDbObCbNbBCvCbb9%ZCRC#I1:0E'5%DE,WC%D05A<'2eWGWFP5P6O2n2001000000121000000b9WEXK7o"). Qed.

(* [comment removed for export] *)
Section RegDrain.
Variables (Σ : rtsA) (m m' : mem) (c : Z) (W : list ivl) (mfa' : Z) (ws' : list word).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis HR0 : reg_rep (l_SB (lay Σ)) c (pr Σ c) m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis HWs : disjoint_from W (shad (rb (l_SB (lay Σ)) c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
                   ((r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) / 8).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).

Lemma cd_reg_drain : forall (l : list Z),
  ri_lock m' R 0 -> ri_core m' R (Z.of_nat (length (r_fl r ++ skipn (dh_keep c) l))) mfa' au (r_muser r) ->
  (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m' R rand exh pad nal nfr r0 r1 r2 r3) ->
  fl_arr m' SB c ws' -> 4 * Z.of_nat (length ws') = mfa' -> firstn (length (r_fl r ++ skipn (dh_keep c) l)) ws' = map (cpw c) (r_fl r ++ skipn (dh_keep c) l) ->
  reg_rep SB c (dh_reg c r l mfa') m'.
Proof using HG Hc HR0 MU WM HWs.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) ["RegDrain"] "p'0h01Hh14__x1h22Hah37__sat10h47__sat11h57__sat12h67__sat13h77__sat14h87__sat15h97__sat16h:7__sat17h;6__sat9h<4cstrh=5cstr0h>7__arithh?4__ffh@8__varmaphA5__withB4__x2hC4__x3hD1chE7__sat18hF4__x4hG4__x5hH2_HhI3_H0hJ1ihK2wshL3_H1hM4__p1hN4__p2hO3exhhP3nalhQ3nfrhR3padhS2r0hT2r1hU2r2hV2r3hW4randhX3AU0hY2B1hZ2B2h[2B3h\2B4h]2FLh^2G1h_2G2h`2G3ha2G4hb2G5hc2G6hd2G7he2G8hf2HRhg3Hfwhh3Hwshi2LKhj2RChk2RThl3SHUhm4STSHhn3STUho2W1hp2W3hq3_H2hr7__sat19hs1lht2sti002sthu1zi011np%0p&0p;1p;2p;3p;6p;;p;4p;7p;9p;8p101>cp4p710g001KR0p4p710p8g006Cj1UTg01?jk10hTg01@bk10PTg01A[k10=Tg01BYk20gTg01CVj3~Tg01DUj2TTg00`Xj1PTg00aQk10KTg00bRj3XTg00gKj1:Tg01ELk10fTg00__j1]Tg01FLj2DTg003?j2>Tg00]ck100Tg01Flj6[Tg00H<j14Tg00Haj1zTg00I?j1yTg00JDl;wTg01Gkj2<Tg01HEj4hTg00Kij15Tg00flj3RTg01ICk10@Tg01J9j4QTg002ej37Tg01JUj4uTg01KOj1lTg01LIk207Tg003\j26Tg01MCj4STg01N8j1\Tg00l5j2mTg0049j2^Tg01Nnk102Tg01Okj4jTg00X=j2_Tg00W:R1j20Tg01Pck40[Tg01Qak10ZTg005Gj21Tg00iLj18Tg01R[k20YTg01SUk20XTg01TTk10WTg01UPk10VTg01VJk10UTg01WHk10TTg01XDk10STg01Y?k10RTg01Z9j2{Tg001ij2JTg014Ik20QTg01[4j2eTg00k6k10OTg01[kj2xTg00Ibk10NTg00lRk10MTg01\@j3cTg01\^k20LTg0000j3kTg01]@k10JTg005cj1bTg01^<k30ITg002Ej2aTg01^Sk10HTg01_Qk10GTg01`Nk10FTg01aLk20DTg01bRj1sTg0102j2`Tg00WUj2VTg00XZj3WTg004Vk20ATg006cj2NTg007Ak10?Tg007_k10>Tg008Jj2OTg008mj2qTg00:;k10<Tg00;ek20;Tg00<Gk20BTg00<ak20CTg00=Mk30:Tg00=lk409Tg01c7k40ETg00oWj4ATg00?[k408Tg00N7j1ZTg016Kj2YTg01:Nj3dTg01;7j2vTg00R6j3oTg00mIk106Tg00nHj3nTg0174j3|Tg01cbj7}Tg01dgk305Tg011Ak30eTg009Pj4fTg00mgk403Tg01efk20bTP0k60aTg01fhm90`Tg00c0k401Tg00\Bk30_Tg00dok40^Tg00@5j7iTg018Bk60]Tg00Yak70\Tg00;Ak804Tg010ck40cTg00BXR0f1R2f0R340_p=H1D03p=@%43#4p=E1<03p=;A7023p=Gf2R41023'0p=9f6R5f5R6f4R7f3R8P4P2H0^P3Cup=3%83#4p=L%83#8p=Fg00C6R9/J3p=C%43#4#4#4p=K%43#4#4#4#4#4#4#4p=I1193p=2A7039p=gP4g00@YR:g00A8R;P;g00AXR<P0P2g00ZaR=P3Cfg00B8R>Fip=MP2P:P;P;P<P3J0]p=rP4P:P;P;P<P2P3K0\p=pP8P:P;P;P<P4P2P3L04p=tP0P4P2P3H0cp==1q03p=?P6P:P;P;P<P7P:P;P;P<P0P8P=P4CfP>FiP2P3L04p=BP2P:P;P;P<P3P>Fip>0d%U0R>p,2m'R:p,2ΣR=$0hR?$0PR@$0=p,1cRA+0gRB;~9S00P:PB1T=ARC#PRD&0KARE=X02'H#@#:p,4mfa'RF&0fARGg01glRH%]CRI'DRJ#:RK'>RL&00CRME[g00DgRN#4RO#4RP#4RQ#ERR#4RS#z#yRT%zQ#yRU%UURVP:PBf8RWf7RXP5P6P7P8P4P2P3M;wXV0#;XU0#;XT0#;XS0#;XQ0#;XP0#;XRV'<XOU'<XWT'<RYP:P@PAp,3ws'RZChS01%5PR[1DTZR\#:R]'>/GFS02%UTR^AX0E6,HDR_#@=RTZP0PT&0@AS03P_CQ37p,3HR0P@PAPCp,1mR_CuP1A~_B9S04P_PB%@DR`#:Ra%lCRbPLPME[S05P_PBPWPXP5P6P7P8P4P2P3M;wXV0#;XU0#;XT0#;XS0#;XQ0#;XP0#;XRV,<VXOU,<UXWT,<TS06P_P@PAP3Ch1DT3#:,>[S07/GbART`3P0PTQ03PDCQ57^39XK^,<^S08g00TGR`P_207@ARV/6LRX16VMS09CSS0:P`P_%\XRc1mMLRd%5QRQ'^Re$02RfCjS0;P`P_%\VS0<%5ORg%5RRR'_Rh,6VRi#\S0=CSS0>'0S0?'0S0@'0S0A'0S0B'0S0CP@PAPAPCPWPFP:F3P3Q04Q0CP1Q05Q0BP@PAPAPCf<S0DPFP:F3P3Q05Q0BP1Q06Q0AP@PAPAPCf@PFP:F3P3Q06Q0AP1Q08Q0@P@PAPAPCfDPFP:F3P3Q08Q0@P1Q0:Q0?P@PAPAPCfHPFP:F3P3Q0:Q0?P1Q0;Q0>P@PAPAPCfLPFP:F3P3Q0;Q0>P=p,2HGRWPAp,2HcRjH0[&0Z?Rk/1VS0E%LP#8#5RP,_gRl,6@Rm,1iS0F20Y@ARng01hgRo'6/1iS0Gg01ibRi,6V/GnS0H'0S0I'0S0J'0P1Q0EQ0JP@PAPAPCfQPFP:F3P3Q0EQ0JP1Q0FQ0IP@PAPAPCfUPFP:F3P3Q0FQ0IP1Q0GQ0HP@PAPAPCfYPFP:F3P3Q0GQ0H20X=W%8OS0K#8Rn#E#5Rp,_gRqg01j_'6&0W?Rr'1S0L%Fn#5Rn,_gRs,1rS0M%CkS0N%ES#KRS#KRt#K#L#E#8#K#I#5,6kRu/1rS0Og01kT/1kS0P11k@S0Q%5S,6m/1uS0Rg01lQ/1kS0S'0S0T'0S0U'0S0V'0S0W'0S0X'0S0Y'0P1Q0LQ0YP@PAPAPCf^PFP:F3P3Q0LQ0YP1Q0MQ0XP@PAPAPCfbPFP:F3P3Q0MQ0XP1Q0NQ0WP@PAPAPCffPFP:F3P3Q0NQ0WP1Q0OQ0VP@PAPAPCfjPFP:F3P3Q0OQ0VP1Q0PQ0UP@PAPAPCfnPFP:F3P3Q0PQ0UP1Q0QQ0TP@PAPAPCfrPFP:F3P3Q0QQ0TP1Q0RQ0SP@PAPAPCfvS0ZPFP:F3P3Q0RQ0SPW&0V=P1&0U?S0[&0T=S0\&0S=&0R='0R?'0S0]P@PAPAPCf{PFP:F3P3Q0[Q0]P1Q0\P?P@PAPAPCp+01@PFP:F3P3Q0\P1%5NRW/13Ru%8NRm#8RS#8S0^#8S0_#5Rr,13'0Rv1T=2Rw,{2[^D0S0`1J3W1Jr3+0Qg00f0g01mT77w[^D01e=2Rx#@#:&0O2'1%Pw,Hx,x0%23Rw1T=4#]Ry,DH#:,J3'0&0NHRz&0M3R{9cHyg01nM-0LHR|37'0XJ0=k0x39\v^D0g00F3Rv&0J=g01oH37Rx1e=3%b057>^D0[g00hm11W2112r'0AcHy2=7z|%:41e=81T=8#P'H60I0[[]J^D0%UH1T=3#]%bH37^D0\x3939S0aP@PAPAPCp+01DPFP:F3\?P3Q0`Q0aP4PAPjO21{ACP1%2M11Mi'0S0bg01ohRi,aM#gS0c11LMS0d16LG,JM%2b11bo'01abi#g1>[a/1b1x0D1J3K,0wAcHI{=7z|'0XJ0=k0DPHp-0R|P3g00ZERz&0H3/63/1G&0G3$0F,GA59uRuPuPzn01100000400101011010100XtH=kHI%4mS0e#8S0f#L#E#I#I#I#5,1L'0393939S0g'0S0h'0S0iP@PAPAPCp+01IPFP:F3P3Q0bQ0iP1Q0cQ0hP@PAPAPCp+01MPFP:F3P3Q0cQ0hP1Q0dQ0gP@PAPAPCp+01QS0jPFP:F3P3Q0dQ0gPGPK20DAj11RG%5t,1GS0k'01aGRRt#gS0l'0%s\R\%2]R]%sJRJ%2KRj1`dQR1%2d%2QRu%2e[[R{1VgPRb%CgRa%2P%Cl[[R[%2gRiAWgP2VzW2RP%2l\z^2iRl1VgnRo%2n%Cs[\aRxAWgn2VzX2iRn%2s\z^2iRs1VgpR=%2p%Cq[\aRyAWgp2VzX2iRp%2q\z^2iRq1VgRRr%2RRW%Ch[\aRaAWgR2VzX2iRg%2h\z^2iRi20AGR%2G%2t\W[g00CTRW#bRt%UWRz1N02S0m&0?0Rh&0>0R>1O0R1q0NR}5M>1r>85p>1r>75p>&0<;R;1O09R~=M>}S0nCt20;><R<P3P4g00FSS0o-0Bv20C34Q0o57vdB0:092H09R9b?b@bAX10XM|XN|11R3/02/04%22[^10^M|^N|P3Q0lQ0kPGf=O4b>b;b3b4b5b6b7b8b9b:bEb=b<b0PJH0E%2LQ00P:PBp+01US0k9X0E,HDS0l#@R|#:PFPLPME[S0oP:P@PAP3ChS0pQ07/GFp+01V9X0E,HDS0q#@=RT3P0PTQ03Q0qCQ57^39XK^S0r,<^RDP`P:PXQ09CSS0sP`P:PcPfCjS0tP`P:Q0<Q0=CSRE'0S0u'0RL'0RR,0YRv'0p+01TQ0oPvp+01SPYPRp+01RPDPLP^Q0rPZQ01Q02ART|ZP0PTQ03Q0lCQ57^R|'0Q0jQ02P|p+01Pp+01OCACAH08Q0sQ0uP_P:PXQ09fzp,2WMS09P\P]PJPjP1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPig00U?R|#ZRZ#ZRL#Z#Z,Y01Y0L1Y0Z1Y0|5d05d0S0u5d0g01>7R|'v=oWtPz1N04RZ&060RL1N06RD9=L77=87=2PhP>P>P~%?O%?m5n0RmP;P>P>PmQ0^#?P;P>P>%8N#F#E#8#L#L#K#I#5RN,O0RO%?SRRP;P>P>PRP}P;A|0}m9M>OEBEBEBEBP<P9b?b@bAX10XB0XC0XF0XG01>24RR#21>48Rv/1611N611581>65,67,1N[[[[^10^B0^C0^F0^G0P3PMPkPKPGPVQ0Df>S0Df`f}O9b>b;b3b4b5b6b7b8b9b:b=b<g020bS0^/1XeF}Q0tPEP`p,1WR5P_P:PcPfQ0Zp,2MUP0PeB055c3Xu0p,3HWs1DUf#:PdPQP\P]PJPjP1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPiPtPz1N08Rd9=Z2PhP>P>PmP}P;B0e0}m9M>~EBP<P9b?b@bAX10XB0XC011R31m2v#2[^10^B0^C0P3PKPGPMQ0DO4b>b;b3b4b5b6b7b8b9b:b=b<P\P]PJPjP1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPiPtPzPLPhP0P~g00D@1O0QCf-0d>P<P9b?b@bA%CQP3b>R~b;b3b4b5b6b7b8b9b:b=b<H03-0beJ0aN90`P_P:Q0<Q0=fuQ09PVPQP\P]PJPjP1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPi1`XQR_%2X1^XQ#2\u[RXQ0u/v|=oWtPzA=L6dA=L6D7=61N079=L4?=6L7=2PhP>P>Q0f#?%4S#?5n0Q0e#4#?P;P>P>POQ0K#?RSP;P>P>PSP}P;Q0nEBEBEBP<P9b?b@bAX10XB0XC0XF0XG01>87/1411N41184%28[[[^10^B0^C0^F0^G0P3PKPGPMPkPVf?faf~O8b>b;b3b4b5b6b7b8b9b:bEb=b<P\P]PJPjP1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPiP_PXP~b;b3b4b5b6b7b8b9b:bEb=b<H031^VQR~#2RkP\P]PJPj1`VQ%2VPk\u[P1P{PbP[PPPlPoPxPnPsP=PyPpPqPrPaPgPiP_PXPtPzQ0mPhP>Q0nP;Q0_#F#F#F#F#F#L#E#K#I#5R;,O09|0}9M>OCtP<P9b?b@bAX10162;,1N\w^10P3P~Q0DO2b>b;b3b4b5b6b7b8b9b:bEbrb=b<b0Q0^Q0<'1eF}CACACACACACAQ00P:PBPMPFPIQ0lH01RB#P#@#:%lB%]B,DH#:,>GRG&00BRBE[Q0pQ07PMPFPIQ0qH01RI#l'G%PIRI#@=RT3P0PTQ03PICQ57^39XK^,<^P`P:16VGR^16VBCSP`P:%\^1mBG/^Q$02Cj;9E59Y39eP@PAPAPCQ0kPFP:F3ebXWIWpP2P3O2n2011000000121000000W0WHP2P3O2n2011000000121000000W0WoP2P3O2n2011000000121000000b0XL?WIWfP2P3O2n2001000000121000000W0P2P3O2n2001000000121000000W0WHP2P3O2n2001000000121000000b0WeWdP2P3O2n2001000000121000000W0WcP2P3O2n2001000000121000000W0WbP2P3O2n2001000000121000000W0WaP2P3O2n2001000000121000000W0W`P2P3O2n2001000000121000000W0W_P2P3O2n2001000000121000000W0W^P2P3O2n2011000000121000000b0W\W[P2P3O2n2001000000121000000W0WZP2P3O2n2001000000121000000W0WYP2P3O2n2001000000121000000b0WmWlP2P3O2n2001000000121000000W0WnP2P3O2n2001000000121000000W0WqP2P3O2n2001000000121000000W0WLP2P3O2n2011000000121000000W0WIP2P3O2n2011000000121000000W0WHP2P3O2n2011000000121000000b0WgWhW]WkWjWiWso"). Qed.

End RegDrain.

Section CFast.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (st : ckst) (lo : Z)
  (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc (set_st Σ c i CkIdle) m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hinit : ca_init Σ = true.
Hypothesis HRW : reg_wf c (pr Σ c).
Hypothesis Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σ c)))) (ca Σ c).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv asegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation mc := (MaxCount c).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

(* [comment removed for export] *)
Lemma cf_small : forall x, In x (ca Σ c) -> 0 <= x * ClassSize c / 16 < 2 ^ 31.
Proof using Hc HRW Hcl.
ltac2:(KReplay.run1 (kr_t_RT_drain_cfast ()) ["CFast"] "p'0h01Hh14__x1h24__x2h37__arithh44__ffh58__varmaph65__with74cstrh84__x3h91xh:2Hah;2_Hh<3CS1h=3CS2h>2Hxh?3W11h@2W3hA2X1hB2X2hC3_H0hD3_H1hE3_H2hF3_H3hG3_H4hH3_H5hI3_H6hJ3_H7hK7__sat12hL7__sat13hM1ihN2sti002sti011np&0p;2p;3p;1p;6p;4p;5p;7p;8g01[4k20;Tg01^<k30:Tg01DUj2oTg00__j1fTg01FLj2^Tg00gKj1WTg0000j3LTg021fj3mTg022Hj6jTg001ij23Tg01ELj1aTg00H<j15Tg00Kij18Tg00iLj1=Tg00X=j2xTg01Z9j2tTg00]cj1rTg005Gj20Tg002Ej2JTg003?j27Tg003\j2ZTg01KOj1kTg00`Xj1iTg01[kj2hTg00Ibj1gTg00lRj1eTg01\@j3dTg01\^j2cTg002ej3DTg00W:R0j21Tg01^Sj1bTg01_Qj1`Tg01`Nj1_Tg01aLk209Tg00l5j2PTg01bRk108Tg005ck107Tg006Ck106Tg006cj2OTg007Ak104Tg007_k103Tg008Jj2>Tg008mj2MTg00:;j1{Tg00;ej2zTg00<Gj2yTg00<aj2wTg00=Mj3vTg00=lj4uTg00mIj1sTg010cj4KTg011Aj3VTg022cj5qTg023Qj2FTg015Aj2TTg024:j4pTg024[j3[Tg025<j2UTg00N7j1CTg016Kj2?Tg01;7j2RTg00R6j3QTg00nHj3HTg0049j2\Tg00mgj4lTg00WUj2|Tg00XZj3}Tg00Haj1~Tg00Y>k300Tg025ek501Tg00oWk402Tg009Pj4XTg00@5j7YTg00;Ak805Tg026Qj3@Tg01:Nj3]Tg00C6R1f2R2'0f1R3f0R4'3'1p=21014p=9%54#5p=N1723/\4p=41013/14p=Sg00BXR5?D41p=I%54#5#5#5p=<P2g00@YR6g00A8R7P7g00AXR8P5P3g00ZaP4CXg00B8R9FYp=;f3R:P6P7P7P8P2P3P4L05p=6P5P3g00D@P4CXp=GP3P6P7P7P8P4P9FYp=EA@534p=AA@523=]54p=BA@5349@52p=nA@5239@5:=]54p=:p,2ΣR9p,1cR6+0;R;:0:54R<g01glR=1o96R9#fR>'^R?#WR@9244RAX95RB=L5;RCPBP3O1RD\<^95R<[PC\<Am5B;p,3HclP3P4EjPDP0%92RD132@%a6RBg00DgR;#5R<#5RC#NRE#8RF54:RG%8<RH%=;RI#=#=#=RJ#8RK'xRL72GP4f4RG#9RMf5RN/3@p,3HRW1t69P0%r9ROg01ib,0O'SRPg01ohRQ,JO#IRR17B@RS/0ORT1ZSB,3ORO%k9RUg01hg,0U'SRV1JUQ#IRQ%8C%i9R9,^5#W'7/0URU1h59RW%g=%e49d=>g01nM,c=3D,1AXM5=L59R9P=p-0P4g00ZERA%8;RX/04%b4/Z4/0B%`4#_9D56'1'1RYPYPAn01100000400101011010100XN==L=>R>%5I#=#=#N#<#<#<#<#<R=#5#<#8RY,0SRS'1RZ'1R['1R\'1R]'1R^'1R_'1R`'1Ra'1Rbf8?4BFRc?2cLP4P0PRPaf<Rc?4BFRd?2dLP4P0PTP`f@?4BFRd?2dLP4P0POP_fD?4BFRd?2dLP4P0PVP^fH?4BFRd?2dLP4P0PQP]fL?4BFRd?2dLP4P0PUP\fP?4BFRd?2dLP4P0PWP[fT?4BFRd?2dLP4P0P9PZfX?4BFRd?2dLP4P0P>PSf\?4BFRd?2dLP4p,2Hc-096%5ERE#8R6/0BRd%5E#N#<#<#8,0BRE'1Re1JB6#IRf'1P0PePffa?4BFRg?2gLP4P0PdPEfe?4BFR0?20L\fP4fhR01P@XRgPB&08?R?%9@Rhg00CTRi$07Rj&06iRk1O53&045Rl&035Rm1>56Rn1M5;Ro5;m%{7R71>51Rp=;moRqC61zm8R8P4P2g00F3Rrg00FSRs'y1w42=DrsdAv513CuRsb4b5b6X151064%93[^15P4PBPGO2b3b7P?PhPjPkP51O52P3%s5RrCKRtPlPm1M5<R<,Go,EmP71>5XRu9V5<9;moC6P8Psb4b5b6X15X2513431P2X,03[^15^25P4P@fjfdO3b3b7Dq170BR017gB'0P?Ph%8=,F5RgP51T5XP;1T51CpRv9[5I,U5A[5;v,U5%==#8,F5R=g00U?Rv#CR;#CRI#CRw,?5Rx1?5vRv%CwRw,?5Ry1F5YRz/Ay3BR{Pg1?5IRI1?5;R;P=P;P{PgP;PxPgP;PvP=Pv1F56Rg/Ay9BIyAn=v{C:C:C:C:C:C:C:g01>7R{'R=QijPkP5P51O5:P2PrCKP3PrCKR=PlPm1M5CRC9;mpR|P7PmAH5o<RoAV5Cu=H5<5;mP7PmA;mn<RnP7PmAH5<C1>5YRC5;mR<P71GoC,EmRCC6C6C6C6P8Psb4b5b6X15X25X851732Ru1P:X/72'0106:R617GNR:/0YRX13:Y[[[\D^15^25^85P4P@PBfkR:P3P2PNPcO7b3b7b0130Yfi/7BR0/\FR}#913}LP0PFP?PhPzPy1Ag;9Bx;PzPyPv%Cw,?5Rw1Agw5Bx1AvI5BvC:C:/R{=QijPkP=PlPmP|P7PmPCP7PmPnP7PmP<P7PmPqP7A;mpoC6C6C6C6C6P8Psb4b5b6X15X25X8513uYf6,7N#9\M\X\6[\D^15^25^85P4P@PBP:P3P2PNPcffO8b3b7P?PhPjPkPrPl1>5FRr,Gp,EmP8Psb4b5b6131FP4b3b7RpClP0PFPLPpP?Ph1|HK131H%9K131L[[%9HR1A}HK3VAW:%9L\A^:1PjPkPtPlPmPCP71>5H%~J60059H5r,Go,EmC6P8Psb4b5b6X15X251743/3Y17FL,3u[^15^25P4PBfmPGO3b3bKbLb7I01H02b0X;fX=EX<dP3P4O2n2001000000121000000X0eP3P4O2n2001000000121000000b0X?SXJ>P3P4O2n2001000000121000000X0ZXI9P3P4O2n2001000000121000000X0[XHWP3P4O2n2001000000121000000X0\XGUP3P4O2n2001000000121000000X0]XFQP3P4O2n2001000000121000000X0^XEVP3P4O2n2001000000121000000X0_XDOP3P4O2n2001000000121000000X0`X@TP3P4O2n2011000000121000000X0aXCRP3P4O2n2011000000121000000X0bX;PP3P4O2n2011000000121000000b0WBWAP3P4O2n2001000000121000000b0W>X95o"). Qed.

Theorem cd_fast_evt : Z.of_nat (length (ca Σ c)) = mc -> 4 * (nf + mc / 2) <= r_mfa r -> evt asegs (cd_post (recp Σ c i)) cd_ms.
Proof using HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB.
  intros Hfull Hfast.
  pose proof (cd_geo Σ HG) as (HT & HSB & TSEP & G1 & G2 & G3 & G4). unfold SHB in G1. unfold kHighShadowEnd in G4.
  pose proof (cd_slot Σ c i st HG Hc Hi) as (P1 & P2 & P3).
  pose proof (MaxCount_range c Hc) as (MC1 & MC2). pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  pose proof (dh_keep_eq c Hc) as (KP1 & KP2).
  assert (Hmc2 : 1 <= mc / 2 /\ mc / 2 <= 8 /\ mc - mc / 2 + mc / 2 = mc).
  { clear - MC1 MC2. split; [apply Z.div_le_lower_bound; lia|]. split; [apply Z.div_le_upper_bound; lia | lia]. }
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11). unfold kFaCap, kUMap, kUserCap in *.
  pose proof (dg_consts L m (proj1 HA)) as (IC & MMG & TC & PS & STS & UB).
  pose proof IC as (IC1 & IC2).
  apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  destruct IC1 as (SBC & _). cbn [cells_size csize Nat.add Z.of_nat] in SBC.
  pose proof (cd_pc Σ m c i HA Hc Hinit) as (chs & PC & CHS & Hchs & Hfch). rewrite Hfull in PC.
  destruct (fl_c8_of_stk m (cstat_alloc T) ltac:(apply (dk_stk_within m _ _ _ _ STS); unfold cstat_alloc; [lia | lia | pose proof HT as (X & _); lia]))
    as (stj & STJ).
  pose proof (cd_reg Σ m c i HA Hc) as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hfw) & STU & SHU & STSH).
  apply ri_tail_norm in RT.
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dk_auser Σ HG c Hc) as AU.
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  pose proof HT as (T1 & T2 & T3 & T4 & T5). unfold img_hull_lo, img_hull_hi in T5.
  assert (HTS : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) by (destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold kHighShadowEnd, SHB in *; lia).
  unfold cd_msD.
  eapply evt_cut; [apply (cdealloc_drain_A_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                             F fc m (l_ACEIL L) T c AB mc (ClassSize c) lo)|].
  1: exact Hc. 1: exact PC. 1: lia. 1: lia. 1: exact HT. 1: exact ST. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: clear - P1 P3 G3 G2 Hc; lia. 1: exact MI.
  intros ms1 (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk & -> & MU1 & WM1 & MI1 & PC1 & FR1 & FR2 & ST1).
  assert (Esp1 : bv_unsigned (Z_to_bv 64 (usp - 112)) = usp - 112) by (apply unsigned_lit; lia).
  assert (DJ1 : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= usp - 112 \/ usp <= a) -> disjoint_from [(P, P + 4); (usp - 112, usp)] a n).
  { intros a n Hn X1 X2. cbn [disjoint_from]. first [ clear - Hn X1 X2; repeat split; lia | split; [lia|]; split; [lia | exact I] ]. }
  assert (Hsp48 : lo <= usp - 1024) by lia.
  pose proof (rw_cells_transport asegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ RT MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RT1.
  pose proof (u32arr_transport asegs _ m m1 _ _ FL MU1 WM1 ltac:(apply DJ1; [lia | unfold pc_addr, fa, rb in *; lia | unfold fa, rb in *; lia])) as FL1.
  pose proof (u32arr_transport asegs _ m m1 _ _ CHS MU1 WM1 ltac:(apply DJ1; [lia | rewrite Hchs; cbn; lia | unfold pc_addr in *; rewrite Hchs; cbn; lia])) as CHS1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ STJ MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, cstat_alloc in *; lia)) as STJ1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ (proj1 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as IC11.
  pose proof (rw_cells_transport asegs _ m m1 _ _ (proj2 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_premapped, g_instance, pc_addr in *; lia)) as IC21.
  pose proof (rw_cells_transport asegs _ m m1 _ _ SBC MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as SBC1.
  assert (MMG1 : mm_gcells m1).
  { destruct MMG as (X1 & X2 & X3 & X4 & X5).
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X1 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X2 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X3 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X4 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    exact (rw_cells_transport asegs _ m m1 _ _ X5 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia)). }
  eapply evt_cut; [apply (rta_fast_spec (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (usp - 112)) gp (Z_to_bv 64 tpA) t0a t1a t2a (Z_to_bv 64 P)
                             (Z_to_bv 64 (cacheT T)) a6a a7a (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) s5 s6 s7 s8 s9 s10 s11
                             t3a t4a t5a t6a F fc m1 (l_ACEIL L) SB c R (usp - 104) (cstats T) (P + 16) (mc - mc / 2) (mc / 2) nf (r_mfa r)
                             (ClassSize c * Z.of_nat (length (r_st r))) (r_muser r) ws chs rand exh pad (bv_unsigned (Z_to_bv 64 nal))
                             (bv_unsigned (Z_to_bv 64 nfr)) (bv_unsigned (Z_to_bv 64 q0)) (bv_unsigned (Z_to_bv 64 q1))
                             (bv_unsigned (Z_to_bv 64 q2)) (bv_unsigned (Z_to_bv 64 q3)) lo)|].
  1: exact HSB. 1: exact Hc. 1: reflexivity. 1: lia. 1: lia. 1: lia. 1: exact Hfast. 1: exact Hws. 1: lia. 1: exact Hchs.
  1: unfold pc_addr in *; lia.
  1: pose proof (bv64_range nfr); pose proof (bv64_range q0); lia.
  1: exact (conj IC11 IC21). 1: exact MMG1. 1: exact LK1. 1: exact RC1. 1: exact RT1. 1: exact FL1. 1: exact CHS1.
  1: rewrite Esp1; exact ST1. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia. 1: rewrite Esp1; lia.
  1: rewrite Esp1; lia. 1: exact MI1.
  intros ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & MU2 & WM2 & MI2
              & LK2 & RC2 & RT2 & FL2 & ST2).
  rewrite Esp1 in ST2.
  rewrite (ret_pc_even drainhalf_retB); [| unfold drainhalf_retB; lia | reflexivity].
  assert (DJ2 : forall a n, 0 <= n -> (a + n <= R \/ R + 128 <= a) -> (a + n <= fa SB c \/ fa SB c + kFaCap <= a) ->
            (a + n <= usp - 320 \/ usp - 112 <= a) -> disjoint_from (rta_tail_W (Z_to_bv 64 (usp - 112)) SB c R nf (mc / 2)) a n).
  { intros a n Hn X1 X2 X3. unfold rta_tail_W. rewrite Esp1. cbn [disjoint_from].
    assert (4 * (nf + mc / 2) <= kFaCap) by (unfold kFaCap; lia). unfold kFaCap in *.
    first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  assert (HPT : P + 80 <= R \/ R + 128 <= P) by (unfold pc_addr, rinfo, RIS_of in *; lia).
  assert (HPF : P + 80 <= fa SB c \/ fa SB c + kFaCap <= P) by (unfold pc_addr, fa, rb, kFaCap in *; lia).
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ PC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as PC2.
  pose proof (u32arr_transport asegs _ m1 m2 _ _ CHS1 MU2 WM2 ltac:(apply DJ2; rewrite ?Hchs; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as CHS2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ STJ1 MU2 WM2 ltac:(apply DJ2; cbn; unfold cstat_alloc, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as STJ2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ SBC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold i_spacebeg, g_instance, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as SBC2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as FR12.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR2 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as FR22.
  eapply evt_mono; [apply (cdealloc_drain_B_spec sp gp (Z_to_bv 64 tpA) t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s5 s6 s7 s8 s9 s10 s11
                             t3b t4b t5b t6b F fc m2 s0 s1 s2 s3 s4 ra junk (l_ACEIL L) T SB c AB (mc - mc / 2) mc (ClassSize c) lo chs stj)|].
  1: exact Hc. 1: exact P1. 1: exact P2. 1: exact SBC2. 1: exact PC2. 1: lia. 1: lia. 1: lia. 1: exact CHS2. 1: exact Hchs. 1: exact STJ2.
  1: exact HT. 1: exact HSB. 1: exact FR12. 1: exact FR22. 1: exact ST2. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: exact MI2.
  intros ms3 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & stj' & -> & MU3 & WM3 & MI3
              & PC3 & CHS3 & _ & _ & ST3).
  unfold cd_postD. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3. split; [reflexivity|].
  assert (MU : munch (W_CD T SB c usp) m m3).
  { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [|exact MU1] | apply (munch_trans _ m1 m2 m3); eapply munch_weaken; [|exact MU2| |exact MU3]].
    - unfold sub_fp, W_CD. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia.
    - unfold sub_fp, W_CD, rta_tail_W. rewrite Esp1. cbn [outside]. intros x Hx.
      assert (4 * (nf + mc / 2) <= kFaCap) by (unfold kFaCap; lia). clear - Hx HLO2 H. unfold kFaCap in *. repeat split; lia.
    - unfold sub_fp, W_CD, cstat_alloc. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }
  assert (WM : wmono asegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
  assert (DJ3 : forall a n, 0 <= n -> (a + n <= P \/ P + 80 <= a) -> (a + n <= T + 2768 \/ T + 3168 <= a) ->
            (a + n <= usp - 160 \/ usp <= a) ->
            disjoint_from [(P, P + 4); (P + 16, P + 80); (cstat_alloc T, cstat_alloc T + 8); (usp - 160, usp)] a n).
  { intros a n Hn X1 X2 X3. cbn [disjoint_from]. unfold cstat_alloc.
    first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  assert (HTR : T + 4096 <= R \/ R + 128 <= T) by (unfold rinfo, RIS_of in *; lia).
  assert (HTF : T + 4096 <= fa SB c \/ fa SB c + kFaCap <= T) by (unfold fa, rb, kFaCap in *; lia).
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ LK2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK3.
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ RC2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC3.
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ RT2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RT3.
  pose proof (u32arr_transport asegs _ m2 m3 _ _ FL2 MU3 WM3 ltac:(apply DJ3; rewrite ?dest2_length, ?Hws; unfold pc_addr, fa, rb in *; lia)) as FL3.
  assert (Hk : (dh_keep c + Z.to_nat (mc / 2) = length (ca Σ c))%nat) by (rewrite KP2; lia).
  assert (Hfl : length (r_fl r ++ skipn (dh_keep c) (ca Σ c)) = (length (r_fl r) + Z.to_nat (mc / 2))%nat) by (rewrite length_app, length_skipn; lia).
  zhide.  
  assert (HWs : disjoint_from (W_CD T SB c usp) (shad (rb SB c + ClassSize c * Z.of_nat (length (r_st r))))
                 ((r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8)).
  { pose proof (shad_len (rb SB c + ClassSize c * Z.of_nat (length (r_st r))) (r_muser r - ClassSize c * Z.of_nat (length (r_st r)))
                  ltac:(unfold rb in *; lia) ltac:(lia) ltac:(unfold rb in *; lia)) as (SL1 & SL2).
    pose proof (fk_shad_le2 (rb SB c + ClassSize c * Z.of_nat (length (r_st r))) (r_muser r - ClassSize c * Z.of_nat (length (r_st r)))
                  ltac:(unfold rb in *; lia) ltac:(lia)) as SL3.
    pose proof (fk_shad_mono (rb SB c + ClassSize c * Z.of_nat (length (r_st r)) + (r_muser r - ClassSize c * Z.of_nat (length (r_st r))))
                  (rb SB c + kUserCap) ltac:(unfold kUserCap; lia)) as SL4.
    assert (Z.max 0 ((r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8) = (r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8)
      by (apply Z.max_r; apply Z.div_pos; lia).
    unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (RR : reg_rep SB c (cdeal_reg c (ureg r i CkIdle) (ca Σ c)) m3).
  { rewrite (cdeal_reg_full c _ (ca Σ c) (cd_full_true c (ca Σ c) Hfull)).
    assert (Edh : dh_mfa c (ureg r i CkIdle) = r_mfa r).
    { unfold dh_mfa, dh_grow, dh_nf, ureg. cbn [r_mfa r_fl].
      destruct (Z.ltb_spec (r_mfa r) (4 * (Z.of_nat (length (r_fl r)) + MaxCount c / 2))); [lia | reflexivity]. }
    rewrite Edh. refine (reg_rep_ureg' _ c (dh_reg c r (ca Σ c) (r_mfa r)) i CkIdle m3 _).
    apply (cd_reg_drain Σ m m3 c (W_CD T SB c usp) (r_mfa r) (dest2 ws chs nf (mc - mc / 2) (Z.to_nat (mc / 2))) HG Hc
             (cd_reg Σ m c i HA Hc) MU WM HWs (ca Σ c)).
    - exact LK3.
    - rewrite Hfl. replace (Z.of_nat (length (r_fl r) + Z.to_nat (mc / 2))) with (nf + mc / 2) by lia. exact RC3.
    - exists rand, exh, pad, (bv_unsigned (Z_to_bv 64 nal)), (bv_unsigned (Z_to_bv 64 nfr) + mc / 2), (bv_unsigned (Z_to_bv 64 q0)),
        (bv_unsigned (Z_to_bv 64 q1)), (bv_unsigned (Z_to_bv 64 q2)), (bv_unsigned (Z_to_bv 64 q3)). exact RT3.
    - exact FL3.
    - rewrite dest2_length. exact Hws.
    - rewrite Hfl. rewrite <- KP1. apply (dest2_prefix (r_fl r) (ca Σ c) ws chs c (dh_keep c) (Z.to_nat (mc / 2)) Hfw Hfch Hk).
      + apply (Nat2Z.inj_le). rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
      + exact cf_small. }
  assert (HP : pclass_rep T c (ca_init Σ) (cdeal_ca c i (ca Σ c)) m3).
  { rewrite Hinit. rewrite (cdeal_ca_full c i (ca Σ c) (cd_full_true c (ca Σ c) Hfull)). split.
    - rewrite length_app, firstn_length_le by lia. cbn [length]. replace (Z.of_nat (dh_keep c + 1)) with (mc - mc / 2 + 1) by lia. exact PC3.
    - exists (upd chs (Z.to_nat (mc - mc / 2)) (Z_to_bv 64 (compact_of SB c AB))). split; [exact CHS3|]. split; [rewrite upd_length; exact Hchs|].
      rewrite length_app, firstn_length_le by lia. cbn [length]. rewrite Nat.add_1_r.
      replace (Z.to_nat (mc - mc / 2)) with (dh_keep c) by (apply Nat2Z.inj; rewrite KP1, Z2Nat.id by lia; reflexivity).
      rewrite firstn_upd_snoc by lia. rewrite (cache_keep (ca Σ c) chs c (dh_keep c) Hfch ltac:(lia)), cpw_compact, map_app. reflexivity. }
  rewrite recp_set_rc, set_st_pr_same'.
  split; [exact (artc_rc Σ m m3 (W_CD T SB c usp) c i st (TZ_CD T c) lo usp HG Hc Hi (cd_TZ T c Hc) (cd_TZd T c Hc) HLO
                  (cd_cert Σ c lo sp HG Hc HLO2) HA Hdep HQB MU WM (cdeal_reg c (ureg r i CkIdle) (ca Σ c)) (cdeal_ca c i (ca Σ c))
                  ltac:(rewrite cdeal_reg_st; reflexivity) RR HP)|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
  exact (client_rc Σ m m3 (W_CD T SB c usp) c (TZ_CD T c) lo usp HG Hc (cd_TZ T c Hc) HLO ltac:(lia) (cd_cert Σ c lo sp HG Hc HLO2) Hlive MU).
Qed.

End CFast.
