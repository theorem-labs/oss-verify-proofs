(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_trans () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes3appC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC46Stdlib6ZArith:ZArith_dec8Z_le_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega7EnvRing5PExpr01C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op205I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K53B02;R_glue_defs5farunC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53B026LayoutKK_kAsanHeapLeftRedzoneMagicC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs5fdrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026LayoutDK_kAsanHeapFreeMagicC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5batchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7reg_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans9reg_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5r_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs7ri_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4r_flC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs7ri_coreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs7ri_tailC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B02;R_prim_defs6fl_arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans7dsj_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame9stk_wmonoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans9farun_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4r_stC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC47Corelib5Lists7ListDef6firstnC69OSSVerify5KrLib2K53B026RT_rep3cpwC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state4ckst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5regst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:pclass_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<pclass_avoidC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs4ahdrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloK69OSSVerify5KrLib2K53Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs5qhdr3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs3lchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@K_kAllocBegMagicC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6pchunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<pchunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs<pshadow_idleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs6lch_ifC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow7ushadowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs3ru8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs=pshadow_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame;wr_at_wmonoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans>ahdr_transportC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans=lch_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs<pshadow_quarC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans?qhdr3_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6schunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<schunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4s_mbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_quarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3s_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4smszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs4shdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5secst00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans4dsjlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib2K53B026RT_rep7sec_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans9sec_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8sec_nresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3layC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans7dsjl_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs;i_sec_mutexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_sec_nresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs<i_sec_chunksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_sec_pageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs<i_sec_sortedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs;i_sec_bylogC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs=i_gstat_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs;i_sec_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state4rtsA00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans8sec_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs8sec_nameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs6qchainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs6qbatchC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List:fold_rightC56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib2K53B026RT_rep8quar_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs7qcacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:qcache_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans:quar_avoidC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appc69OSSVerify5KrLib2K53B028RT_trans@qchain_transportC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastC69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_globalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_cmutexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7dep_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans9dep_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs4d_hsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs7hash_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6DEP_BKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs?depot_rep_frameC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state7layoutA00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B02<R_depot_defs5depot00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:fs_cls_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8fss_hintC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs7fs_hintC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fss_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs8fs_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs>fs_free_framesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<fs_cls_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs7fl_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs2NFC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K53B029R_fs_defs:frame_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs3fszC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib2K53Lib3Arr?u8arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defsHfs_free_frames_transportC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state4fsst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs2b8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6fs_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans8fs_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transDfs_cls_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7fs_busyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans7fs_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrCg_real_tls_get_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr9g_dtv_ptrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr6g_dtv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrBg_got_common_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrHg_intercept_tls_get_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr?g_got_verbosityC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrCg_current_verbosityC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr;g_tls_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr>g_got_dtls_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr:g_tls_dtlsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrGmusl_tls_get_addr_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr5g_dtvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr8dtv1_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr>g_common_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ia_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_intalloc8ia_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_intalloc3IAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_intalloc9g_ia_wordC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans7ia_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow5sh_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1Z;div_le_monoK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:shadow_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs4zrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5pg_dnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:static_accC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<shadow_avoidC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib2K53B028RT_trans=acc_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6CS_ACCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow2z8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:consts_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans<consts_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame;consts_rngsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame7in_rngsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Exists_existsC69OSSVerify5KrLib2K53Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame@consts_rep_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep5ART_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans9art_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2prC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53B026RT_rep6ART_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:ART_constsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transDconsts_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep8ART_primC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transAreg_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep8prim_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7ca_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2caC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9ART_cacheC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transDpclass_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9cache_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9ART_chunkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9chunk_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans@pchunk_transportC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans@schunk_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7ART_secC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transAsec_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep8ART_quarC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transBquar_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9budget_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7ART_depC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transAdep_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ART_fsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans@fs_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ART_iaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_trans@ia_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep:ART_shadowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_transDshadow_rep_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7ART_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep=vis_rep_wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9ART_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7dep_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8rt_countC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dsj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|].
  destruct H as [H3 H4]. split; [lia|]. exact (IH _ _ _ _ H4 H1 H2).
Qed.

Lemma dsj_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ _ (proj2 H1) H2)]. Qed.

Lemma dsj_app_inv : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n -> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a n H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH _ _ _ H2) as [X Y]. split; [split; [exact H1 | exact X]| exact Y].
Qed.

(* [comment removed for export] *)
Lemma dsj_of_outside : forall W a n, 0 < n -> Forall (fun p => fst p < snd p) W ->
  (forall x, a <= x < a + n -> outside W x) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n Hn HW H; cbn in *; [exact I|]. apply Forall_cons_iff in HW as [Hlh HW]. cbn [fst snd] in Hlh.
  split.
  - destruct (Z_le_dec (a + n) lo) as [X|X]; [left; exact X|]. destruct (Z_le_dec hi a) as [Y|Y]; [right; exact Y|].
    exfalso. destruct (Z_le_dec lo a) as [Z2|Z2].
    + destruct (H a ltac:(lia)) as [U _]. apply U. lia.
    + destruct (H lo ltac:(lia)) as [U _]. apply U. lia.
  - apply IH; [exact Hn | exact HW|]. intros x Hx. exact (proj2 (H x Hx)).
Qed.

Lemma outside_app : forall W1 W2 x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ (proj2 H1) H2)]. Qed.

Lemma bytes_at_nil_any : forall (m : mem) a, 0 <= a <= 2 ^ 64 -> bytes_at asegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* [comment removed for export] *)
Lemma farun_len : forall k, Z.of_nat (length (farun k)) = Z.max 0 k.
Proof. intros k. unfold farun. rewrite repeat_length. lia. Qed.
Lemma fdrun_len : forall k, Z.of_nat (length (fdrun k)) = Z.max 0 k.
Proof. intros k. unfold fdrun. rewrite repeat_length. lia. Qed.

Ltac cs_size := cbn [cells_size csize Nat.add length] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition reg_avoid (W : list ivl) (SB c : Z) (r : regst) : Prop :=
  let auser := ClassSize c * Z.of_nat (length (r_st r)) in
  disjoint_from W (rinfo (RIS_of SB) c) 120 /\ disjoint_from W (fa SB c) (r_mfa r)
  /\ disjoint_from W (shad (rb SB c + auser)) (Z.max 0 ((r_muser r - auser) / 8)).

Lemma reg_rep_transport : forall W SB c r (m m' : mem), reg_rep SB c r m -> munch W m m' -> wmono asegs m m' ->
  reg_avoid W SB c r -> reg_rep SB c r m'.
Proof.
  intros W SB c r m m' H MU WM (A1 & A2 & A3).
  destruct H as (L & C & (rand & exh & pad & nal & nfr & r0 & r1 & r2 & r3 & T) & (ws & F & Hws & Hpre) & S1 & B & S2).
  unfold ri_lock, ri_core, ri_tail in *.
  split; [apply (rw_cells_transport asegs W m m' _ _ L MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [apply (rw_cells_transport asegs W m m' _ _ C MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [exists rand, exh, pad, nal, nfr, r0, r1, r2, r3; apply (rw_cells_transport asegs W m m' _ _ T MU WM); cs_size;
          eapply dsj_sub; [exact A1| |]; lia|].
  split; [exists ws; split; [|split; [exact Hws | exact Hpre]]; unfold fl_arr in *;
          apply (u32arr_transport asegs W m m' _ _ F MU WM); rewrite Hws; exact A2|].
  split; [exact (stk_wmono m m' _ _ S1 WM)|].
  split; [apply (bytes_at_transport asegs W m m' _ _ B MU); rewrite farun_len; exact A3|].
  exact (stk_wmono m m' _ _ S2 WM).
Qed.

Definition pclass_avoid (W : list ivl) (T c : Z) : Prop := disjoint_from W (pc_addr T c) 80.

Lemma pclass_rep_transport : forall W T c init l (m m' : mem), pclass_rep T c init l m -> munch W m m' -> wmono asegs m m' ->
  pclass_avoid W T c -> pclass_rep T c init l m'.
Proof.
  intros W T c init l m m' (P & chs & U & Hl & Hp) MU WM A. unfold pc_cells in *.
  split; [apply (rw_cells_transport asegs W m m' _ _ P MU WM); cs_size; eapply dsj_sub; [exact A| |]; lia|].
  exists chs. split; [|split; [exact Hl | exact Hp]]. apply (u32arr_transport asegs W m m' _ _ U MU WM). rewrite Hl.
  eapply dsj_sub; [exact A| |]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pchunk_avoid (W : list ivl) (SB c : Z) (i : nat) (st : ckst) : Prop :=
  let AB := p_abeg SB c i in let S := ClassSize c in
  match st with
  | CkIdle | CkBatch => disjoint_from W (shad AB) (Z.max 0 (S / 8))
  | CkAlloc n =>
      disjoint_from W (AB + rz_size n - 16) 16 /\ (16 < rz_size n -> disjoint_from W AB 16)
      /\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ ushadow n)))
      /\ disjoint_from W (shad (AB + rz_size n + ru8 n)) (Z.max 0 ((S - rz_size n - ru8 n) / 8))
  | CkQuar n =>
      disjoint_from W (AB + rz_size n - 16) 24 /\ (16 < rz_size n -> disjoint_from W AB 16)
      /\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ fdrun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8))))
  end.

Lemma ahdr_transport : forall W (m m' : mem) M n, ahdr m M n -> munch W m m' -> wmono asegs m m' -> disjoint_from W M 16 -> ahdr m' M n.
Proof.
  intros W m m' M n (b1 & ctx & Hb & H) MU WM A. exists b1, ctx. split; [exact Hb|].
  apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma qhdr3_transport : forall W (m m' : mem) M n, qhdr3 m M n -> munch W m m' -> wmono asegs m m' -> disjoint_from W M 24 -> qhdr3 m' M n.
Proof.
  intros W m m' M n (b1 & ctx & fid & Hb & H) MU WM A. exists b1, ctx, fid. split; [exact Hb|].
  apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma lch_transport : forall W (m m' : mem) AB M, lch m AB M -> munch W m m' -> wmono asegs m m' -> disjoint_from W AB 16 -> lch m' AB M.
Proof. intros W m m' AB M H MU WM A. apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A. Qed.

Lemma pchunk_transport : forall W SB c i st (m m' : mem), pchunk SB c i st m -> munch W m m' -> wmono asegs m m' ->
  pchunk_avoid W SB c i st -> pchunk SB c i st m'.
Proof.
  intros W SB c i st m m' H MU WM A. unfold pchunk, pchunk_avoid in *. destruct st as [|n|n|].
  - destruct H as [S B]. split; [exact (stk_wmono m m' _ _ S WM)|]. unfold pshadow_idle in *.
    apply (bytes_at_transport asegs W m m' _ _ B MU). rewrite farun_len. exact A.
  - destruct H as (Wr & Hh & Hl & B1 & B2). destruct A as (A1 & A2 & A3 & A4).
    split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (ahdr_transport W m m' _ _ Hh MU WM A1)|].
    split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
    split; [apply (bytes_at_transport asegs W m m' _ _ B1 MU); exact A3|].
    apply (bytes_at_transport asegs W m m' _ _ B2 MU). rewrite farun_len. exact A4.
  - destruct H as (Wr & Hh & Hl & B1). destruct A as (A1 & A2 & A3).
    split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (qhdr3_transport W m m' _ _ Hh MU WM A1)|].
    split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
    unfold pshadow_quar in *. apply (bytes_at_transport asegs W m m' _ _ B1 MU). exact A3.
  - unfold pshadow_idle in *. apply (bytes_at_transport asegs W m m' _ _ H MU). rewrite farun_len. exact A.
Qed.

(* [comment removed for export] *)
Definition schunk_avoid (W : list ivl) (s : secst) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  disjoint_from W mb 32 /\ disjoint_from W AB 16 /\ disjoint_from W M (if s_quar s then 24 else 16)
  /\ disjoint_from W (shad mb) (Z.max 0 ((4096 + 2048) / 8))
  /\ disjoint_from W (shad (AB + 2048)) (Z.of_nat (length (if s_quar s then fdrun (ru8 n / 8) else ushadow n)))
  /\ disjoint_from W (shad (AB + 2048 + ru8 n)) (Z.max 0 ((msz - 4096 - 2048 - ru8 n) / 8)).

Lemma schunk_transport : forall W k s (m m' : mem), schunk k s m -> munch W m m' -> wmono asegs m m' ->
  schunk_avoid W s -> schunk k s m'.
Proof.
  intros W k s m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6). unfold schunk in *.
  destruct H as (Hs & Wr & Hl & Hh & S & B1 & B2 & B3).
  split; [unfold shdr in *; apply (rw_cells_transport asegs W m m' _ _ Hs MU WM); cs_size; exact A1|].
  split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (lch_transport W m m' _ _ Hl MU WM A2)|].
  split; [destruct (s_quar s); [exact (qhdr3_transport W m m' _ _ Hh MU WM A3) | exact (ahdr_transport W m m' _ _ Hh MU WM A3)]|].
  split; [exact (stk_wmono m m' _ _ S WM)|].
  split; [apply (bytes_at_transport asegs W m m' _ _ B1 MU); rewrite farun_len; exact A4|].
  split; [apply (bytes_at_transport asegs W m m' _ _ B2 MU); exact A5|].
  apply (bytes_at_transport asegs W m m' _ _ B3 MU). rewrite farun_len. exact A6.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dsjl (W : list ivl) (l : list (Z * Z)) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r)) l.
Lemma dsjl_in : forall W l a n, dsjl W l -> In (a, n) l -> disjoint_from W a n.
Proof. intros W l a n H Hin. exact (proj1 (Forall_forall _ _) H (a, n) Hin). Qed.
Ltac in_lit := repeat (first [ left; reflexivity | right ]).
(* [comment removed for export] *)
Ltac dsj_lit H := match goal with |- disjoint_from ?W ?a ?n => eapply (dsj_sub W a _ a n); [eapply (dsjl_in _ _ a _ H); in_lit | lia | lia] end.
Ltac rwc_lit H := eapply rw_cells_transport; [eassumption | eassumption | eassumption |]; cs_size; dsj_lit H.
(* [comment removed for export] *)
Ltac rwc_litX H X := eapply (rw_cells_transport asegs _ _ _ _ _ X); [eassumption | eassumption |]; cs_size; dsj_lit H.

(* [comment removed for export] *)
Definition sec_lits : list (Z * Z) :=
  [(i_sec_chunks, 8); (i_sec_nres, 16); (i_sec_mutex, 1); (i_sec_mutex + 1, 3); (i_sec_page, 8); (i_sec_range, 8); (i_sec_sorted, 40);
   (i_sec_bylog, 512); (i_gstat_alloc, 16); (0x10ab48, 8); (0x10ca78, 8)].
Definition sec_avoid (W : list ivl) (Σ : rtsA) : Prop := dsjl W sec_lits /\ disjoint_from W (l_PAB (lay Σ)) (8 * sec_nres Σ).

Lemma sec_rep_transport : forall W Σ (m m' : mem), sec_rep Σ m -> munch W m m' -> wmono asegs m m' -> sec_avoid W Σ -> sec_rep Σ m'.
Proof.
  intros W Σ m m' H MU WM (A & AP). unfold sec_rep, sec_core, sec_pad, sec_page, sec_range, sec_junk, name_cells in *.
  destruct H as ((C1 & C2 & C3) & P & (ws & U & Hl & Hf) & G & R & ((b & j & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)) & N1 & N2).
  split; [split; [rwc_lit A | split; [rwc_lit A | rwc_lit A]]|].
  split; [rwc_lit A|].
  split; [exists ws; split; [|split; [exact Hl | exact Hf]]; apply (u64arr_transport asegs W m m' _ _ U MU WM); rewrite Hl; exact AP|].
  split; [rwc_lit A|]. split; [rwc_lit A|].
  split; [split; [exists b, j, w1, w2, w3, w4; rwc_lit A | split; [exists bl; split; [exact Hbl|] | exists ga, gm; rwc_lit A]]|].
  - apply (u64arr_transport asegs W m m' _ _ J2 MU WM). rewrite Hbl. dsj_lit A.
  - split; rwc_lit A.
Qed.

(* [comment removed for export] *)
Definition quar_avoid (W : list ivl) (Σ : rtsA) : Prop :=
  disjoint_from W (qcacheT (l_T (lay Σ))) 32 /\ dsjl W [(i_q_global, 32); (i_q_cmutex, 4)]
  /\ Forall (fun b => disjoint_from W (fst b) 8192) (ql Σ ++ qg Σ).

Lemma qchain_transport : forall W (m m' : mem) bs, qchain m bs -> munch W m m' -> wmono asegs m m' ->
  Forall (fun b => disjoint_from W (fst b) 8192) bs -> qchain m' bs.
Proof.
  intros W m m' bs. induction bs as [|[b ents] bs IH]; intros H MU WM A; [exact I|].
  apply Forall_cons_iff in A as [A1 A2]. cbn [fst] in A1. destruct H as [(H1 & (ws & U & Hl & Hf) & Hn) H2].
  split; [|exact (IH H2 MU WM A2)]. split; [apply (rw_cells_transport asegs W m m' _ _ H1 MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [|exact Hn]. exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64arr_transport asegs W m m' _ _ U MU WM).
  rewrite Hl. eapply dsj_sub; [exact A1| |]; lia.
Qed.

Lemma quar_rep_transport : forall W Σ (m m' : mem), quar_rep Σ m -> munch W m m' -> wmono asegs m m' -> quar_avoid W Σ -> quar_rep Σ m'.
Proof.
  intros W Σ m m' ((Q1 & C1) & (Q2 & C2) & X) MU WM (A1 & A2 & A3). apply Forall_app in A3 as [A3 A4].
  split; [split; [apply (rw_cells_transport asegs W m m' _ _ Q1 MU WM); cs_size; exact A1 | exact (qchain_transport W m m' _ C1 MU WM A3)]|].
  split; [split; [rwc_lit A2 | exact (qchain_transport W m m' _ C2 MU WM A4)]|]. rwc_lit A2.
Qed.

(* [comment removed for export] *)
Definition dep_avoid (W : list ivl) (L : layoutA) : Prop :=
  dsjl W [(0x1fbc58, 0x5fbc58 + 4 - 0x1fbc58); (0x5fbc68, 8); (0x1ebc48, 8); (0x1ebc58, 0x1ebc60 + 4 - 0x1ebc58)]
  /\ disjoint_from W (l_DNB L) (2 ^ 20) /\ disjoint_from W (l_SSB L) (2 ^ 23).

Lemma dep_rep_transport : forall W L d (m m' : mem), dep_rep L d m -> depot_ok d (l_DNB L) (l_SSB L) (l_ACEIL L) ->
  munch W m m' -> wmono asegs m m' -> dep_avoid W L -> dep_rep L d m'.
Proof.
  intros W L d m m' H OK MU WM (A & A5 & A6). unfold dep_rep in *.
  apply (depot_rep_frame d _ _ _ _ W m m' H OK MU WM); [exact (dsjl_in _ _ 0x1fbc58 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x5fbc68 _ A ltac:(in_lit)) | exact A5
    | exact (dsjl_in _ _ 0x1ebc48 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x1ebc58 _ A ltac:(in_lit)) | exact A6].
Qed.

(* [comment removed for export] *)
Definition fs_lits : list (Z * Z) :=
  [(tpA, 8); (0x11aa58, 1); (g_real_tls_get_addr, 8); (g_dtv_ptr, 8); (g_dtv1, 8); (g_got_common_flags, 8);
   (g_intercept_tls_get_addr, 1); (g_got_verbosity, 8); (g_current_verbosity, 4); (g_tls_index, 16); (g_got_dtls_off, 8);
   (g_tls_dtls, 8)].
Definition fs_cls_avoid (W : list ivl) (FSB c : Z) (f : fsst) : Prop :=
  disjoint_from W (FSB + 8 * c) 8 /\ disjoint_from W (fl_base FSB c) (Z.of_nat (length (fss_flags f)))
  /\ (forall p, 0 <= p < NF c -> nth (Z.to_nat p) (fss_flags f) 1 = 0 ->
        disjoint_from W (frame_addr FSB c p) (fsz c) /\ disjoint_from W (shad (frame_addr FSB c p)) (fsz c / 8)).
Definition fs_avoid (W : list ivl) (Σ : rtsA) : Prop :=
  let L := lay Σ in
  disjoint_from W (l_FSB L + 0x58) 9 /\ fs_cls_avoid W (l_FSB L) 0 (fs0 Σ) /\ fs_cls_avoid W (l_FSB L) 1 (fs2 Σ)
  /\ (fs_cls_avoid W (l_FSB L) 6 (fs4 Σ) /\ fs_cls_avoid W (l_FSB L) 2 (fs1 Σ)) /\ dsjl W fs_lits /\ disjoint_from W (l_DTV L + 24) 8 /\ disjoint_from W (l_T L + 48) 16
  /\ Forall (fun fk => disjoint_from W (fst fk + fs_size (snd fk) - 8) 8) (frames Σ).

Lemma fs_cls_rep_transport : forall W FSB c f (m m' : mem), fs_cls_rep FSB c f m -> munch W m m' -> wmono asegs m m' ->
  fs_cls_avoid W FSB c f -> fs_cls_rep FSB c f m'.
Proof.
  intros W FSB c f m m' (H1 & H2 & H3) MU WM (A1 & A2 & A3). unfold fs_hint, fs_flags in *.
  split; [apply (rw_cells_transport asegs W m m' _ _ H1 MU WM); cs_size; exact A1|].
  split; [apply (u8arr_transport asegs W m m' _ _ H2 MU WM); rewrite length_map; exact A2|].
  exact (fs_free_frames_transport FSB c m m' _ W H3 MU WM A3).
Qed.

Lemma fs_rep_transport : forall W Σ (m m' : mem), fs_rep Σ m -> munch W m m' -> wmono asegs m m' -> fs_avoid W Σ -> fs_rep Σ m'.
Proof.
  intros W Σ m m' H MU WM (A1 & A2 & A3 & (A4 & A4b) & A5 & A6 & A7 & A8). unfold fs_rep, fs_const, tga_cells, dtls_cells, ttls_cells in *.
  destruct H as (F1 & F2 & F3 & (F4 & F4b) & T & (dtvbeg & Hdb & (G1 & G2 & G3 & G4 & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8))) & (tb & te & TT) & FB).
  split; [apply (rw_cells_transport asegs W m m' _ _ F1 MU WM); cs_size; exact A1|].
  split; [exact (fs_cls_rep_transport W _ _ _ m m' F2 MU WM A2)|].
  split; [exact (fs_cls_rep_transport W _ _ _ m m' F3 MU WM A3)|].
  split; [split; [exact (fs_cls_rep_transport W _ _ _ m m' F4 MU WM A4) | exact (fs_cls_rep_transport W _ _ _ m m' F4b MU WM A4b)]|].
  split; [rwc_lit A5|].
  split; [exists dtvbeg; split; [exact Hdb|]|split; [exists tb, te; apply (rw_cells_transport asegs W m m' _ _ TT MU WM); cs_size; exact A7|]].
  2: { unfold fs_busy in *. apply Forall_forall. intros fk Hfk. destruct (proj1 (Forall_forall _ _) FB fk Hfk) as (p & Hp & W1 & W2 & Cw).
       exists p. split; [exact Hp|]. split; [exact (wr_at_wmono m m' _ _ W1 WM)|]. split; [exact (wr_at_wmono m m' _ _ W2 WM)|].
       apply (rw_cells_transport asegs W m m' _ _ Cw MU WM). cs_size. exact (proj1 (Forall_forall _ _) A8 fk Hfk). }
  split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
  split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
  split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
  apply (rw_cells_transport asegs W m m' _ _ D8 MU WM); cs_size; exact A6.
Qed.

(* [comment removed for export] *)
Definition ia_lits : list (Z * Z) :=
  [(g_ia_word, 4); (IAP, 1); (IAP + 8, 0x40000); (IAP + 0x40040, 0xd80); (IAP + 0x40dc0, 0x40248); (IAP + 0x81008, 40);
   (0x10ab40, 8); (0x1a9820, 8)].

Lemma ia_rep_transport : forall W Σ (m m' : mem), ia_rep Σ m -> munch W m m' -> wmono asegs m m' -> dsjl W ia_lits -> ia_rep Σ m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_trans ()) [] "p'0h02bsh11jh24__x1h31Hh47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:5cstr1h;1xi001xh<1bi011bh=1zh>2H0h?2W1h@4__p1hA4__p2hB4__x2hC1mhD1nhE1AhF2B1hG2B2hH2B3hI1GhJ1JhK2J4hL2L1hM2L2hN2L3hO3MAPhP2MUhQ1PhR1WhS2WMhT2b1hU2b2hV2b3hW2j4hX2m'hY1yhZ2z0h[2Σp%0p&0p;1p;2p;3p;4p;6p;8p;:p;7p;<p;Bg000nj1lTg00;>j19Tg00Vdj1rTg00WBk105Tg00Wek10STg03TWj2kTg03UPj2{Tg0127j3xTg012nj3uTg029lj2yTg00XGj1_Tg00h[j2aTg01Ajk106Tg003Fj1nTg00g<R0k10PTg00iAk30MTg01Bbj1zTg00YBj2HTg00YbR1j18Tg00<Fj1FTg005[j1LTg01CZj2|Tg01Q8k102Tg005@R2j25Tg00HIk20TTg004Fj4mTg003fj3QTg02@Cj6fTg0088k204Tg009Rk10RTg00:0k10QTg00:[k203Tg00=Mk20OTg00=oj2`Tg00>Ik20NTg00?5j3TTg00?Ok30LTg00?nk40KTg002MR3j21Tg002iR4j26Tg00^nk10JTg00_Lk40ITg00a7j4RTg01>nj8DTg01?jj1WTg001Nj3ETg01@fl:VTg00g\j2wTg00h9k20FTg00NRk20ETg004fj2vTg0094k10CTg008Vk40BTg00A]j4sTg00R\j2hTg00Blk70@Tg00<kk10?Tg00CPk80>Tg00i`k30=Tg00jBj6bTg034>l:cTg00@`j4@Tg01<CR5j2:Tg00bIj1iTg01DRj4UTg03VOj4qTg01_4j4KTg02:ej3pTg00Qhk30;Tg00BHj7~Tg00bnm<00Tg00cSlBjTg00_om<0:Tg00;ck301Tg00RBk309Tg00^Jk608Tg00T;k707Tf0R6#9#9p=Bg01RkR7f1R8;Q6p=Mg03WDR9/66p=Y%96#9#9#_p=Jg00e:R:f2R;P8P6Cqp=?P:P;g03X>R<P8CK/56p=}P:P8P9P6CKp=7g00D4R=?T86p==f3R>P:P;P8P6Cq'5p=0%96#Fp=C%96#9#9#9p=g%F6#9p=N%L6#Lp>0<%L6#L#L#Lp=IP:P;P8P6CKp=3P:f5R?f4R@P>CKP:P;P8P6CK'5p=A1:@>1:;8/56'5p=2P:P@P<P>CK1:;8/56'5p=>P:P8P<P6CKp=\f7RAf6RB':P:P?P@P>CKP:P;P8P6CK'5'5p=GP=P=P8P6Cmp=ZATAB?Ap@>;1`8640;p=PP;g00E9RCg00EXRDPDg00F8REP=P8g00DRP6Csg00FXRFF~p=<1`=6p=;g00d9RGP=P=P=P1P1P?P@P>P;P8P6N<00p=]P=P=P=P=P=P=P4PAPBP?P4P@P<P<P>P;P8P6MBjp>0HP=P=P3PAP3PBP?P@P>P;P8P6N<0:p=X1h=6:01=8p=OATB?@Ap>;8<096p=4P@g03Y>R3P>P;P8P6Efp=S1h=6p=dB01=86p=^P=PGP=P=P0P@P1P>g00k]P;P8P6N<00p>0GP=P=P=P=P=P=P4P6P8P;P4P>P@P?PBPAf8S00f9R1MBjp=eP8PCPDPDPEP6J08p=tP8PCPDPDPEP6PFF~p>0AP;PCPDPDPEP8P6K07p=o1:;8/56p=[P=P=P=P=P=P=P4PAPBP?P4P@P9P9P>P;P8P6MBjp>0Dg00G8#lg02LFg00J`R4#9S01#9RF#9R0#9#BRH#rRI$05%r0RJ$05RK$0S[S02Q021k;8P5g00KERL1{6>X<LAx?>;Au:@>1yA31kA?[[[P61{6?Q00?xB?Au:ABf:RM/y3PLPLp-0RNP6%_4RO,aI$06%n7R7'MRP%_0R0#YRQg00LERR,aJS03%BHRJ#9#BRS#9RT#9#B#JRU$0PRV60MKRW5?15}1S04P11aIR$06/M7RXPK%z6/M7RY,7MX1K%lKRZ1HK6#8R[/=UR\PMPQP6C0X0ZPZ%F4#C#F#g#JR],=[R^PM%NS#B#JS05#YRSP6C0X0ZPZ%FJ#B#N#C#JRJ,=[R[PM%FHRH#F#C#F#N#B#JS06#YR_P6C0X0ZPZ%9H#B#g#C#JS07#YRHg00IU#LS08#L$0<S09#IS0:#I#I#I#I#I#I#I#IR`/|6/M7Ra53MX1ZP1%94#B#C#C#C#C#N#N#B#JRb%N4#N#N#C#F#g#C#B#JRc,aI$02/M7RdP1Pc%_T,aI$02/M7RIEAD2D2D>S0;n0110100020001X<LP@PLPLPNP61\MPRTA?MQWR1'5Re1\MXS0<PKf;Rf/7YX1KPZP\PfPQP6C0X0ZPZP^PfPSP6C0X0ZPZP[PfP_P6C0X0ZPZA3fHaX1ZPMPbPdPMPcPIGGD2D2S0='5S0>n0110100020001PLPNP8PeQ0>n0110100020001]3P@Q04P2PTP1PeP6f<S0?/\Pf=Re??QWR11\ePP1P:f@R1f>RTPeP<PPP8PAPBP1P<%_FRFP<Q09#8S0@P1P3P<PFP?20T==RfP=P=P<PFCmRgPgPfPgP=P=P9POCmRh1ZQURi1ZS]Rj1Z_JRkQ01#F#JRl,ZHRm1Zb0Rn1Zc0Ro%nfS0A5QfS0B5QfS0C5QfS0D5QfRp5QfRq5QfRr5QfRsPfPgGPS0EEfg00HiRt#nRu%ltRt204=8Rv&0R=Rw&0Q=Rx203=4R4;<420OxERyP6P;g00KeRz,`L20N6;=TLzdB0L=R8H0KRzb5b6b7X2=S0F1166^2=S0GP6P<O1S0Hb4S0IQ0@,6<R{16<FR|'1S0J11||S0KP6X;=R}1186$0JXY=X;=R~P{P|P}P}P}P=P=g00fX1686H0I#;XC=XD=R{1`=<Q0@PFP}P}%86S0L#;X;GS0MQ09PF%;FE]L0HP|P|%;|GXS09PuPtPvPw1O4FR|=<x|PyPzb5b6b7X2=166FR|/1|^2=Q0Hb4S0HCRGD%WP#89E1<eM:VP:P1PTPePQPWP6PAPBPGPVfAS0NQ0L7EQXDGP1PQPUPQ%8VRGP1PQPUP?PfPgPiPfPiPsPfPhPiPfPiPrPfPiPiPfPiPqPfPiGPF4F4S0LDSPuPtPvPw%d0S0O,^4R1=<x1PyPzb5b6b7X2=1660S0PQ0P'1^2=P6P9O1RAb4S0Q16QGS0R16QURP'11wRUR|,6QS0S/1PP}P~Q0RQ0SP}P}P}P{PQPQ%;QPGP|P}P}Q0MPVP|P}1wR6X;=PUPU%;UI0GE]M:ePPPP%;PGX20FRU20ERURP1=|U'511URRGAT=|R'5'vP|P=PuPtP=204=;P8&0C=S0SH0BPwPxPCPDPDPEPxPCPDPDPE1tx@P=Q01-03=REg00lJ%dURCCs-0Ax5ox1h=R9<xC1tx?5oxK0@&0?D1^1E1^1CRC5<xL0>PyPzb5b6b7X2=XB=X@NXAN1=8U,5;15G>'v1680RG/6;16GU'1[^2=^B=^@N^ANP6AT=8RPPP8P9P;O5b4bZb>CRGD1HKWQ03>0=KVEbM:cC@WOW?P8P6O2n2001000000121000000W3Q0;P2Q0<Q0=Q0>P6Q0?/\XPK17TYX1KPZP\PTPQP6C0X0ZPZP^PTPSP6C0X0ZPZP[PTP_P6C0X0ZPZA3THaX1ZPePbPdPePcPIGGD2D2P2f?RV/7YX1K,:KRWPZP\PVPQP6C0X0ZPZP^PVPSP6C0X0ZPZP[PVP_P6C0X0ZPZA3VHaX1ZPTPbPdPTPcPIEAD2D2RV15WV9}TXP6Q0N/7YX1K,:KP5PKfBRV/7YX1KPZP\fCRWPQP6C0X0ZPZP^PWPSP6C0X0ZPZP[PWP_P6C0X0ZPZA3WHaX1ZPVPbPdPVPcPIEAD2D2R;PVPXPK17WYX1KP;D>[P6fD/7YPZP\fFR;PQP6C0X0ZPZP^P;PSP6C0X0ZPZP[P;P_P6C0X0ZPZA3;HaX1ZfERWPbPdPWPcPIEAD2D2P2P\fGRWPQP6C0X0Z,:ZRPPZP^PWPSP6C0X0ZPZP[PWP_P6C0X0ZPZA3WHaX1ZP;PbPdP;PcPIGGD2RNP;PXPK17WYX1K15PND>P6P\fIS0NPQP6C0X0Z,:ZP5PZP\fJRNPQP6C0X0ZPZP^fKRPPSP6C0X0ZPZP[PPP_P6C0X0ZPZA3PHaX1ZPNPbPdPNPcPIGGD2RWPNPXPK17PYX1KP\PPPQP6C0X0Z=[ZWD>[P6P\fLPQP6C0P21HK8#8RW/=UfM??Q8PZP^fORPPSP6C0X0ZPZP[PPP_P6C0X0ZPZA3PHaX1ZfNR;PbPdP;PcPIGGD2RGP;PXPK17PYX1KP\PPPQP6C0X0Z=[ZGD>[P61HK>#8RG/=UfP??Q@PZP^fRR1PSP6C0X0ZPZP[P1P_P6C0X0ZPZA31HaX1ZfQREPbPdPEPcPIGGD2P2P^fSREPSP6C0X0Z,:ZRDPZP[PEP_P6C0X0ZPZA3EHaX1ZP1PbPdP1PcPIEAD2R|P1PXPK17EYX1KP\PEPQP6C0X0Z15D|5[ZD>P6P^fUS0?PSP6C0X0Z,:ZP5PZP^fVR|PSP6C0X0ZPZP[fWRDP_P6C0X0ZPZA3DHaX1ZP|PbPdP|PcPIEAD2REP|PXPK17DYX1KPZP\PDPQP6C0X0ZPZP^PDPSP6C0X0ZPED2D>[P6P^fXPSP6C0P21=W]fY??S8PZP[f[REP_P6C0X0ZPZA3EHaX1ZfZRDPbPdPDPcPIEAD2R1PDPXPK17EYX1KPZP\PEPQP6C0X0ZPZP^PEPSP6C0X0ZP1D2D>[P61=G]f\S0>??S@PZP[f^R1P_P6C0X0ZPZA31HaX1Zf]REPbPdPEPcPIEAD2P2P[f_REP_P6C0X0Z,:ZS0=PZA3EHaX1ZP1PbPdP1PcPIGGS0<P1PXPK17EYX1KPZP\PEPQP6C0X0ZPZP^PEPSP6C0X0ZQ0=Q0<'5D2D>P6P[faS0<P_P6C0X0Z,:ZP5PZP[fbREP_P6C0X0ZPZfcR1?3HaX1ZPEPbPdPEPcPIGGS0=PEPXPK171YX1KPZP\P1PQP6C0X0ZPZP^P1PSP6C0X0ZP[P1P_P6C0X0ZQ0=5[ZD2D>[P6P[fdP_P6C0P21=WJfe??_8PZfgRW?3HaX1ZffR1PbPdP1PcPIGGS0=P1PXPK17WYX1KPZP\PWPQP6C0X0ZPZP^PWPSP6C0X0ZP[PWP_P6C0X0ZQ0=5[ZD2D>[P61=GJfh??_@PZfjR@?3HaX1ZfiS0=PbPdQ0=PcPIGGP2fkRG?3HaX1Z,:ZRWP@PbPdP@PcPIEAR1P@PXPK17GYX1KPZP\PGPQP6C0X0ZPZP^PGPSP6C0X0ZP[PGP_P6C0X0Z15W15[ZD2D>P6fmR1?3HaX1Z,:ZP5PZfnR5?3HaX1ZP5PbPdP5PcPIEARWP5PXPKfoRG/7YX1KPZP\PGPQP6C0X0ZPZP^PGPSP6C0X0ZPZP[PGP_P6C0X0ZPZA3GHaX1ZPWD2D2D>[P6fp?3HafqRWPbPdPWPcPIEAP2frR2?3bdRWA32cIR@P2PXPKfsR2/7YX1KPZP\P2PQP6C0X0ZPZP^P2PSP6C0X0ZPZP[P2P_P6C0X0ZPZA32HaX1Z15W@D2D2D>P6ft?3bdfuR@?3cIRW1\@XfvR2/7YX1KS04,:KS03P\P2PQP6C0X0ZS01,:ZS0RP^P2PSP6C0X0ZS0T,:ZS0UP[P2P_P6C0X0ZS0V,:ZS0WA32HaX1ZS0X,:ZS0YA3@bdS0Z/5WS0['5S0\'5S0]'5S0^'5S0_'5P:fxRaP2P@P<PXQ0=PGP5PaP<PFP<Q0@PaP3P<PFP1Q0EEf1HKVRF#iR[%8FRF,1RR^1HKPRP#iR\%8P,1RRPQ0>,HKS0>#iRYQ0>#8,1RRRQ0Ib:b9b8Q0JQ0KQ09P[P^P\PPPYPRQ0Hb:b9b8CRGD%WX#89Ea<eM:VQ03Q0_PKQ04PEP:PaP2P@P9%zE/M7REQ0<PGP5PaP9POP9Q08#8R<PaP3P9POP1PfPgPhPfPhPsPfPhPhPfPhPrPfPhGPF4EfP[P^P\PPPYPRQ0FQ0GPAb4b:b9b8%Y<R3%YORX'111XXP}P~P3PXP}P}P}P{1`=9P<POP}P}Q0MQ08PO%;OE]L0DPXPX%;XGXP[P^P\PPPYPRPuPtPvPw1O4ORX=<xXPyPzb5b6b7X2=166ORO/1O^2=PAb4b:b9b8CRGD%WE#89Ea9eM:VCUQ0RQ0^PZQ01PD1HKD#8R9/=UA?@QDP|P:PaP2P@PQPDQ0?PGP5P=PUfyRD?EQ6X==PaPQPUPQPUPaPQPUP1Q0LDSP[P^P\PPPYPRQ0Qb:b9b8P[P^P\PPPYPRPuPtPvPwA<xCCPyPzb5b6b7X2=Q0P/6URU/1U^2=PAb4b:b9b8GDP9P|EbM:cC@CUQ0UQ0]PZQ0TP;1HK;#8R|/=]A?@S;PNP:PaP2P@PSP;Q0NPGP5P=P]AEDS6X==PaPSP]PSP]PaPSP]P1PfPgPjPfPjPsPfPhPjPfPjPrPfPiPjPfPjPqPfPjPjPfPjPpPfPjGPF4F4F4DSP[P^P\PPPYPRPuPtPvPwQ05,O4RS=<xSPyPzb5b6b7X2=Q05,66R;/1;^2=PAb4b:b9b8P[P^P\PPPYPRPuPtPvPw1OS]RS=<xSPyPzb5b6b7X2=16;]R;/1;^2=PAb4b:b9b8GDP|PNEbM:cC@CUQ0WQ0\PZQ0VPV1=FJA?@_VPTP:PaP2P@P_PVPePGP5P=PJAED_6X==PaP_PJP_PJPaP_PJP1PfPgPkPfPkPsPfPhPkPfPkPrPfPiPkPfPkPqPfPjPkPfPkPpPfPkPkPfPkQ0DPfPkGPF4F4F4F4DSP[P^P\PPPYPRPuPtPvPwQ06,O4R_=<x_PyPzb5b6b7X2=Q06,66RD/1D^2=PAb4b:b9b8P[P^P\PPPYPRPuPtPvPw1O_JR_=<x_PyPzb5b6b7X2=16DJRD/1D^2=PAb4b:b9b8GDPFPTEbM:cC@CUQ0YQ0[PZQ0XPBP:PaP2P@PH1|`B/M7R7P?PGP5PaPHPlPH%8`R?PaPHPlP1PfPgPmPfPmPsPfPhPmPfPmPrPfPiPmPfPmPqPfPjPmPfPmPpPfPkPmPfPmQ0DPfPmPmPfPmQ0CPfPmGPF4F4F4F4F4DSP[P^P\PPPYPRPuPtPvPwQ07,O4R4=<x4PyPzb5b6b7X2=Q07,66RB/1B^2=PAb4b:b9b816H?RT16HlRF'111FFP}P~PTPFP}P}P}P{PHPH%;HP?PlP}P}Q0MP`Pl%;lE]M:ePFPF%;FGXP[P^P\PPPYPRPuPtPvPw1O4lR4=<x4PyPzb5b6b7X2=16BlRB/1B^2=PAb4b:b9b8CRGD%W7#89EaHeM:VCUQ0ZPWP:PaP2P@PbPdP8PGP5PaPbP0PbQ0:#8RWPaPbP0P1PfPgPnPfPnPsPfPhPnPfPnPrPfPiPnPfPnPqPfPjPnPfPnPpPfPkPnPfPnQ0DPfPmPnPfPnQ0CPfPnPnPfPnQ0BPfPnGPF4F4F4F4F4F4DSP[P^P\PPPYPRPuPtQ0SPw%dbRH=<xHPyPzb5b6b711bbP6b4b:b9b816bWR716b0RA'111AAR=P}P~P7PAP}P}P}P{PbPb%;bPWP0P}P}Q0MQ0:P0%;0E]R7M:ePAPA%;AGXP[P^P\PPPYPRPuPtQ0SPwQ0O,^HRH=<xHPyPzb5b6b7P=P6b4b:b9b8CRGD%Wd#89EabeM:VP:PaP2P@PcPIP6PGP5PaPcP0PcPWPaPcP0P1PfPgPoPfPoPsPfPhPoPfPoPrPfPiPoPfPoPqPfPjPoPfPoPpPfPkPoPfPoQ0DPfPmPoPfPoQ0CPfPnPoPfPoQ0BPfPoPoPfPoQ0APfPoGPF4F4F4F4F4F4F4DSP[P^P\PPPYPRPuPtQ0SPw%dcRo=<xoPyPzb5b6b711ccP6b4b:b9b816cWRf16c0Rn'111nnRmP}P~PfPnP}P}P}P{PcPc%;cPWP0P7M:ePnPn%;nGXP[P^P\PPPYPRPuPtQ0SPwQ0O,^oRo=<xoPyPzb5b6b7PmP6b4b:b9b8CRGD%WI#89EaceM:VC@C@C@C@C@C@C@WQWIP8P6O2n2001000010121000000W3WKXWZP8P6O2n2001000010121100000W3P8P6O2n2001000010121000000W3WHWNP8P6O2n2001000010121000000W3XVZP8P6O2n2001000010121100000W3P8P6O2n2011000010121000000W3WGWMP8P6O2n2001000010121000000W3XUZP8P6O2n2001000010121100000W3P8P6O2n2011000010121000000W3WFWLP8P6O2n2001000010121000000W3XTZP8P6O2n2001000010121100000W3P8P6O2n2011000010121000000W3WJX1KP8P6O2n2001000010121100000W3P8P6O2n2011000010121000000W3W?P8P6O2n2011000010121000000W3n0110101020101P>O1CUQ00,kMeWEWSWPW3X<LP8P6O2n2001000000121100000W>WXWCW[WRo"). Qed.

(* [comment removed for export] *)
Definition shadow_avoid (W : list ivl) (L : layoutA) : Prop :=
  disjoint_from W (shad (l_ACEIL L)) (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8))
  (* [comment removed for export] *)
  /\ Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.

Lemma acc_transport : forall W (m m' : mem) a n, acc asegs m a n -> munch W m m' -> 0 < n ->
  disjoint_from W (shad a) (shad (a + n - 1) + 1 - shad a) -> acc asegs m' a n.
Proof.
  intros W m m' a n H MU Hn D i Hi. destruct (H i Hi) as (b & Hb & Ho). exists b. split; [|exact Ho].
  apply (bytes_at_transport asegs W m m' _ _ Hb MU). cbn [length Z.of_nat].
  apply (dsj_sub W (shad a) _ _ _ D); unfold shad; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia|].
  assert ((a + i) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma shadow_rep_transport : forall W L (m m' : mem), shadow_rep L m -> munch W m m' -> wmono asegs m m' -> shadow_avoid W L -> shadow_rep L m'.
Proof.
  intros W L m m' (B & S1 & S2 & SA) MU WM (A & AS). split; [|split; [exact (stk_wmono m m' _ _ S1 WM) | split; [exact (stk_wmono m m' _ _ S2 WM)|]]].
  - apply (bytes_at_transport asegs W m m' _ _ B MU). unfold zrun. rewrite repeat_length.
    replace (Z.of_nat (Z.to_nat ((2 ^ 47 - l_ACEIL L) / 8))) with (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8)) by lia. exact A.
  - unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
    pose proof (proj1 (Forall_forall _ _) AS r Hr) as D. cbv beta in X, D.
    assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
Qed.

(* [comment removed for export] *)
Definition consts_avoid (W : list ivl) (L : layoutA) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r - fst r)) (consts_rngs L).

Lemma consts_rep_transport : forall W L (m m' : mem), consts_rep L m -> munch W m m' -> wmono asegs m m' -> consts_avoid W L -> consts_rep L m'.
Proof.
  intros W L m m' H MU WM A. apply (consts_rep_frame L m m' H); [|exact WM].
  intros x Hx. apply MU. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hx). cbv beta in Hx.
  exact (disjoint_outside W (fst r) (snd r - fst r) (bv_unsigned x) (proj1 (Forall_forall _ _) A r Hr) ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition art_avoid (W : list ivl) (Σ : rtsA) : Prop :=
  consts_avoid W (lay Σ)
  /\ (forall c, 1 <= c <= 31 -> reg_avoid W (l_SB (lay Σ)) c (pr Σ c) /\ pclass_avoid W (l_T (lay Σ)) c)
  /\ (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W (l_SB (lay Σ)) c i st)
  /\ (forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s)
  /\ sec_avoid W Σ /\ quar_avoid W Σ /\ dep_avoid W (lay Σ) /\ fs_avoid W Σ /\ dsjl W ia_lits /\ shadow_avoid W (lay Σ).

Lemma ART_transport : forall W Σ (m m' : mem), ART_A Σ m -> munch W m m' -> wmono asegs m m' -> art_avoid W Σ -> ART_A Σ m'.
Proof.
  intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof (ART_wf Σ m H) as Hwf.
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - exact (consts_rep_transport W _ m m' (ART_consts Σ m H) MU WM A1).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m H c Hc) MU WM (proj1 (A2 c Hc))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m H c Hc) MU WM (proj2 (A2 c Hc))).
  - destruct (ART_chunk Σ m H) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn)).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk)).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m H) MU WM A5).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m H) MU WM A6).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m H) Hdok MU WM A7).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m H) MU WM A8).
  - exact (ia_rep_transport W Σ m m' (ART_ia Σ m H) MU WM A9).
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m H) MU WM A10).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m H) WM).
Qed.
