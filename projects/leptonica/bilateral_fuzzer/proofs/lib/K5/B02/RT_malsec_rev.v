(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Exec RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface D_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import R_cache_defs R_prim_defs R_thread R_tlsgetaddr R_glue_defs R_sec_defs R_fs_defs RT_state RT_rep RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_sys_stmt RT_vis RT_malsec_state.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_malsec_rev () := "C47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K52AS8AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53B028RT_state5pg_dnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5pg_upC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib2K53B029RT_facts07rta_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7rtA_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4smszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53B028RT_state5l_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8grant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7rt_mapsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib2K53B029RT_facts0;rz_size_bigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z5max_lC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev;pg_up_factsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7add_modC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib2K53B026Layout?K_LOW_SHADOW_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@K_HIGH_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr03I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z7div_mulK46Stdlib;setoid_ring<Ring_polynom5PExpr07C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01c69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_mapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@K_HIGH_SHADOW_loC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00c69OSSVerify5KrLib2K53B02=RT_malsec_rev7p_firstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev6p_lastC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev;pg_dn_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev7rv_shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout?K_LOW_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?RT_malsec_state3shwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev5W_revC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes9andb_propc69OSSVerify5KrLib2K53B02=RT_malsec_rev;page_base_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep?outside_app_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev<page_base_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib2K53B02=RT_malsec_rev8rv_pagesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes8list_indC69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib2K53B02=RT_malsec_rev:dsj_withinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev9rv_withinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state>startup_grantsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ART_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9budget_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7dep_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8rt_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_f0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_tidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_al0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8maps0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state>pairwise_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7l_maps0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC46Stdlib5Lists4List=Forall_forallK47Corelib4Init5Logic2or01C46Stdlib5Lists4List9in_or_appC47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53B028RT_state3secC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B027RT_geo0:geo_of_ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo07g_grantC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53B028RT_state:shadow_resC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5secst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6secmapC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib2K53B02=RT_malsec_rev9page_meetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_revAallowed_of_windowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK46Stdlib9micromega=RingMicromega3Op206c69OSSVerify5KrLib2K53B02=RT_malsec_rev7dsj_padC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7dsj_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev>rv_grant_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo05g_prbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib9micromega:ZMicromega;ZArithProof06I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List<nth_error_InI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53B02;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6fk_prbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev:rv_prb_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6kFaCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4r_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit7fk_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7r_muserC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegI69OSSVerify5KrLib2K53B028RT_state4ckst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8kUserCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit<fk_shad_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_transc69OSSVerify5KrLib2K53B02=RT_malsec_rev<rv_prim_shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4s_mbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8sec_nresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3s_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2awC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6fk_mapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs3ru8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7SEC_MAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev:rv_sec_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state:allow_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<schunk_avoidC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_revC46Stdlib5Lists4List6in_mapC69OSSVerify5KrLib2K53B027RT_fkit8fk_aceilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev7dsj_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_quarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs5fdrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow7ushadowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev9rv_secmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit;fk_shad_le2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_rC69OSSVerify5KrLib2K53B02;RT_freelift:fdrun_lenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;RT_freelift>fl_ushadow_lenC1?~~~~~~~~~~~~~~~K46Stdlib;setoid_ring<Ring_polynom5PExpr06C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib2K53B02=RT_malsec_rev8rv_grantC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev=in_allow_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo06geo_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fs_cls_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs2NFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs:frame_addrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K53B028RT_state6framesC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C69OSSVerify5KrLib2K53B028RT_state5fs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fss_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs5nbusyC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List6filterC69OSSVerify5KrLib2K53B028RT_state8fss_hintC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs8flags_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;RT_freelift>fl_flags_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs9flags_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs7fl_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs3fszC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_fsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs@frame_addr_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev8rv_fshadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<fs_cls_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7CREDIT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs>kFakeStackSizeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C69OSSVerify5KrLib2K53B028RT_trans8fs_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans4dsjlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev9rv_fs_clsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev4rv_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo07g_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7fs_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrCg_real_tls_get_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr9g_dtv_ptrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr6g_dtv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrBg_got_common_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrHg_intercept_tls_get_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr?g_got_verbosityC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddrCg_current_verbosityC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr;g_tls_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr>g_got_dtls_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_tlsgetaddr:g_tls_dtlsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<shadow_avoidC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC69OSSVerify5KrLib2K53B026RT_rep6CS_ACCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<consts_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9reg_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pclass_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pchunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9sec_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans:quar_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9dep_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame;consts_rngsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit@consts_rngs_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit<ris_of_wholeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6kv_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit9kv_pclassC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit9kv_pchunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev;dsj_nil_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6kv_secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53B028RT_state7qent_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5qentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6qbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53B027RT_fkit7kv_quarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6kv_depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit5kv_iaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7ia_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit;CONSTS_LITSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_risC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev5rv_faC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev;rv_shad_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev7rv_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev<rv_shad_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev9rv_schunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans8sec_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_globalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_cmutexC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B028RT_state4ckst04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5batchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6QMAX_GC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6QMAX_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit8DEP_LITSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev5rv_fsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_rev9rv_shadowC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma allowed_of_window : forall A lo hi p, In (lo, hi) A -> lo <= p -> p + 4096 <= hi -> 0 <= p < 2 ^ 64 ->
  page_allowedb A (Z_to_bv 64 p) = true.
Proof.
  intros A lo hi p Hin H1 H2 H3. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|].
  cbn [fst snd]. rewrite unsigned_lit by exact H3. unfold page_size. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma page_meet : forall p s e lo hi, p mod 4096 = 0 -> lo <= s -> e <= hi -> p < e -> s < p + 4096 ->
  pg_dn lo <= p /\ p + 4096 <= pg_up hi.
Proof.
  intros p s e lo hi Hp H1 H2 H3 H4. unfold pg_dn, pg_up. apply Z.mod_divide in Hp; [|lia]. destruct Hp as [q ->].
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (hi + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (hi + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma pg_dn_facts : forall x, 0 <= x -> pg_dn x <= x < pg_dn x + 4096 /\ pg_dn x mod 4096 = 0 /\ 0 <= pg_dn x.
Proof.
  intros x Hx. unfold pg_dn. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

Lemma pg_up_facts : forall x, 0 <= x -> x <= pg_up x < x + 4096 /\ pg_up x mod 4096 = 0.
Proof.
  intros x Hx. unfold pg_up. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)).
  split; [lia|]. apply Z.mod_mul. lia.
Qed.

Lemma page_base_Z : forall a : word, bv_unsigned (page_base a) = pg_dn (bv_unsigned a).
Proof.
  intros a. unfold page_base, page_base_of, page_size, pg_dn. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)).
  rewrite unsigned_lit by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]). reflexivity.
Qed.

Lemma page_base_eq : forall a : word, page_base a = Z_to_bv 64 (pg_dn (bv_unsigned a)).
Proof. intros a. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition p_first (P : Z) : Z := pg_dn (shad P).
Definition p_last (P n : Z) : Z := pg_dn (shad (P + smsz n) - 1).

Definition W_rev (Σ : rtsA) (P n : Z) : list ivl :=
  [(shad P, shad (P + smsz n))]
  ++ (if page_allowedb (rtA_allow Σ) (Z_to_bv 64 (p_first P)) then [] else [(p_first P, p_first P + 4096)])
  ++ (if page_allowedb (rtA_allow Σ) (Z_to_bv 64 (p_last P n)) then [] else [(p_last P n, p_last P n + 4096)]).

Section Rev.
Variables (Σ : rtsA) (m : mem) (P n : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x8000000.
#[local] Notation L := (lay Σ).
#[local] Notation A := (rtA_allow Σ).
#[local] Notation msz := (smsz n).

(* [comment removed for export] *)
Lemma rv_map : 0 < P /\ P mod 4096 = 0 /\ P + msz <= l_ACEIL L /\ (P + msz <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= P)
  /\ SEGTOP_A <= P /\ 72704 <= msz /\ msz mod 4096 = 0 /\ msz <= 0x8004000 /\ l_ACEIL L <= 2 ^ 47 - 0x800000.
Proof using HA HG Hn.
  pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi in W2. clear HA.
  assert (AC : l_ACEIL L <= 2 ^ 47 - 0x800000) by (unfold l_ACEIL, STACK_WIN; lia).
  destruct HG as ((G1 & G2 & G3 & G4 & G5) & _).
  assert (RZ : rz_size n = 2048) by (apply rz_size_big; lia).
  assert (ND : needed n = 8 * ((n + 7) / 8) + 2048) by (unfold needed, rounded; rewrite RZ, !Z.max_l by lia; reflexivity).
  assert (E : msz = pg_up (needed n + 2048) + 4096) by (unfold smsz; rewrite RZ; reflexivity).
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (pg_up_facts (needed n + 2048) ltac:(lia)) as (U1 & U2).
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [destruct G5 as [G5|G5]; [rewrite E in G5; lia | exact G5]|].
  split; [lia|]. split; [rewrite E, Z.add_mod, U2 by lia; reflexivity|]. split; [lia | exact AC].
Qed.

(* [comment removed for export] *)
Lemma rv_shad : shad P mod 512 = 0 /\ shad (P + msz) = shad P + msz / 8 /\ msz / 8 mod 512 = 0 /\ 9088 <= msz / 8
  /\ SHB <= shad P /\ shad (P + msz) <= K_HIGH_SHADOW_hi
  /\ (shad (P + msz) <= 0x8fff6e00 \/ K_HIGH_SHADOW_lo <= shad P).
Proof using HA HG Hn.
  pose proof rv_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). clear HA HG.
  unfold shad, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  apply Z.mod_divide in M2; [|lia]. apply Z.mod_divide in M7; [|lia]. destruct M2 as [q1 E1]. destruct M7 as [q2 E2].
  rewrite E1, E2 in *.
  assert (D12 : (q1 * 4096 + q2 * 4096) / 8 = (q1 + q2) * 512) by (replace (q1 * 4096 + q2 * 4096) with ((q1 + q2) * 512 * 8) by ring; apply Z.div_mul; lia).
  assert (D1 : q1 * 4096 / 8 = q1 * 512) by (replace (q1 * 4096) with (q1 * 512 * 8) by ring; apply Z.div_mul; lia).
  assert (D2 : q2 * 4096 / 8 = q2 * 512) by (replace (q2 * 4096) with (q2 * 512 * 8) by ring; apply Z.div_mul; lia).
  rewrite D12, D1, D2.
  split; [rewrite Z.add_mod, Z.mod_mul by lia; reflexivity|]. split; [ring|].
  split; [apply Z.mod_mul; lia|]. lia.
Qed.

Lemma rv_pages : p_first P <= shad P < p_first P + 4096 /\ p_first P mod 4096 = 0
  /\ p_last P n < shad (P + msz) <= p_last P n + 4096 /\ p_last P n mod 4096 = 0
  /\ shad P + 4096 <= p_last P n
  /\ ((K_LOW_SHADOW_lo <= p_first P /\ p_last P n + 4096 <= K_LOW_SHADOW_hi)
      \/ (K_HIGH_SHADOW_lo <= p_first P /\ p_last P n + 4096 <= K_HIGH_SHADOW_hi)).
Proof using HA HG Hn.
ltac2:(KReplay.run1 (kr_t_RT_malsec_rev ()) ["Rev"] "p'0h01Hh14__x1h24__x2h36__sat8h46__sat9h57__arithh64__ffh77__sat10h88__varmaph95__with:6__sat7h;5heq_xh<5heq_yh=1zh>4__x3h?1xi001xh@1yhA7__sat11hB2D1hC2D2hD2D3hE2E1hF2E2hG2E3hH2S6hI2S7hJ4__p1hK4__x4hL1ahM1bhN2ExhO2EyhP2S1hQ2S2hR2S3hS2S4hT2S5hU2qxhV2qyp%0p&0p;1p;2p;3p;4p;6p;7p;8g01FAj1mTg002`j13Tg003Ej1<Tg00QKj2DTg0124k102Tg003cj21Tg00U:j2wTg00UWj16Tg002Dj20Tg014aj2RTg0059R0j22Tg01TKk103Tg01ULk200Tg004]j2GTg00^Vj1cTg015;j2ZTg00V]j2sTg00SHj2fj3OTg00<]j1rTg000mj1qTg00==j2[Tg00>Wj1pTg00?5j1oTg00?`j2_Tg00@nk10=Tg00DIj2nTg00APk20<Tg00B2j2eTg00BLk20;Tg00Hbj3]Tg00C8k309Tg00CWk408Tg01VLj2lTg00Z0j1?Tg00X5j2kTg00=[k105Tg00>9j4\Tg015Xj3bTg00Qkk101Tg00RDj2XTg00Rdj3~Tg00@Cj4`Tg00T9j6}Tg00T]j2>Tg00X^j2|Tg00YGj3{Tg00\cj2WTg00]Oj3gTg00^2j6zTg00Fij6aTg00EOj4^Tg01@Lj6xTg00I<j7jTg00I`j8vTg00`Jk304Tg00\7j2uTg00a3j3dTg00Dlk307Tg00aSj7tTg01=fk70:Tf0R1#3#3p=H%31#3#3#3p=Eg00MCR2g00NFR37]1p=Yf1R4=]21p=8%61#6p=Fg01DA,01p=K%61#6#6#6p==%61#3p=N%31#3#3#3#3#3#3#3p=Sf3R5f2R6'01G41'2p=91D41=]23p=C1041,26p=B1064/21p=71264/R1p=J1241,26p=QP2f4R7P5P6P4P1Exp=M1031p=41n21p=@P6g00KDR8g00KcR9P9g00LCR:P2P4g00PdP1C`g00LcR;Fjp=5P5P8P9P9P:P6P4P1Gvp=;1k21p=IB04241p=:g00dA,u1p=Tg00P8R<?d41p>06B07241p=P1R41,26p=iP2P4g00b^P1C`p=UP4P8P9P9P:P1P;Fjp=LP6P8P9P9P:P4P1Ftp=AAd<419d<6p=VP6P8P9P9P:P4P1K0:p=h1G41,26p=yg01WQp,1PR;#mR=g00MaR>#3R?#HR@#H#ERA#<RB'DRC#YS00p,1nRD$02RE,1;#mRF%<@RG,wERH,1=RI'8RJ1DHBRK#YRL%6@#FR@#3#H#E#<RM/0HRNg01Qk/0=RO%KFRP%=@#=#N#FS01#3#F#N#S#<R@,0Fg01R`RQ/0=RR'RRS'2RT'2RU'2RV'2RW'2RX'2P0Q00PX&03;RYP=P=%3A#HS02#<RZ,1YC91CYZ200;DRD/GF11DZR;7BF1CDZ11=ZR[g01C?R\/0Yg01XRR],0;%K;97QY3J77D3Q3QRDP1Q00P0PJPWPDP1P0PLPVPDP1P0PNPUPDP1P0POPTPDP1P0PPPSPDP1P2PI%c=RYP=P=11YZC9R;1DYZR^#YR_%<>R`,Z1#cRa/G111aZRb7B11CaZ10\YRc10b]10QYRd%Kb'23J97[a3Q3QX=2PF101@/RRX=2P1PIfARaDM10I@/RRPF%K1X=2P6PIfBS03DM%KI1sEGRR%4E%4G%4HRG[[RE1fHBRb%4BRe%4K[\GRG1f=BRB%4=RK%4C\e[Re%r<RC%q<R<1[24%p2Rf%o2Rg%6>S04#6S05#=#=#=S06#N#H#E#S#<Rh#@1_2>R>55gS07&0=9Ri1n23Rj=5g>C;20<g:RkP1P6g00JDRlg00JdRm'e20;16=]lmdB09234H08R3b6b8b9X1210h1Rm%44[^12P1P=f;RlO2b5b:b3b4PKe,l=%4YRK,2_Rn,2;P0P;Pn1ZI`Ro#cRp/GI11pZRq7BI1CpZRr10q]%Kq,2d5Jc97[p3Q9Q;_RcP1P0P_PKPcP1PRPEPbPGAOYZ6%4ZRd%4^[PBPeg00cbR^#?Rs#?S08#I%IsRs1k2^R^':S09':#T006CP<P21[26S0:P4&052S0;C\RtPfPgQ07PiPg%@MS0<1_2?R?55gPi1P>?%@`Ru5b295gjC;C;PkP3b6b8b9X12X2210M61165Rv/Z`#4[\m^12^22P1PHP=fEfIO4b5b:b3b4b7%4oe,loPpPoPoPqC9Rq%4pRm,2rRw'2P0PqPwPcP1P0PrPmPcP1PYP2PpP2P4P=P=114ZRcC91C4ZS0=1G1I111ZRx7BIS0>1C1ZS0?10[1S0@10x]97\4%Kx97Q43iS0A'2S0B'2S0C'21e2pRQ181pR\eS0DP\1e2YR]186YRIeS0EPIPRPEPbPGf6Ry9O7ZS0Ff5Rz/DZ#4\dS0Gf@R{9OyZS0Hf7R|/DZ#4\dS0IPBPePCP<PtPfPgA5g>?%@ZRt,P>R},U?,Lg5AgR~PiP~C;PkP3b6b8b9X12X22P1P4P4PxC9P4P6P6PcC9[^12^22P1P=f9R~fHO3b5b:b3b4b7bAb;b<Q0=Q0Cf<Q0>Q0BQ0DP\Q0EPIPRPEPbPGQ0FQ0GQ0HQ0IPBPePCP<P2Q0:P41[25C\PfPgQ04,_2S04,P?RI=b2uR\95g>1U\},Lg5AgPi1U>I,LgA5gI}5AgC;PkP3b6b8b9X12X22X>2P11146/Z`RIPIPxC91G4v?Bvc[^12^22^>2P1PHP=f8Rcf?RvO4b5b:b3b4b7bAb;b<Q0?Q0AP5%Y1$01RIP01C641X65[R01X461C56R\[1X57\\A~641P4n2001000000120000000UXM2XL2R\P0\I^M2^L2RIP1P6PZPQ184pR0eP0P]185YR0eP0PRPEPbPGAOzZ|1DyZ#4\dAO|Za1DcZ#4\dRdPBPePCP<Q0;PfPgP8P9P9P:P2Ptg00b7PjC`,LgE}PkP3b6b8b9%YZg00cE[P1b5b:Rjb3b4b7bAb;b<f=R0O41XZ6P\PIP1P5PZPQ185pRIePIP]18zYRIePIPRPEPbPGAO|Z~PdPjb3b4b7b;b<PyO41XZ5g0060S0?P21>1ZRj,8yX=2Q06#3#6#F#E#S#<Rd/0y11zZS06Q01#6#E#S#<RI'0%NA#H#6#F#=#=#N#6#F#E#S#<RAQ06Q02#3#6#F#=#=#=#N#H#E#S#<R\'077y3J97[zP618cjQ0?P218~jX=2f:S0?,0d11~ZS06/0IQ0?Q06/0\57A3J97[~P718ljP21>zZRj10d1110ZR~/0I10~\97A13J97[0X?2P0%41S0?X?2fGPjP7DM%4jf>S06P1P=P=PxC9X?2fM1>yZRjPzDMPjP=P=11jZC9P21>5ZRjQ0@1>cZR[,0dR~?BxI10A[R[?Bx\3iX@2Q06Q0?X@2P{PjP6DM%4jPvP1PoPoPxC9X@2fF1>7ZRxP5DMPxPoPo11xZC9PQ18{pR{eP{P]Q03/8YRYePYPRPEPbPGPBPep-0Re1|2Z={2^RBQ08#?#?RG#?Rb#?RE#?RR#IRY%IERE':':#TR],WsR{%?R#?#IRR%Ib':,:B#T,W^Rb1W^]Q09,:E#TR]1:RE,:B#T,Ws%IG,:Y,:B#T,Ws=VbC7Vb7V]3V7V{P<P2Q0:P4P2Q0;P51[27C\C\PfPgAg2?tR?Q05,_2Rf,P>R<=b2uRu55g1P?tR{,Uu,Lg5AgPiPgPgP8P9P9P:PyEzQ04=g2tR:/Pt,U>,Lg5AgPiPg%@@95g<%@ARt=5g>5hgPiPg%@\R>95g<PiPgQ07PiPgQ0<=5gfPiA5g}?%@d=5g:%@I95g{5AgA5gt:A5g{>5Ag5hg5AgC;C;C;C;C;C;PkP3b6b8b9X12X22X>2XK2WJ1>4ZR31115/Z`R`P`113ZC911jZ9yz4116z/0@10A6'R115y/0\10h710Mc11yZ1>|ZR|11|ZR|/0IAB[|\5J~37[[[[[[^12^22^>2^K2^JeP11>vZ/0=PHPvPlP=PyPcf[fZfafeO;b5b3b4b7b;b<bEbGQ06P6EabBbDP0P7EaWOXV2P4P1O2n2001000010121100000WNXU2P4P1O2n2001000010121100000bFb0bCb0Q0AeC^C^C^C^b@b?XGmXFrP4P1O2n2001000010121000000X0wXEqP4P1O2n2001000010121000000b0XDKXC_P4P1O2n2001000010121000000X0nXB;P4P1O2n2001000010121000000b0bHbIPFPaEaPDeXISXHPP4P1O2n2001000010121000000X0TXTOP4P1O2n2001000010121000000X0UXSNP4P1O2n2001000010121000000X0VXRLP4P1O2n2001000010121000000X0WXQJP4P1O2n2001000010121000000X0XWPP4P1O2n2001000010121000000b0o"). Qed.

(* [comment removed for export] *)
Lemma rev_munch_hyp : forall a : word, page_allowedb [shw P n] (page_base a) = true -> page_allowedb A (page_base a) = false ->
  ~ outside (W_rev Σ P n) (bv_unsigned a).
Proof using HA HG Hn.
  intros a H1 H2. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). pose proof rv_shad as (_ & S2 & _ & S4 & S5 & _).
  clear HA HG.
  unfold page_allowedb in H1. cbn [existsb] in H1. rewrite orb_false_r in H1. unfold shw in H1. cbn [fst snd] in H1.
  apply andb_prop in H1 as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. unfold page_size in X2.
  rewrite page_base_Z in X1, X2. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn [Z.of_N] in RA.
  pose proof (pg_dn_facts (bv_unsigned a) ltac:(lia)) as ((Q1 & Q1') & Q2 & Q3).
  pose proof (pg_up_facts (shad (P + msz)) ltac:(unfold SHB in *; lia)) as (U1 & U2).
  fold (p_first P) in X1. set (x := bv_unsigned a) in *. set (pb := pg_dn x) in *.
  unfold W_rev. intros Ho. apply outside_app_inv in Ho as [Ho1 Ho2]. apply outside_app_inv in Ho2 as [Ho2 Ho3].
  cbn [outside] in Ho1. destruct Ho1 as [Ho1 _].
  assert (Hx : x < shad P \/ shad (P + msz) <= x) by lia. clear Ho1.
  apply Z.mod_divide in R3, R6, Q2, U2; try lia.
  destruct R3 as [q1 E1]. destruct R6 as [q2 E2]. destruct Q2 as [q3 E3]. destruct U2 as [q4 E4].
  destruct Hx as [Hx|Hx].
  - assert (Ep : pb = p_first P) by lia. rewrite page_base_eq in H2. fold x in H2. fold pb in H2. rewrite Ep in H2. rewrite H2 in Ho2.
    cbn [outside] in Ho2. destruct Ho2 as [Ho2 _]. lia.
  - assert (Ep : pb = p_last P n) by lia. rewrite page_base_eq in H2. fold x in H2. fold pb in H2. rewrite Ep in H2. rewrite H2 in Ho3.
    cbn [outside] in Ho3. destruct Ho3 as [Ho3 _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dsj_within : forall (W : list ivl) lo hi a k, Forall (fun p => lo <= fst p /\ snd p <= hi) W -> (a + k <= lo \/ hi <= a) ->
  disjoint_from W a k.
Proof using.
  induction W as [|[x y] W IH]; intros lo hi a k HF H; [exact I|]. apply Forall_cons_iff in HF as [[H1 H2] HF]. cbn [fst snd] in H1, H2.
  cbn [disjoint_from]. split; [lia | exact (IH lo hi a k HF H)].
Qed.

Lemma rv_within : Forall (fun p => p_first P <= fst p /\ snd p <= p_last P n + 4096) (W_rev Σ P n).
Proof using HA HG Hn.
  pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). unfold W_rev.
  apply Forall_app. split; [apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]|].
  apply Forall_app. split; [destruct (page_allowedb _ _); [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]|].
  destruct (page_allowedb _ _); [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]].
Qed.

(* [comment removed for export] *)
Lemma rv_app : forall a k, (a + k <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H. pose proof rv_pages as (_ & _ & _ & _ & _ & X). apply (dsj_within _ _ _ a k rv_within).
  unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_grant_apart : forall b gn, In (b, gn) (startup_grants L) -> apart P msz b gn.
Proof using HA HG.
  intros b gn Hin. destruct HG as (_ & Hap). pose proof (ART_wf Σ m HA) as (HL & _).
  assert (HM : maps0_ok L).
  { unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM. }
  destruct HM as (HM & _). pose proof (proj1 (Forall_forall _ _) HM (b, gn) ltac:(apply in_or_app; left; exact Hin)) as Hin'.
  cbn [fst snd] in Hin'. pose proof (proj1 (Forall_forall _ _) Hap _ ltac:(unfold rt_maps; apply in_or_app; right; exact Hin')) as X.
  cbn [fst snd] in X. pose proof (g_grant Σ (geo_of_ART Σ m HA) b gn Hin) as (G1 & _ & G3 & _).
  pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi, l_ACEIL, STACK_WIN in *.
  assert (Hgn : 0 < gn) by (unfold startup_grants in Hin; destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as _ <-; lia).
  rewrite !unsigned_lit in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma dsj_pad : forall p a k slo shi, In (pg_dn slo, pg_up shi) A -> slo <= a -> a + k <= shi -> p mod 4096 = 0 -> 0 <= p ->
  p + 4096 < 2 ^ 64 -> disjoint_from (if page_allowedb A (Z_to_bv 64 p) then [] else [(p, p + 4096)]) a k.
Proof using Σ.
  intros p a k slo shi Hin H1 H2 Hp0 Hp1 Hp2. destruct (page_allowedb A (Z_to_bv 64 p)) eqn:E; [exact I|].
  cbn [disjoint_from]. split; [|exact I]. destruct (Z_le_gt_dec (a + k) p) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (p + 4096) a) as [Y|Y]; [right; exact Y|]. exfalso.
  pose proof (page_meet p a (a + k) slo shi Hp0 H1 H2 ltac:(lia) ltac:(lia)) as (Q1 & Q2).
  rewrite (allowed_of_window A _ _ p Hin Q1 Q2 ltac:(lia)) in E. discriminate.
Qed.

Lemma dsj_win : forall a k slo shi, In (pg_dn slo, pg_up shi) A -> slo <= a -> a + k <= shi ->
  (shi <= shad P \/ shad (P + msz) <= slo) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k slo shi Hin H1 H2 H3. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & R8).
  assert (B8 : p_last P n + 4096 < 2 ^ 64) by (unfold K_LOW_SHADOW_hi, K_HIGH_SHADOW_hi in *; lia).
  assert (B0 : 0 <= p_first P) by (unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_lo in *; lia).
  unfold W_rev. apply dsj_app; [cbn [disjoint_from]; split; [lia | exact I]|].
  apply dsj_app; [apply (dsj_pad _ a k slo shi Hin H1 H2 R3 B0); lia | apply (dsj_pad _ a k slo shi Hin H1 H2 R6); lia].
Qed.

(* [comment removed for export] *)
Lemma rv_prb_app : forall a k, l_PRB L <= a -> a + k <= l_PRB L + 0x2000011000 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2. apply rv_app.
  pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
Qed.

Lemma rv_prim_shad : forall a k, shad (l_SB L) <= a -> a + k <= shad (l_SB L + 2 ^ 37) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2. pose proof rv_pages as ((R1 & R2) & R3 & (R4 & R5) & R6 & R7 & _). pose proof rv_shad as (S1 & S2 & S3 & S4 & S5 & _).
  pose proof rv_map as (M1 & M2 & _ & _ & _ & _ & M7 & _).
  pose proof (rv_grant_apart (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap.
  pose proof (g_prb Σ (geo_of_ART Σ m HA)) as (P1 & P2 & P3).
  apply (dsj_within _ _ _ a k rv_within). unfold apart in Ap.
  apply Z.mod_divide in P3, R3, R6, M2, M7; try lia. destruct P3 as [q1 E1]. destruct R3 as [q2 E2]. destruct R6 as [q3 E3].
  destruct M2 as [q4 E4]. destruct M7 as [q5 E5].
  assert (D1 : shad (l_SB L) = q1 * 8192 + SHB) by (unfold shad; rewrite E1; replace (q1 * 2 ^ 16) with (q1 * 8192 * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D2 : shad (l_SB L + 2 ^ 37) = q1 * 8192 + 2 ^ 34 + SHB)
    by (unfold shad; rewrite E1; replace (q1 * 2 ^ 16 + 2 ^ 37) with ((q1 * 8192 + 2 ^ 34) * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D3 : shad P = q4 * 512 + SHB) by (unfold shad; rewrite E4; replace (q4 * 4096) with (q4 * 512 * 8) by ring; rewrite Z.div_mul by lia; reflexivity).
  assert (D4 : msz / 8 = q5 * 512) by (rewrite E5; replace (q5 * 4096) with (q5 * 512 * 8) by ring; apply Z.div_mul; lia).
  rewrite S2, D3, D4 in R4. rewrite D3 in R1, R2. rewrite D1 in H1. rewrite D2 in H2. rewrite E2 in *. rewrite E3 in *.
  clear - H1 H2 R1 R2 R4 Ap P1 P2 E1 E4 E5. unfold SHB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from [] a k -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn. intros a k H1 H2 _. apply rv_app. unfold SEGTOP_A, K_LOW_SHADOW_lo in *. lia. Qed.

Lemma rv_grant : forall i b gn a k, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros i b gn a k Hi _ H1 H2. pose proof (g_grant Σ (geo_of_ART Σ m HA) b gn (nth_error_In _ _ Hi)) as (G1 & _ & _ & G4 & _).
  apply rv_app. lia.
Qed.

Lemma rv_T : forall a k, l_T L <= a -> a + k <= l_T L + 4096 -> disjoint_from [] a k -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros a k H1 H2 _. pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
  apply rv_app. lia.
Qed.

Lemma rv_ris : forall a k, RIS_of (l_SB L) <= a -> a + k <= RIS_of (l_SB L) + 4096 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
ltac2:(KReplay.run1 (kr_t_RT_malsec_rev ()) ["Rev"] "h01Hh14__x1h24__x2h34__x3h42Hah57__arithh64__ffh76__sat6h86__sat7h98__varmaph:5__with;4__x4h<2H1h=2H2h>2X1h?2X2h@2X3hA2X4hB2X5hC1ahD1kp;1p;2p;3p;4p;7p;8g012mj1cTg02=Ej1bTg02cEj1PTg002Dj20Tg003cj21Tg002`j12Tg003Ej1:Tg02Onj3ITg02dCj2HTg02<Kj1FTg004]j2ATg00UWj16Tg013ej1`Tg004@j2XTg0059R0j2<Tg01[Qj3UTg01cWj38Tg00;Qj2STg00<9j3RTg00Z0j1CTg00X5j2?Tg00`Jj3BTg00\7j2OTg00<]j1NTg00a3j3MTg000mj1KTg00==j2>Tg00=[j1JTg00>9j4;Tg00>Wj1GTg00?5j1LTg00?`j27Tg00@nj1QTg00DIj2@Tg007Jj1ETg00knj3TTg00Dlj39Tg00APj2aTg00B2j2_Tg00BLj2]Tg00Hbj3\Tg00C8j3YTg00CWj4ZTg02e=j4[Tg00@Cj4WTg00I<j7VTg00I`j8^Tf0R1#2#2p=D%21#2#2#2p=3g00MCR2f1R3g00PdP1CWp=5P3g00KDR4g00KcR5P5g00LCR6P1g00LcFVp=4f3R7P4P5P5P6f2R4P3P1G^p==p,2ΣR8#cR9#bR:#PR;/031143g00MaR<#2R=#2R>#D#3#3R?#:R@,1;'0p,1mp,2HA5I8,H8g00NFR;%F9RA'ARB%3?#3#6#2#D#6#3#3#3#:R?,1ARC%`9'0R9g01ED/0ARD10A:RE%:=RF%6>#2#6RG#:RH'XRI,1:/1@/0CRC'<RJ'<RK'<RL'<P0PBPLp,1Pp,1n5U8R8f5f4RM38P1P0P9PKf9f8588P1P0PDPJf=f<588P1P0PEPCfAf@588P1fDR0fCRN1SFHRO1A;F10;H1A;I[[RP10;FRQg00O\RRARFH3UW4RH10;I\R^4QRQg00P8RRg00cbRS#CRT#C,?21?2T1?2S5B25B2g00dA'O%NR3MRS%KRRRP2P21>27P4%J2RTC;P3PTC;%G2RU%L2RV172<RW172>R>'5,4V%Q5R5PV1@2F%EG5T2RG992>172=R>'5,4VP515W>,4VC=C=1aV6R6P1P4g00JDRFg00JdRX'_1]14=\FXdAY2;3CZR;b6b9b:X12X22X321014117IRX/041047[[^12^22^32P1P:fGRFPAPMfEO5b5b7b8POPPPHPQPSPRP21>24P3P21>2MP7PTC;C;PUPV%6=,72=92G1@2@592RG%6<,721@2?592R<'5,4VP5PVA92W>R>/5G,4VP515><,4VC=C=P6P;b6b9b:X12X22X32X;211X@114?'0113411MI/1@'0114711M?'0[[^12^22^32^;2P1P:PAfFPFP7P0O6b5b7b8C[A880NeXBCXAEP3P1O2n2001000000121000000X0JX@DP3P1O2n2001000000121000000X0KX?9P3P1O2n2001000000121000000X0LX>BP3P1O2n2001000000121000000b0W=W<XD2XC2o"). Qed.

Lemma rv_fa : forall c a k, 1 <= c <= 31 -> ~ In c [] -> fa (l_SB L) c <= a -> a + k <= fa (l_SB L) c + kFaCap -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c a k Hc _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (X1 & X2 & X3 & X4 & X5). unfold fa, rb, kFaCap in *.
  apply rv_prb_app; lia.
Qed.

Lemma rv_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  p_abeg (l_SB L) c i <= a -> a + k <= p_abeg (l_SB L) c i + ClassSize c -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c i st a k Hc Hi _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (X1 & X2 & X3 & X4 & X5).
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i st Hc Hi) as (Y1 & Y2 & Y3 & Y4). unfold rb, kUserCap in *.
  apply rv_prb_app; lia.
Qed.

Lemma rv_shad_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  shad (p_abeg (l_SB L) c i) <= a -> a + k <= shad (p_abeg (l_SB L) c i + ClassSize c) -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c i st a k Hc Hi _ H1 H2.
  pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i st Hc Hi) as (Y1 & Y2 & Y3 & Y4). unfold rb, kUserCap in *.
  apply rv_prim_shad; [eapply Z.le_trans; [apply (fk_shad_mono (l_SB L) (p_abeg (l_SB L) c i)); lia | exact H1]|].
  eapply Z.le_trans; [exact H2|]. apply fk_shad_mono. lia.
Qed.

Lemma rv_shad_reg : forall c a k, 1 <= c <= 31 -> ~ In c [] ->
  shad (rb (l_SB L) c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a -> a + k <= shad (rb (l_SB L) c + 2 ^ 32) ->
  disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn.
  intros c a k Hc _ H1 H2. pose proof (ClassSize_range c Hc) as (C1 & _).
  apply rv_prim_shad; [eapply Z.le_trans; [|exact H1]; apply fk_shad_mono; unfold rb; lia|].
  eapply Z.le_trans; [exact H2|]. apply fk_shad_mono. unfold rb. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_sec_app : forall k s, nth_error (sec Σ) k = Some s ->
  (s_mb s + smsz (s_n s) <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= s_mb s) /\ 0 < s_mb s /\ 0 <= smsz (s_n s).
Proof using HA.
  intros k s Hk. pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (G1 & _ & G3 & G4 & _) & _).
  pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn1 & _ & _ & _ & _ & _ & _ & Hr & Hu & _). split; [exact G4|]. lia.
Qed.

Lemma rv_secmap : forall k s a k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from (W_rev Σ P n) a k'.
Proof using HA HG Hn. intros k s a k' Hk _ H1 H2. pose proof (rv_sec_app k s Hk) as (X & _). apply rv_app. lia. Qed.

Lemma in_allow_main : forall w, In w (allow_main L) -> In w A.
Proof using Σ. intros w Hw. unfold rtA_allow. apply in_or_app. right. apply in_or_app. right. exact Hw. Qed.

(* [comment removed for export] *)
Lemma rv_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid (W_rev Σ P n) s.
Proof using HA HG Hn.
  intros k s Hk. pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn1 & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & _).
  pose proof (rv_sec_app k s Hk) as (X & _ & _).
  assert (Hin : In (pg_dn (shad (s_mb s)), pg_up (shad (s_mb s + smsz (s_n s)))) A).
  { pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & _ & _ & HG3).
    unfold rtA_allow. apply in_or_app. left. exact (proj1 (Forall_forall _ _) HG3 s (nth_error_In _ _ Hk)). }
  assert (Hap : apart P msz (s_mb s) (smsz (s_n s))).
  { destruct HG as (_ & Hap). pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact (nth_error_In _ _ Hk))) as Y.
    unfold secmap in Y. cbn [fst snd] in Y. pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (_ & Z1).
    rewrite !unsigned_lit in Y by lia. exact Y. }
  pose proof rv_map as (M1 & _ & M3 & _).
  assert (Hsh : shad (s_mb s + smsz (s_n s)) <= shad P \/ shad (P + msz) <= shad (s_mb s)).
  { unfold apart in Hap. destruct Hap as [Y|Y]; [right | left]; apply fk_shad_mono; lia. }
  assert (SH : forall a k', shad (s_mb s) <= a -> a + k' <= shad (s_mb s + smsz (s_n s)) -> disjoint_from (W_rev Σ P n) a k')
    by (intros a k' H1 H2; exact (dsj_win a k' _ _ Hin H1 H2 Hsh)).
  assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
  unfold schunk_avoid.
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | lia]|].
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | lia]|].
  split; [apply (rv_secmap k s); [exact Hk | intros [] | lia | destruct (s_quar s); lia]|].
  pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
  pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
  pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
  replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
  assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
  pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
  pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
  pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
  replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
  split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
  split.
  - apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
    rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rv_fsb : forall a k, l_FSB L <= a -> a + k <= l_FSB L + 0xb09000 -> disjoint_from (W_rev Σ P n) a k.
Proof using HA HG Hn. intros a k H1 H2. exact (rv_grant 5 (l_FSB L) 0xb09000 a k eq_refl ltac:(lia) H1 H2). Qed.

Lemma rv_fshad : forall f k, l_FSB L <= f -> f + k <= l_FSB L + 0xb09000 -> 0 <= k ->
  disjoint_from (W_rev Σ P n) (shad f) (k / 8).
Proof using HA HG Hn.
  intros f k H1 H2 Hk. pose proof (rv_grant_apart (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as Ap.
  pose proof (g_grant Σ (geo_of_ART Σ m HA) (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  pose proof rv_map as (M1 & _).
  apply (dsj_win _ _ (shad (l_FSB L)) (shad (l_FSB L + 0xb09000))).
  - apply in_allow_main. unfold allow_main. right; right; left; reflexivity.
  - apply fk_shad_mono. lia.
  - pose proof (fk_shad_le2 f k ltac:(lia) Hk) as E. pose proof (fk_shad_mono (f + k) (l_FSB L + 0xb09000) ltac:(lia)). lia.
  - unfold apart in Ap. destruct Ap as [Y|Y]; [right | left]; apply fk_shad_mono; lia.
Qed.

Lemma rv_fs_cls : forall k, (k = 0 \/ k = 1 \/ k = 6 \/ k = 2)%nat -> fs_cls_avoid (W_rev Σ P n) (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using HA HG Hn.
ltac2:(KReplay.run1 (kr_t_RT_malsec_rev ()) ["Rev"] "h01Hh14__x1h27__arithh34__ffh48__varmaph55__with64cstrh72Hah84__x2h94Hlenh:1kh;1zh<2_Hh=6__sat3h>6__sat4h?4__x3h@1phA1xhB2fkhC2A1hD2A2hE2F0hF2F2hG2F4hH3FC2hI2HFhJ3HGohK2HchL3HfzhM2HkhN2HphO3HwfhP2R1hQ2R2hR3_H0hS3_H1hT1yp%0p&0p;1p;3p;2p;4p;6p;<p;7p;5p;8g00Z0j1\Tg02Onk30`Tg03MJk10\Tg012mk10WTg01mLk10MTg01nJk10GTg020Bk10DTg0229k10ATg0059R0j23Tg01[Qk30hTg02Adk10fTg03NDk10_Tg03O<j2rTg003Ej1ATg03P:k10[Tg00UWj1JTg002`j1=Tg03Q2k10VTg03Qjk10TTg000Mk20QTg009Uk30:Tg02JZR1j10Tg03Rbj19Tg004]j2OTg006mk30ETg03SZj3LTg03TZk107Tg03U:k406Tg0060k20@Tg03UVk10?Tg019hj3}Tg03VQk20=Tg02J:j2bTg002Dj24Tg03Vfj2]Tg03W`j1STg03X^j1eTg03YYk20bTg03Z9k30aTg03ZTj1dTg004@j2DTg03[Qk10^Tg015;k20]Tg00T]k201Tg03\Lj2KTg02MMj3pTg00Fij6[j7hTg014aR2j22Tg00Hbj3:k10YTg00i]k10XTg00B2j2^Tg00nTl<mTg03Inj6?Tg02nRj1>Tg00<]k10STg000mk10PTg00=[k10OTg00>Wk10NTg00?5k10LTg00DIk209Tg00APk20KTg00BLk20JTg00C8k30ITg00CWk40HTg03JVj4iTg03]Jk20FTg03^Pj1_Tg003cj28Tg01cWj3FTg03_Ok208Tg03`Lj1XTg01FAj1wTg00U:j2tTg00==j2zTg00?`j2yTg03aEj4|Tg00>9k405Tg00@nk10>Tg03bEk50RTg00;Qj2lTg00<9j3sTg00knj3nTg007Jk104Tg03cKk50gTg00EOk403Tg03dMk402Tg00mIm<0<Tg00@Cj4fTg00I<j7cTg01=fk70eTg00]Ok30dTg00Dlk30;Tg00I`k80cTg02bfR3f0R4g00cbR53:p=Zf1R6=:34p=;f3R7f2R85:3A:364'2p=E1264,28p=Wf4R9P7%081]64H02p=Rg00NFR:/44p=5g00MCR;?:64p=11]64#Sp=VA:386/24p=q1b;4p=oA:;4:p=7A:;64,28p>0ZA:;78A:;64'2p=<1]64#S,b;p=BA:;:4p>00P3P;P;P;P1P1P7P8P6P5P:P4N<0<p>0UP;P;P4P6P8P7P9P:f5R<f6R=f7R>f8R?M<mp=~209;4p=QP8g00KDR@g00KcRAPAg00LCRBP;P6g00b7RCP4Cfg00LcRDFcp=kP9P@PAPAPBP7P@PAPAPBP;P8PCP6CfPDFcP4K0ep=@P3P;P;P;P1P1P<P9P7P8P6P4N<0<p=xP;P;P>P=P<P9P7P8P6P:P:P4M<mp=vP;P;P4P6P8P7P9P<P=P>P?f9M<mp=I%=4#=p=u%=4#=#=#=p=T1886/44p=6P9P7P81]64H02p>0C20164,88p=G%S4,b;p>0BA:;86/24p=jB0d;64p=UB0;;64p=HP8P@PAPAPBP;P6g00PdR1P4CfPDFcp=NP;P:P7P8P6P4E[p={P;P9P7P8P6P4E[p=CP7P@PAPAPBP;B0;;86P1P4CfPDFcp=PP7P@PAPAPBP8P6P4L0cp=`20164,O:p=M1O:4p=YP;P6g00b^P4Cfp=aP6P@PAPAPBP4PDFcp=g%Z4%\5RD,;4P4%\DR@#\#\#\#\R1P4P@CE3WRCp,2ΣREp,1mp,2HA40`&0\ERFP4PFP0&0WERF$0MS00&0GERG&0DERH&0AERI'3RJ'3S01p,1Pp,1n60hERK&0fFRFP9PEP9DRP4Q00Q01P0PGPJPKPFP?PEP?DRP4P0PHPIPKPFf<RLPEPLDRP4P0&0_ERL,r:S02g00MaRM#ARN&0[ERO'rRP%JMRQ#=S03#ARR&0VERS'rRT%=MRU#ARV&0TERW'rRX'3RY20Q;3RZB0:;34R[#Z1;[DP[P1P[P@CE3W%54R\B0:;36R]#0R^#9,O4'3B0E;36ALF^4'1P;&0741VE]P:H06/1N'3'3X@;-0@;'3XBZ&0?ER]3}20=Z]1bZ]#0%=UR^#=R_#=R`#ARa'41]E6Rb#S#e#020b[8XBZ>0aZ],bZ#0'1\C^:3%db%JQRb#=#A,DVg03eN&0^E+0]+01'4\C^:3'3'3'3'3RC'3RZ'3S04PKPFf@R]PEP]DRP4Q02Q04P0PPPZPKPFfDR]PEP]DRP4P0PYPCPKPFfHR]PEP]DRP4P0PTPXPKPFfLR]PEP]DR\CP4P2fOR]#ZP]P1P]P@CE9q]DfPR[#0Rc1VE[Rd'KfN%Z[P3P5%04Re1VE4Rf'KX:3Rg%SLRh,K:%dLRL#5%Jb#=#J#A,DVRb,OL'3%eh#0/4a'3f?3pfQRhP4E[W0P4O1P[P1P[P@CE9q[DP21;hDPhP1PhP@CEfRR[#0RL1VE[Ri'KP41;[DP3PDPg%SORj,KN%dORO#51OOb'3%ej#0/4a'3f=S053pfSRjP4E[W0P4O1P[P1P[P@CEP21;j11;j@fTR[#0RO1VE['KP41;[1RkP3P1Pg%SSRl,KR%dSRS#51OSb'3%el#0/4a'3;p?fURlP4E[W0P4O11;[@RSP3P@Pg%SWRg,KV%dWRW#51OWb'3%eg#0/4a'3;p>PlP4E[W0P4O1n200100000021000010000W0P4O1n200100000021000011000W0P4O1n200100000021000011000%0]1VE]'KP0%od#0%9c'1%74@0Z4NX;;Rc=};dPKPFPhPEPhDRP4%oi#0%9L'11VEj9};cP2%Z[12kS9q[D%0lR[#711[NP[PRP[PVC<3WPj%ZlP3P5%of#0%9e'1%06Rf#711fNPfPRPfPVC<3W]9X:3Rf1BE5Rj#0RS%05R5#9'1%75Rk115NRc115RRL115VRi'2Rh'2Rd'2R]A:;::Ra&00NRg&00RRW&00VRb'2Rm'2Rn'2RoPkPdPaPnP;P;&0Y;RnP4XA;RaPn1164$0XXT;XA;RdP5P:PaPa1^;eXA3Re1^;:RkH0URpP:P:PkM<mPcPhPgPmPnPaPnPdP5PpPNPN1^;NRmM9~PLPiPWPbPnPaPnPdP5PpPRPR1^;RRbM9~PnPaPnPdP5PpPVPV1^;VRpM9~E?E?E?%>j%5Sg00P8RS$0SRj&0PSRS&0O;R5&0N;RW&0L;RiPi209;:RLPLPiPiPL%QNRgPiPiPL%QRRh%QVRc9kiLD@D@D@20KiBRBP4P8g00JDRqg00JdRr'^20J48=:qrdB0I;:6H0HRrb3b4b5PoP4b2b6CiP]eW9fVR]P4P7FhW0P4O1PlP1PlP@CE9qlDP21;]DP]P1P]P@CEfWRl#0Ro#711oNPoPRPoPVC<3WP41;lDP3PDPf1BEDRq#0Rs%0DRt#9'1%7tRu11tNRv11tRS0611tVS07'2Rw'2Rx'2S08%7NRy11NNRz11NRR{11NVR|'2R}'2R~'2S09PuPxPyP~PnPaPnPdPtPNPaPaPePDPNPmExRDPkGvPvPwPzP}PnPaPnPdPtPNPDPNPNPmM:IQ06Q07P{P|PnPaPnPdPtPNPDPRPRPbM:IPnPaPnPdPtPNPDPVPVPpM:IE?E?E?%>q%5sPjPSP5PWPiPiPgPLPiPiPgPgPiPiPgPhAkigcD@D@D@PBPrb3b4b5Q09P4b2b6CiQ08eW9fXRsP4P<FhW0P4O1PlP1PlP@CEP21;s11;s@fYRq#0RD#711DNPDPRPDPVC<3WP41;q1P3P1Pf1BE1Rt#0R|%01R{#9'1%7{R}11{NS0811{RS0911{VS07'2Rz'2Rw'2S06%7RRv11RNR~11RRS0:11RVRy'2Rx'2Ru'2S0;P}PwPvPuPnPaPnPdP{PRPaPaPeP1PRPbExR1PkGvQ08PzP~PxPnPaPnPdP{PRP1PNPNPmM:IQ09Q07Q0:PyPnPaPnPdP{PRP1PRPRPbM:IPnPaPnPdP{PRP1PVPVPpM:IE?E?E?%>t%5|PjPSP5PWPiPiPhPLPiPiPhPgPiPiPhPhAkihcD@D@D@PBPrb3b4b5Q0;P4b2b6CiQ06eW9fZR|P4P>FhW0P4O11;q@P3P@Pf1BE@Rf#0Rq%0@Rt#9'1%7tR111tNR{11tRS0611tVS0;'2Ry'2Rx'2S0:%7VR~11VNRz11VRRu11VVRv'2Rw'2R}'2S07P1PxP~P}PnPaPnPdPtPVPaPaPeP@PVPpExR@PkGvP{PyPzPwPnPaPnPdPtPVP@PNPNPmM:IQ06Q0;PuPvPnPaPnPdPtPVP@PRPRPbM:IPnPaPnPdPtPVP@PVPVPpM:IE?E?E?%>f%5qPjPSP5PWPiPiPcPLPiPiPcPgPiPiPcPhAkiccD@D@D@PBPrb3b4b5Q07P4b2b6CiQ0:eW9P|P4P>FhW0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000%7O11ONPOPRPOPVC<3W20F[4%u`S0:#u#T#AR`%_[,8`RO'4%9[%J^#T#T#T#AR^56O'3P0%0]R]#_,8`RO,4`%9]=6O^PKPFPoPEPlI0CP4%0s#_,8`,4`%_D,8`%9D;6^%A_R_%0|RD5GFRs=FK_208FDRl1]E|S07$0BS0;#0R|5FKS06f[#0Ro#9,O4,3\S09P;&076f\R\,VEROPNH06#7S08f]#0R]=LF8R[%X]Rq5FK%w[1tq_5FK'3[[^@;S0<'3PsP_P2%7DRsPDPRPDPVC<9jDNRfAGF_oRp,4FP<%7oR@AGF_4Rt,4FX;;Rd%oORO#>S0=%0O#5S0>PjPS1z;6ROPW1y;MRn%Q_Ra/UL,HnRb5NiPBPrb3b4b5X1;AG4_:Rv,44^1;P4PFO1Rub2b6%0\R\P4C{W0P4O1PoPRPoPVC<9joNS0?P211\NS0@P\PRP\PVC<S0AAGF_]Rm,4FP411]NRwPNPdf^Rz,BERy#>S0B%0y#5S0CPjPSPOPW1Uag,HnS0D9NinPBPrb3b4b5X1;AG4_NRg,44^1;Pub2b6%0zRzP4DCW0P4O1P]PRP]PVC<RyP211zRS0E11zVS0Ff_#0R{9GF_Rk,4FP411{RRePRPdf`R},BER~#>Rx%0~#5R~PjPSPOPW1Uah,HnS0G9NinPBPrb3b4b5X1;AG4_RRh,44^1;Pub2b6%0}R}P4DCW0P4O111{VR1PVPdPxP~PjPSPOPW1Uac,HnS0H9NinPBPrb3b4b5X1;AG4_VRd,44^1;Pub2b6P}P4DCW0P4O1n200100000021000010000W0P4O1n200100000021000011000W0P4O1n200100000021000011000P2PsPf%JU#J#T#J#u#J#T#T#T#ARf,8FRs96p_P<A6t_sX;;RtQ0=Q0>PjPSPOPWPiPbPa%QfS0>,HnRbCPPBPrb3b4b5X1;184fRp96v_^1;Pub2b6P\P4C{X0@P4O1Q0?P2Q0@Q0AA6m_sP4PNPtQ0BQ0CPjPSPOPWPiQ0DPaPbCPPBPrb3b4b5X1;A6g_p^1;Pub2b6PzP4DCX0wP4O1P2Q0EQ0FA6k_sP4PRPtPxP~PjPSPOPWPiQ0GPaPbCPPBPrb3b4b5X1;A6h_p^1;Pub2b6P}P4DCX0eP4O1PVPtPxP~PjPSPOPWPiQ0HPaPbCPPBPrb3b4b5X1;A6d_p^1;Pub2b6P}P4DCX01P4O1n200100000021100011000X0yP4O1n200100000021100011000W0P4O1n200100000021100011000C|Q06Q0<%9DRy208Fo=FK4X;;PlPyQ0;#>Ro%5|R1PjPSP;1z;8RuP6P5H05RpPWPi%Q`Rd1y;URa,HdR~5Ni&0>ARA1Hnd/HaRd9NinC`PBPrb3b4b5X1;X8;18`6Rx,4`186`/88R`,46[^1;^8;P4%_\RtPFP7O3b2b614FlePoP1PjPSP;PuP61z;7H05RuPWPiPiP~1y;QRQ%Q^R~CPPAPiPdPQPbCPC`PBPrb3b4b5X1;X8;X?;A6x8^186f96`7[^1;^8;^?;P4%9\PtPFP8O4b2b6A6lyseC|P|P>DCQ09Q08PFP]P8P?P6I0R18F^R]/4[g03fJ,8FR>96[q'3P0ALFz7R0,4]%Xz=60>ALF{9R0%X{R{5FK%w01t{_5FK'3P4ALF}<,4]fa#0R]=LF=%X];6>P2fb#0R>#7P>PRP>PVC<9j>NQ0:#AR]fcR=#0R},DV'MQ05%7}1DV4,M]X;;R<fdR{,BER0#>%00#51lV:%YVR014::1DV:Rz#Y[[%5VRqg00O\R[AsV:6UW7%5z\[^7qPjPSP5PW%Q]R:g03gN9n;c'U,aL,giPBPrb3b4b51M]zRzP4b2b=b>b6Pze%0{R{P4C{W0P4O1P}PRP}PVC<9j}NP211{NP{PRP{PVC<fe#0R{,DV,M]P411{NPNP<ffRz,BER|#>%0|#51lVN%5N1DVNR|#Y[\0AsVN6V[X7q%5|\[^7qPjPSP5PW&04M9n;c,U:,aL,giPBPrb3b4b51M]|R|P4b2b=b>b6P|e%0zRzP4DCW0P4O1P{PRP{PVC<P211zR11zVfg#0Rz,DV,M]P411zRPRP<fhR2,BER|#>RM%0|#5R|1lVR%5R1DVRRN#Y[\0AsVR6V[X7q%5N\[^7qPjPSP5PWQ03$049n;c,U:,aL,giPBPrb3b4b51M]NRNP4b2b=b>b6PNe%02R2P4DCW0P4O111zVPVP<PMP|1lVV1DVVR|#Y\q\0AsVV6V[X7q%5|\[^7qPjPSP5PW&04U9n;c,U:,aL,giPBPrb3b4b51M]|R|P4b2b=b>b6P|eP2P4DCW0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000%X>#YR>eP>ALF}?R?%X}R}5FK%w?1t}_5FKP?P}1BE=R=#>RE%0=#5R=PjPSPpPWPiPiPnP~PaCPPAANinaC`PBPrb3b4b5X1;X8;A64^61468[^1;^8;P4f:9LF{R^PFP9O3b2b6R9PEP=PjPSPuPWPiPiPnPaQ0>,HQCPRQPAPQC`PBPrb3b4b5X1;X8;X?;188f9646187f9668[^1;^8;^?;P4PF%X{R{P^P7O4b2b6R7C|P?P}P9P7PEP=PjPSPOPWPi1aLn,giPAANiLnC`PBPrb3b4b5X1;%Y4%56[^1;P4P{P8O2b2b6I0gH03bLWDWCP6P4O2n2001000000121000000b0W<WNX@;H03H03PKPFPDQ07H02eWQWPP6P4O2n2001000000121000000b0bKW<W9P6P4O2n2001000000121000000bOX<CXHXXGTP6P4O2n2001000010121000000X0YP6P4O2n2011000000121000000X0ZXFPP6P4O2n2011000000121000000W0WEP6P4O2n2011000000121000000XIIXSHP6P4O2n2001000000121000000X0JXRGP6P4O2n2001000000121000000W0W<P6P4O2n2001000000121000000b0bJWMX:3o"). Qed.

Lemma rv_fs : fs_avoid (W_rev Σ P n) Σ.
Proof using HA HG Hn.
ltac2:(KReplay.run1 (kr_t_RT_malsec_rev ()) ["Rev"] "p'0h07__arithh14__ffh28__varmaph35__with41Hh54__x1h62Hrh74__x2h84__x3h91xh:1rh;1Ah<1Ph=1lh>2G1h?3HGoh@3HinhA2X1hB2X2hC2X3hD2_HhE1ahF1fhG2fkhH1khI1yi001ni011pi021zp%0p&0p;3p;1p;2p;5p;4p;6p;9p;7p;<p;8g02Onk30fTg03MJk10eTg012mk10ITg02Adk10>Tg002`j10Tg00UWj14Tg000MS00j2}Tg02<Kk108Tg00Hbj31j1zTg02>>k10XTg02?8k10UTg003Ej18Tg02@0k10RTg02@jk10PTg024ik10KTg025ck10HTg00<]j1|Tg00a3j37Tg001mj32Tg00B2j2ZTg02LUj3xTg02OTj3YTg01jVk10@Tg02Plk50?Tg0175k30=Tg00QKk20;Tg003cj29Tg013ek10:Tg002Dj2:Tg014aR0j23Tg0059S01j2@Tg01[Qk30bTg03glk20_Tg01cWj3OTg03NDk10\Tg03dMj4cTg03P:k10[Tg03Q2k10ZTg03Qjk10YTg03hik20WTg03ibj1HTg03UVk10STg019hj3bTg000mk101Tg00==j2nTg00>Wk10QTg00?5k10OTg00?`j2mTg00APk20JTg00BLk20GTg00C8k30FTg00CWk40ETg03aEj4{Tg00Z0j1UTg02JZR1j1yTg03Hnk20DTg03IQk30CTg03Inj6>Tg00=[k10ATg00DIj2iTg03JVj4XTg03j^j2_Tg00EOj4QTg02L3k30<Tg001Mj4BTg01@Lj6JTg02[nk309Tg02`ck10LTg02ack207Tg03KAm90MTg03kak50NTg03l_k506Tg00X5j2oTg00`Jk302Tg00\7k205Tg00>9k40TTg00@Cj4\Tg00@nk10cTg015Xk304Tg004]k20aTg006mj3sTg009Uj3tTg015;k20^Tg00Dlk303Tg00I<j7]Tg00nTl<dTg01=fk70]Tg00I`k80`Tf0R2#4#0#0#0p=~%02#4p=`%02#0#4#0p=[%02#0#0#0p=E%02#0#0#8p=<%42#0p=eg00MCR3P3f1R4P2CBp=Ng00NFR500a2p=SA1325p=^g01C?R6,:2p>00%02#0p=K%02#8p>0Vg02bfR7=s32p=rAt372p=qf2R8/9400^2p=R1i32p=;B03342p=FP8g00KDR9g00KcR:P:g00LCR;P3P4g00PdR<P2C\g00LcR=F]p=L1984/:2p=6g00cbR>=172p=kA1352p=jA1342p=AA1742p=?P7P3f4R?P1f3R@P8P>P5P4P>P5P2M<dp>0B1Z32p=VP7P3f6RAP1f5RBP?P>P5P@P8P4P2M<dp=pP8P9P:P:P;P3P4g00b7RCP2C\P=F]p=WP?P9P:P:P;P@P9P:P:P;P3P8PCP4C\P=F]P2K0]p==A172>p=hP7P3PAP1PBP?P@P8P4P>P5P2M<dp=gP7P3P2P1P4P8P@P?PBPAf7R1f8RCM<dp=CAs332p=wAt332p=v1942/:6p=G%42#4p=D%02#4#0#4p=TAs334At332'9/:6p=5%42#0#0#4p=M%42#4#4#0p=PP@P9P:P:P;P31i38>0334P<P2C\P=F]p=I%02#0#0#4p=a%42#0#4#0p=f%02#4#0#0p=lP4P9P:P:P;P2P=F]p>0dP@P9P:P:P;P8P4P2L0`p=up,2ΣR9p,1mp,2HA40f&0e9P9P2&0I9R=$0>R<g00MaR6#0RD#4S02#~RE#`#[#E#E#<RF1}33RG&08=%0DRH#0RI#0RJ#E#ERK#ERL#ERM#e#[#E#E#<'N1N<FRN31&0X=%<MRO'NRP&0U=S03%8KRK'NRQ&0R=%8LRL'NRR&0P=S04/NKRS&0K=%8M'N&0H=/NO%|GRO57G57GRM97GNRT57GRU57GRV57GRW57G92GNA1GPNA2GNWA1GQNA2GNVA1GRNA2GNUA1GSNA2GNTA1GNNA2GNM1ZGN3x3Y3Y3Y3Y3Y&0@=92GNeI0?B0==<FQ01%S<S0520;<K#^19<FRN&0:=':&00Ng01DAR=/:<'31:NLg01ED/:<'3'@'@'@S06p,1Pp,1n60b9RL00_9S07P2Q05Q06%8ERE,9<RM%4HS08#8RT5OLPLP<P5&0\9CcRUPLP<%86RR&0[9CcRVPLP<%46RQ#0RW#8RP&0Z9CcS09PLP<%8DRX&0Y9CcRY'@RZg03mZR[-0WLS0:Q04%KWRW#8R\'9S0;%8IRI5OLS0<Q03&0VWRW'9S0=%8JRJ5OLS0>1}37R]%r2%q2#H;RI=OLIXG]S0?&0S9R^3bS0@'@S0A'@S0B'@R_'@R`'@Ra'@PMPTg00P8RM#|Rb&01MRc1n34Rd&0Q3Re&0O3Rf1m36Rg%;E,FgRh3L20Jf;R;P2P8g00JDRig00JdRj'Z20G28=1ijdB0F354H0ERjb1b2b3X53192ERE,:2^53P2P<O1Rib0PbPcPdPe%;T,Fh%;FS0C,Fg5LfP;Pjb1b2b3X53192F96ET^53Pib0C{PUPaA17>>Ra%U>RU#kRi%UURE#US0D#URT#US0E#URh#kRk%kERl'3Rm'3Rn'3A1355Ro%jRRp%jPRq%jXRr'3Rs'3Rt'3RuPaPnPoPt%z7Rt%z3Ro%y4%y2'A1?4220D4240CXI7X97Rn1Z35RaPaI0BPiPmPpPsPtPoPnPaPUPR%VRRsFpPkPlPqPrPtPoPnPaPhPP%VPRrFpPtPoPnPaPEPX%VXRqFpE>E>E>PbPc&0A3RlPePfPf1i35R5P5PfPfP5%;RRkPfPfP5%;PRp%;XRm9Wf5D=D=D=P;Pjb1b2b3PuP2b0CX,_>PVP`%hUR`1?UURV1?UhRu1?UERi'3Rv'3Rw'3%^RRx1ARRRy1ARPRz1ARXR{'3R|'3R}'3R~P`PwPxP}PtPoPnPUPRPsPaFgPVPvPyP|PtPoPnPUPRPsPUPRPsM9CPuPiPzP{PtPoPnPUPRPsPhPPPrM9CPtPoPnPUPRPsPEPXPqM9CE>E>E>PbPcPlPePfPfPkP5PfPfPkPkPfPfPkPpAWfkmD=D=D=P;Pjb1b2b3P~P2b0CX,_UPZP_Q09PY%hhRY1?hUR_1?hhRZ1?hER~'3R{'3Rz'3%^PRi1APRRu1APPR|1APXRy'3Rv'3RV'3R}PYPzPiPVPtPoPnPhPPPrPaFgP_P{PuPvPtPoPnPhPPPrPUPRPsM9CPZP~P|PyPtPoPnPhPPPrPhPPPrM9CPtPoPnPhPPPrPEPXPqM9CE>E>E>PbPcPlPePfPfPpP5PfPfPpPkPfPfPpPpAWfpmD=D=D=P;Pjb1b2b3P}P2b0CX,_h%hER}1?EURy1?EhR|1?EER~'3RZ'3Rv'3%^XRu1AXRR{1AXPR_1AXXRV'3Ri'3Rz'3RYP}PvPuPzPtPoPnPEPXPqPaFgPyPZP{PiPtPoPnPEPXPqPUPRPsM9CP|P~P_PVPtPoPnPEPXPqPhPPPrM9CPtPoPnPEPXPqPEPXPqM9CE>E>E>PbPcPlPePfPfPmP5PfPfPmPkPfPfPmPpAWfmmD=D=D=P;Pjb1b2b3PYP2b0CX,_ECQQ0:Q0Bg01fQp4p710RYp-0\2Rm&014RpQ01Ab842A2?28P?P4O1[^9@Rq[A2@24P@P4O1[^98Ab@84[RXAb?@8\qB0<842P2n2001000000120000000W=W<W;S0BPX^=p^<m^;YS0:P2PG%w2RY%v2Rm5OLX:GP[A2G2[%w4R[%v4Rp1G[p1:=[P0P3P3g03nVS09PICBR[=1G4%06#K#D#`#T#[#D#<S0F/NRR=P3P3g03oNS0GPICBRpP3P3g040ZS0HPICBRXP3P3g041\S0IPICBRqP3P3g042[S0JPICBRrP3P3g043fS0KPRCBRPP3P3g0457S0LPICBRhP3P3g046?S0M%8HRHCBRVP3P3g047KS0NPJCBR_P3P3g048OS0OPICBR~P3P3g049VS0PPICBR|=7GORi57GR{57GRZ57GRy57GRa57GRz57GRu57GRv57GR}57GRx57GS0Q92G41588P2A1G[8PGP[1GYmX:GRmPbPcPlPePf%46#K#M#M#P#M#<S0R%;IRY%DQ#D#D#D#D#P#P#E#E#<Rw#;R`CIP;Pjb1b2b3Q0R?6IwP2b0Q09/GIe15[[eP@P2EJW4P2O1Q0Q92G8P0A1G=@A2G@x15??P2A1G=?PGP=PmPbPcPlPePfQ0FPkP`CIP;Pjb1b2b3Q0F/9RR[/:wP2b0&00[e15==ePBP2EJW4P2O1A2G?xP0A1GpBA2GB}15AAP2A1GpAPGPpPmPbPcPlPePf%06#a#M#[#P#<RxPYP`CIP;Pjb1b2b3A6xIwP2b0Q0G/GIe15ppeP1P2EJW4P2O1A2GA}P0A1GX1A2G1v15CCP2A1GXCPGPXPmPbPcPlPePf%46#K#M#M#P#~#<R}PYP`CIP;Pjb1b2b3A6}IwP2b0Q0H/GIe15XXef9RXP2EJW4P2O1A2GCvP0A1GqXA2GXuf:Rv/5vP2A1GqvPGPqPmPbPcPlPePf%46#K#M#M#P#P#<R}PYP`CIP;Pjb1b2b3A6}IwP2b0Q0I/GIe15qqef;RqP2EJW4P2O1A2GvuP0A1GrqA2Gqzf<Ru/5uP2A1GruPGPrPmPbPcPlPePf%06#K#T#T#e#f#<R}PYP`CIP;Pjb1b2b3A6}IwP2b0Q0J/GIe15rref=RrP2EJW4P2O1A2GuzP0A1GPrA2Graf>Rr/5rP2A1GPrPGPPPmPbPcPlPePf%e6#f#P#l#D#a#8RzPkP`CIP;Pjb1b2b3A6zRwP2b0Q0K/GRe15PPef?RPP2EJW4P2O1A2GraP0A1GhPA2GPyf@RP/5PP2A1GhPPGPhPmPbPcPlPePf%06#K#T#T#D#`#e#<RrPYP`CIP;Pjb1b2b3A6rIwP2b0Q0L/GIe15hhefARhP2EJW4P2O1A2GPyP0A1GVhA2GhZfBRh/5hP2A1GVhPGPVPmPbPcPlPePf%46#`#l#D#K#E#D#<RP%;HRyP`CIP;Pjb1b2b3A6PHwP2b0Q0M/GHe15VVefCRVP2EJW4P2O1A2GhZP0A1G_VA2GV{fDRV/5VP2A1G_VPGP_PmPbPcPlPePf%06#K#T#D#a#[#<Rh%;JRZP`CIP;Pjb1b2b3A6hJwP2b0Q0N/GJe15__efER_P2EJW4P2O1A2GV{P0A1G~_A2G_ifFR_/5_P2A1G~_PGP~PmPbPcPlPePf%06#K#T#D#a#l#<RVPYP`CIP;Pjb1b2b3A6VIwP2b0Q0O/GIe15~~efGR~P2EJW4P2O1A2G_iP0A1G|~A2G~OfHR~/5~P2A1G|~PGP|PmPbPcPlPePf%46#K#M#M#P#f#<R6PYP`CIP;Pjb1b2b3A66IwP2b0Q0P/GIe15||efIP2EJW4P2O1A2G~Og00cEfJR~/5~P2n010000000W6P2O1n200100000021100010000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n200100000021100011000W6P2O1n2001000000211000110003x409W6X:GO4b4Q0<Q0APTQ04PKQ0;PI&0LG207GS'Z1?TURSQ0D,?TRG1?TTR~Q0E,?TRO'3R|'3R6'31AHRRw%8QR`,AHRm1AHHR0Q02#8R_,AHRi'3RV'3R{'3RhPSP6PwP{PtPoPnPTPH%VHR{PUPRPsM9CPGP|PmPVPtPoPnPTPHP{Q0DP`%V`M9CP~POP0PiPtPoPnPTPHP{PTPHP{M9CPtPoPnPTPHP{Q0EP_%V_M9CE>E>E>PbPcPlPePfPfPyPkPfPfPy%;`PfPfPyPy%;_9WfyD=D=D=P;Pjb1b2b3PhP2b0CXPbPcPdPe%;\,FgRh9LfgP;Pjb1b2b3X53192\R\,:2^53P2Q04O1Ryb0PbPcPdPe1FhY%;K,FgRh5LfP;Pjb1b2b3X53192KRK96\I^53Pyb0N90MQ0>Q0@Q0=PJPbPcPdPe%;W,FgRy9LfgP;Pjb1b2b3X53192WRW,:2^53P2Q03O1R\b0PbPcPdPe1FyZ=LfhP;Pjb1b2b3X53A6WJK^53P\b0g01POI0NQ0BQ0:P2P]Q0?P^Q00P3P7A2]2^%r4%q4#H;RI=OLI[P2P3P7P4P2CB=2]^P9PuP8P4P2I06Q08#0#E#E#<R9,9<R^/:8%H4R\=68N%S\'@'@Q011:^@%H8R\=6@N%S\'@%H@=R?I=OLIP21:^B%HBRB=6AN%SB'@Q01%HARB=61N%SB%H1=RCI=OLIP2%HC=6XN%HX#S%Hv=RqIPI1o3E1o3U1o3>60236023g00dA+05=7MbPcP31n38P41n3@H0TRMPePfP3P5g00b^1m3QRQC\-0df&0c:R:Pf%;9,Fg1m3DRD5LfP:1FDQ>043Y9LfgCuCuP;Pjb1b2b3X53X73X83%S8A6498AR@?I,:8[[^53^73^83P2%HqRqPuP<P4PAO5b0PbPcPMPePf1FgDRDQ0C,FQRQ5LfP:B043DY/FY=LfQCuP;Pjb1b2b3X53X73X83198F9624AR48I19@F76I[^53^73^83P2P<PqPuP8O4b0C{WCWBP4P2O2n2001000000121000000W4WAP4P2O2n2001000000121000000bEP3P7P8P4CBR8#r%q8#H;RI=OLIeW@XH7XF3P4P2O2n2001101000121102100X9]O4b4CQCQCQCQCQCQCQQ07eWDW>P4P2O2n2001000000121000000b4b?o"). Qed.

(* [comment removed for export] *)
Lemma rv_shadow : shadow_avoid (W_rev Σ P n) L.
Proof using HA HG Hn.
  pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (X1 & X2). pose proof rv_map as (M1 & M2 & M3 & M4 & M5 & _).
  split.
  - apply (dsj_win _ _ (shad (l_ACEIL L)) (shad (2 ^ 47))).
    + apply in_allow_main. unfold allow_main. right; right; right; left; reflexivity.
    + lia.
    + pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
      replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring. rewrite Z.max_r by (apply Z.div_pos; lia). lia.
    + right. apply fk_shad_mono. lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x66e828) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (dsj_win _ _ (shad 0x10000) (shad SEGTOP_A)).
    + apply in_allow_main. unfold allow_main. left; reflexivity.
    + apply fk_shad_mono; lia.
    + assert ((snd r - 1) / 8 < 843264) by (apply Z.div_lt_upper_bound; lia).
      assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0x66f000 / 8) with 843264; lia). lia.
    + left. apply fk_shad_mono. lia.
Qed.

Lemma dsj_nil_all : forall l : list (Z * Z), Forall (fun r => disjoint_from [] (fst r) (snd r)) l.
Proof using. intros l. apply Forall_forall. intros r _. exact I. Qed.
Lemma dsj_nil_all' : forall l : list (Z * Z), Forall (fun r => disjoint_from [] (fst r) (snd r - fst r)) l.
Proof. intros l. apply Forall_forall. intros r _. exact I. Qed.

(* [comment removed for export] *)
Theorem rev_avoid : art_avoid (W_rev Σ P n) Σ.
Proof using HA HG Hn.
  pose proof (geo_of_ART Σ m HA) as HGo.
  split.
  { apply Forall_forall. intros r Hr. apply rv_app.
    destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
    - left. unfold CONSTS_LITS in Hl. repeat (destruct Hl as [<-|Hl]; [cbn [fst snd]; unfold K_LOW_SHADOW_lo; lia|]). destruct Hl.
    - pose proof (g_grant Σ HGo (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
    - rewrite Er. cbn [fst snd].
      pose proof (g_grant Σ HGo (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia.
    - pose proof (g_grant Σ HGo (l_TCX L) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _). lia. }
  split.
  { intros c Hc. split.
    - exact (kv_reg Σ (W_rev Σ P n) [] HGo (ris_of_whole (l_SB L) (W_rev Σ P n) [] rv_ris) rv_fa rv_shad_reg c Hc (fun X => X)).
    - exact (kv_pclass Σ (W_rev Σ P n) [] rv_T c Hc I). }
  split; [intros c i st Hc Hi; exact (kv_pchunk Σ (W_rev Σ P n) [] HGo rv_slot rv_shad_slot c i st Hc Hi (fun X => X))|].
  split; [exact rv_schunk|].
  split; [exact (kv_sec Σ (W_rev Σ P n) [] HGo rv_img rv_grant (dsj_nil_all _))|].
  split.
  { apply (kv_quar Σ (W_rev Σ P n) [] [] [] HGo rv_img rv_T rv_slot I (dsj_nil_all _) (fun _ _ X => X)).
    pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & HQw & _). exact (proj1 (proj2 (proj2 HQw))). }
  split.
  { apply (kv_dep Σ (W_rev Σ P n) [] rv_img (dsj_nil_all _)).
    intros i b gn a k Hi _ H1 H2. pose proof (g_grant Σ HGo b gn (nth_error_In _ _ Hi)) as (_ & _ & _ & G4 & _). apply rv_app. lia. }
  split; [exact rv_fs|].
  split; [exact (kv_ia (W_rev Σ P n) [] rv_img (dsj_nil_all _))|].
  exact rv_shadow.
Qed.
End Rev.
