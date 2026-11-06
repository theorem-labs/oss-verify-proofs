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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_sep () := "C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8map_consI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib2K53B026RT_sep;not_outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_rangesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indK47Corelib7Numbers7BinNums1Z02I47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B026RT_rep4CS_WC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C69OSSVerify5KrLib2K53B028RT_iface9RT_STATICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=CLIENT_STATICC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B028RT_state4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7aclientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8W_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep?outside_app_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib2K53B026RT_sepCclient_static_coverC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03c69OSSVerify5KrLib2K53B026RT_sep7live_ivC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep>outside_map_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib2K53B026RT_sep8frame_ivC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8fshad_ivC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2K53B028RT_state4rtsA00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib2K53B026RT_sep>W_client_coverC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc69OSSVerify5KrLib2K53B026RT_sep7dsj_mapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7dsj_appC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ART_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9budget_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B02<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7dep_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8rt_countC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6geo_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state>startup_grantsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53B028RT_state5l_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8grant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_f0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_tidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_al0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8maps0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state>pairwise_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep:geo_layoutC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53B028RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3s_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_ubegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4s_mbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53B028RT_state4r_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_ubegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6reg_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2caC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4r_flC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib2K53B028RT_state7ca_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5r_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK69OSSVerify5KrLib2K53B028RT_state4ckst02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List>nth_error_SomeC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K53B029RT_facts0=ClassSize_posC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC69OSSVerify5KrLib2K52AG;R_sizeclass6rz_logC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2K53B028RT_state4smszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8sec_nresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5pg_dnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5pg_upC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2awC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_facts09smsz_roomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_quarC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffI69OSSVerify5KrLib2K53B028RT_state4ckst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8kUserCapC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5secst00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53B028RT_state6kFaCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5kUMapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib2K53B028RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5regst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4reg0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B028RT_state4ckst01C1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C69OSSVerify5KrLib2K53B028RT_state7SEC_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_facts0<rta_frame_inC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2c69OSSVerify5KrLib2K53B026RT_sep9sep_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9geo_grantC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_facts07rta_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7rtA_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@K_HIGH_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout?K_LOW_SHADOW_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9sep_fshadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_facts0=rta_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_facts0>rta_live_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sepBavoid_client_introC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7geo_prbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9sep_stackC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep:dsj_CS_outC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8geo_liveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep=sep_fshad_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib2K53B026RT_sep9geo_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorC56Stdlib5Arith8PeanoNat3Nat6eq_decC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8slot_geoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_lec69OSSVerify5KrLib2K53B026RT_sep:slot_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep<live_in_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep4dsjbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes9andb_propC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib5Lists4List7forallbc69OSSVerify5KrLib2K53B026RT_sep6img_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>forallb_forallC47Corelib4Init9Datatypes4andbc69OSSVerify5KrLib2K53B026RT_sep:dsjb_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_TCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep4ac_TC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib2K53B028RT_trans<consts_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_cache_defs;i_premappedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread@g_tsd_key_initedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread9g_tsd_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread7pth_tsdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_threadBg_pthread_tsd_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_setshadowAg_got_real_memsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_setshadow=g_real_memsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_poison<g_can_poisonC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_poisonPg_cf_clear_shadow_mmap_thresholdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout?off_t_stack_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026LayoutEoff_t_stack_switchingC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026LayoutHg_GOT_shadow_offset_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026LayoutOg_shadow_memory_dynamic_addressC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@g_GOT_detect_uarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026LayoutOg_detect_stack_use_after_returnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9reg_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pclass_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2faC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_transC56Stdlib6ZArith6BinInt1Z<divide_mul_rC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z<divide_add_rC56Stdlib6ZArith6BinInt1Z7add_modC46Stdlib6ZArith4Zdiv:Zminus_modC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z5max_rC56Stdlib6ZArith6BinInt1Z8max_specc69OSSVerify5KrLib2K53B026RT_sep9abeg_mod8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7mod8_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulC69OSSVerify5KrLib2K53B02;R_glue_defs3ru8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8rz_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib6ZArith:ZArith_dec8Z_le_decK47Corelib7Numbers7BinNums1N01C47Corelib5Lists7ListDef6repeatC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List:length_appC69OSSVerify5KrLib2K52AG6Shadow7ushadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C69OSSVerify5KrLib2K52AG6Shadow2z8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib2K53B02;R_glue_defs5farunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs5fdrunC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B028RT_state4ckst03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep<ac_slot_shadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9slot_roomC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep;ushadow_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7ac_slotC1?~~~~~~~~~~~~~~~K46Stdlib;setoid_ring<Ring_polynom5PExpr06C69OSSVerify5KrLib2K53B028RT_trans9farun_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9fdrun_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pchunk_avoidC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B028RT_state4ckst04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_lC69OSSVerify5KrLib2K53B029RT_facts0;rz_size_bigC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7map_geoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep;ac_map_shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<schunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans4dsjlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7ac_litsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans8sec_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs7qcacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state2qgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6qbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7qent_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5qentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_globalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs:i_q_cmutexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5batchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6QMAX_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6QMAX_GC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_DNBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7ia_litsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC69OSSVerify5KrLib2K53B026RT_rep6CS_ACCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09C69OSSVerify5KrLib2K53B028RT_trans<shadow_avoidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep>av_static_shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9sec_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans:quar_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9dep_avoidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9av_constsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6av_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9av_pchunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9av_schunkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6av_secC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7av_quarC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6av_depC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep5av_iaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9av_shadowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs2NFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs:frame_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs3fszC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_indepC69OSSVerify5KrLib2K53B028RT_state5fs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<fs_cls_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fs_cls_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fss_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs5nbusyC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List6filterC69OSSVerify5KrLib2K53B028RT_state8fss_hintC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs8flags_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs7fl_baseC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith4Znat5Nat2Z3injc69OSSVerify5KrLib2K53B026RT_sep;nth_indep_ZC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z6to_natC47Corelib4Init5Logic8eq_transc69OSSVerify5KrLib2K53B026RT_sep;frame_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep;fs_size_fszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs@frame_addr_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC69OSSVerify5KrLib2K53B028RT_state7CREDIT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs>kFakeStackSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans8fs_avoidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9av_fs_clsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7fs_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep5ART_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep8ac_grantC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep7ac_shadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_prbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep9ac_secmapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep=art_avoid_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9art_avoidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep6ac_fsbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep5av_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep<munch_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026RT_sep@art_avoid_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans=ART_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live_iv (pn : Z * Z) : ivl := (fst pn, fst pn + snd pn).
Definition frame_iv (fk : Z * nat) : ivl := (fst fk, fst fk + fs_size (snd fk) - 8).
Definition fshad_iv (fk : Z * nat) : ivl := (shad (fst fk), shad (fst fk + fs_size (snd fk))).

Definition W_client (Σ : rtsA) (sp : Z) : list ivl :=
  [(sp, USTACK_TOP)] ++ CS_W ++ map live_iv (live Σ) ++ map frame_iv (frames Σ) ++ map fshad_iv (frames Σ).

Lemma not_outside : forall W lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ outside W x.
Proof.
  induction W as [|[lo' hi'] W IH]; intros lo hi x Hin Hx Ho; [exact Hin|]. cbn in Hin, Ho. destruct Ho as [H1 H2].
  destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (H1 Hx)| exact (IH _ _ _ Hin Hx H2)].
Qed.

Lemma outside_app_inv : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH _ _ H2) as [X Y]. split; [split; [exact H1 | exact X]| exact Y].
Qed.

Lemma outside_map_in : forall {X} (f : X -> ivl) l e x, In e l -> fst (f e) <= x < snd (f e) -> ~ outside (map f l) x.
Proof. intros X f l e x Hin Hx. apply (not_outside _ (fst (f e)) (snd (f e))); [|exact Hx]. apply in_map_iff. exists e. destruct (f e); split; reflexivity || exact Hin. Qed.

Ltac cs_pick lo hi := apply (not_outside CS_W lo hi); [unfold CS_W; repeat (first [left; reflexivity | right]) | lia].
Ltac rt_contra lo hi Hn := exfalso; apply Hn; exists lo, hi; split; [unfold RT_STATIC; repeat (first [left; reflexivity | right]) | lia].

Lemma client_static_cover : forall x, client_static x -> ~ outside CS_W x.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_sep ()) [] "p'0h04__x1h12hih27__arithh34__ffh48__varmaph55__with61si001sh71Hh82loh92Hxh:4__p1h;1li011lh<2l0h=2l1h>2l2h?2l3h@2l4hA2l5hB2l6hC2l7hD2l8hE1EhF3HinhG1ehH3l10hI2l9hJ2HnhK1xi021xi031pi041zp%0p&0p;1p;2p;3p;6p;4p;7p;8g00?Yk10;Tg00@[j2`Tg003Sj1cTg000GR0k20:Tg0000j3BTg00AYj13Tg004lj3PTg00B>j14Tg003lj1nTg004Lj3<Tg00Bcj2ATg001cj21Tg001Gj22Tg000gk109Tg00CJk208Tg00Chk107Tg00DFk105Tg00E1k204Tg00ETk103Tg00F6k602Tg00FZk201Tg00<mj2kTg00G<k200Tg00Ghj3~Tg00HGj4{Tg00I9j2KTg002Zj2yTg006aj4gTg002?R1j2TTg00<4R2j2xTg00IXj1jTg005Fj6wTg00J6R3j2vTg00JVj3|Tg00K0j2}Tg00KSj4mTg00L>j7lTg00Lbj7uTg00MFj8fTg00=aj6tTg008Vj4sTg00=Gj4oTg00Mjj3rTg005ck706Tg00NDR4f0R5'y#cp=7g007AR6P6f1R7P5Cgp=6f4R8f3R9f2R:'21175'T'Tp=C1x65p=H129:1175'Tp=5%35#3#3#3#4p=q%45#4#3#4p=Y%45#4#4#3p=R%45#3p=X%35#3#3#jp=?%35#3#4#3p=U%45#4#3#3p=_%35#3#4#4p=M%35#3#3#4#4#4#4#3p=d%35#4#4#3p=^%35#4#4#4p=O%35#4#3#3p=S%35#3#3#4p=[%35#4p=eP8P6P9P:P7P5Ewp=WAP675p=D%35#3#3p=]%45#3#3#3p=Z%35#jp=b119:1275'vp=@%35#3#3#3#4#4#4#4#3p=Q%45#3#3#4p=G%35#3#3#3p=p%45#3#3p=\%45#4p=af7S00f6R;f5R<3PAB89:1k753|p=;AB754p=F1}65p=9P:g00O;R=g00OZR>P>g00P:R?P6P7g00PZP5Cmg00QAR@Flp=:P:P=P>P>P?P6P7g00QaP5CmP@Flp==P:P=P>P>P?P7P5Fup=8P;P=P>P>P?P<P8P9P=P>P>P?P:P7P5GfGfp=>12:7/T5p=iP4P8P9P:P7P5Etp=Eg00RHR49B75p=IP6P6P<P8Cg=B;4129:1175'T'Tp=NP;12<8119:'TP7P5Csp=JP6P8P9P6P:P7P5CoCop=LAP;<8AB9:7;r5p=01175,T:p=hP6P<P8P9P:P7P5K06p=VP9P=P>P>P?P:P7P5Gfp=z&0;5P1g00SFR@/`71`47#c%7:P51`@91`48#cP2P620:66R41675RA;B@RBP7Q00Q00P5DCX16#HX86%7;P7PBP7f9S01Q01P5DCX16#HP2P616:5=B4@P:f:S02Q02P5DCX16Q02#7P51685=B4@P8f<S03Q03P5DCP116<7=B4@P<f=S04Q04P7C5f>S05#7P5Q00/69=B4@f8R@f@S06Q06P8C5g008<S07g00THR1#q#Y#R#X#X#?R2%31#U#_#R#M#?RB'6RCQ01/6<RD5P4%41#d#d#X#?RE%41#U#^#d#X#?RF'6RG%41#M#O#S#[#e#?RH,6FS08%n4S095<4S0:5<4S0;9B4DfBS0<#7P7Q02/6;S0=9P4CP4P0P6P6P6P5P5n2001103000120104104XG4S0>PCf;S0?Q00'6S0@P5DWQ00,DBP4P0P6P6P6P5P7n2001103000120104104XG4S0APCQ03/6@S0BP7DWQ03,D2Q04,D2P2P5fGR@P@Q0?C5Q03,DBfIS0C#7[]9X86P2fFS0DQ0DQ02C5Q0?,DBPBP2Q0CQ0CP5C5fJS0E#7]9X16P2fHS0FQ0FPBC5Q0C%]1#O#Z#_#U#bR@'AQ0CP@P@Q0CC@P3Q0E/1@Q0E,2@fKS0G#7S0HP5Q0G/1@P2P@fLS0IP4162@RCPCP4PC%Q1#M#S#?R0%]1#O#Z#Y#e#?R;'6RD%Q1#M#Z#?RI%Q1#M#G#?RJ'6RK%Q1#M#_#?RL%Q1#M#Y#?RM'6RN%Q1#S#p#?RO%]1#O#G#p#U#bRP'6RQ%Q1#S#S#?RR%]1#O#G#[#U#bRS'6RT%Q1#S#Z#?RU/6BRV%\1#G#G#Y#R#?RW,6FRX%41#U#^#O#O#a#?RY%\1#G#G#R#Z#?RZ'6R[%\1#G#G#R#_#?R\%\1#G#G#R#Y#?R]'6R^%\1#G#G#R#a#a#?R_%41#M#^#X#S#[#?R`'6Ra%41#M#^#X#S#U#?Rb%41#M#O#[#e#R#?Rc'6Rd%41#M#O#[#O#a#?Re/6HRfQ095<4S0J5<4S0K5<4S0L5<4S0M5<4S0N5<4S0O9<4GS0P5<4S0Q5<4S0R5<4S0S5<4S0T5<4Rg5<4RhP4PCG;1F4Cep-0Rig00TmRj#nRk&09jRj20867Rl&076Rm&056Rn20461R1%9@Ro5:nRp&03>RqPn%92==n1RrPnP=P>P>P?P9J02S0U58nPqA8nrpF>201n?R?P5P:g00UYRrg00V9Rp'k2005:=Prpdg00VY=~67C{Rpb3b4b5X06W:115@Ai27:P2P:P:P@C5[[^06^:iP5fMRr/1BPrP7P8O4b2DEW;P5O1Q0G,2@Q0I/A0Q0IP0P0Q0IC@P311r0120rfNS0V#7S0WP5Q0V/10fOS0X#7S0YQ0E1I4AS0ZP7fQRAPAP5DCX16#HX86P@P4P@P5P@fPR9P9P5FNX16P016@0R>,I4R=P@Q0XQ0XP0P4P>P>P4P>16;IRs16JLRt16MORu16PRRv16SURw16WYRx16Z\Ry16]_Rz16ceR{16`bR|Q095<4S0[5<4S0\5<4S0]5<4S0^5<4S0_5<4S0`5<4S0a5<4S0b5<4S0c5<4S0dP4P>G;P=ePkPjPlPmPn%90R=9:n1R}PqPnA=no1RoPqA8no}F>P?Ppb3b4b5X06115012@7P@P:P:P0C5[[^06P5P9P7P8O3b2FJDLO1'KW<P5O1Q0V,20Q0X/A;Q0XP;P;Q0XC@P3119;12;9%7AP511A;P0P;fRS0eP4PCPDP4PDPhP4PDPDP4PDPgP4PDG;F01F4DePkPjPlPmPn%9;R@9:n1RoPqPnA=n=1R=PqA8n=oF>P?Ppb3b4b5X06115;1207P0P:P:P;C5[[^06P5fSR0P7P8O3b2DEW=P5O112;AQ0e/AIQ0ePIPIQ0eC@P3110I12I0fTR=#7P511=IfURo#7S0fP9Q0ZP7fWR}P}P5DCX16#HX86P;P4P;P5P;fVR~P~P5FNX16PI1I4sS0gP;PoPoPIP4P>PsP4PsQ0dP4PsPsP4PsQ0cP4PsG;F0Q0gePkPjPlPmPn%9IS0g9:n1S0hPqPnA=n@1R@PqQ0h98n@F>P?Ppb3b4b5X06115I12;7P;P:P:PIC5[[^06P5P~P7P8O3b2FJDLO1'KW>P5O112I=1AoJPoPJPJPoC@P311~J12J~%7}P511}JPIPJfXS0hP4PCPKP4PKPhP4PDPKP4PKPgP4PKPKP4PKQ0TP4PKG;F0F01F4KePkPjPlPmPn%9JS0i9:n1R;PqPnQ0g==n1R@PqA8n@;F>P?Ppb3b4b5X06115J12I7PIP:P:PJC5[[^06P5fYRIP7P8O3b2DEW?P5O112J}Q0h/ALQ0hPLPLQ0hC@P311IL12LIfZS0g#7P5Q0g/1Lf[R@#7S0jP~Q0ZP7f]S0kQ0kP5DCX16#HX86PJP4PJP5PJf\R;P;P5FNX16PL1I4tS0lPJP@P@PLP4P>PtP4PtQ0dP4PsPtP4PtQ0cP4PtPtP4PtQ0bP4PtG;F0F0Q0lePkPjPlPmPn%9LS0l9:n1S0mPqPnQ0i==n1S0iPqQ0iQ0m58nF>P?Ppb3b4b5X06115L12J7PJP:P:PLC5[[^06P5P;P7P8O3b2FJDLO1'KW@P5O1Q0g,2L1A@MP@PMPMP@C@P311;M12M;Q0k#7P5Q0k/1MPLPMf^S0iP4PCPNP4PNPhP4PDPNP4PNPgP4PKPNP4PNQ0TP4PNPNP4PNQ0SP4PNG;F0F0F01F4NePkPjPlPmPn%9MS0m9:n1S0nPqPnQ0l==n1RJPqQ0n98nJF>P?Ppb3b4b5X06115M12L7PLP:P:PMC5[[^06P5f_RLP7P8O3b2DEWAP5O1Q0k,2MQ0i/AOQ0iPOPOQ0iC@P311LO12OLf`S0n#7P5Q0n/1OfaS0l#7S0oP;Q0ZP7fcS0pQ0pP5DCX16#HX86PMP4PMP5PMfbRJPJP5FNX16PO1I4uS0qPMQ0lQ0lPOP4P>PuP4PuQ0dP4PsPuP4PuQ0cP4PtPuP4PuQ0bP4PuPuP4PuQ0aP4PuG;F0F0F0Q0qePkPjPlPmPn%9OS0q9:n1S0rPqPnQ0m==n1S0mPqQ0mQ0r58nF>P?Ppb3b4b5X06115O12M7PMP:P:POC5[[^06P5PJP7P8O3b2FJDLO1'KWBP5O1Q0n,2OQ0l/APQ0lPPPPQ0lC@P311JP12PJQ0p#7P5Q0p/1PPOPPfdS0mP4PCPQP4PQPhP4PDPQP4PQPgP4PKPQP4PQQ0TP4PNPQP4PQQ0SP4PQPQP4PQQ0RP4PQG;F0F0F0F01F4QePkPjPlPmPn%9PS0r9:n1S0sPqPnQ0q==n1RMPqQ0s98nMF>P?Ppb3b4b5X06115P12O7POP:P:PPC5[[^06P5feROP7P8O3b2DEWCP5O1Q0p,2PQ0m/ARQ0mPRPRQ0mC@P311OR12ROffS0s#7P5Q0s/1RfgS0q#7S0tPJQ0ZP7fiS0uQ0uP5DCX16#HX86PPP4PPP5PPfhRMPMP5FNX16PR1I4vS0vPPQ0qQ0qPRP4P>PvP4PvQ0dP4PsPvP4PvQ0cP4PtPvP4PvQ0bP4PuPvP4PvQ0aP4PvPvP4PvQ0`P4PvG;F0F0F0F0Q0vePkPjPlPmPn%9RS0v9:n1S0wPqPnQ0r==n1S0rPqQ0rQ0w58nF>P?Ppb3b4b5X06115R12P7PPP:P:PRC5[[^06P5PMP7P8O3b2FJDLO1'KWDP5O1Q0s,2RQ0q/ASQ0qPSPSQ0qC@P311MS12SMQ0u#7P5Q0u/1SPRPSfjRPP4PCPTP4PTPhP4PDPTP4PTPgP4PKPTP4PTQ0TP4PNPTP4PTQ0SP4PQPTP4PTQ0RP4PTPTP4PTQ0QP4PTG;F0F0F0F0F01F4TePkPjPlPmPn%9SS0r9:n1S0wPqPnQ0v==n1S0vPqQ0vQ0w58nF>P?Ppb3b4b5X06115S12R7PRP:P:PSC5[[^06P5fkS0vP7P8O3b2DEWIP5O1Q0u,2S1APUPPPUPUPPC@P3Q0v/1UQ0v,2UflRR#7P511RUfmS0w#7PMQ0ZP7foS0xQ0xP5DCX16#HX86PSP4PSP5PSfnS0xQ0xP5FNX16PU1I4wS0yPSQ0wQ0wPUP4P>PwP4PwQ0dP4PsPwP4PwQ0cP4PtPwP4PwQ0bP4PuPwP4PwQ0aP4PvPwP4PwQ0`P4PwPwP4PwQ0_P4PwG;F0F0F0F0F0Q0yePkPjPlPmPn%9US0y9:n1S0zPqPnQ0r==n1S0rPqQ0rQ0z58nF>P?Ppb3b4b5X06115U12S7PSP:P:PUC5[[^06P5Q0xP7P8O3b2FJDLO1'KWHP5O112URPUPBQ0wP4PCPVP4PVPhP4PDPVP4PVPgP4PKPVP4PVQ0TP4PNPVP4PVQ0SP4PQPVP4PVQ0RP4PTPVP4PVQ0QP4PVPVP4PVQ0PP4PVG;F0F0F0F0F0F01F4VePkPjPlPmPnQ0y==n1S0yPqPnQ0U%9B9:n1RS58nPqQ0y=8nSF>P?Ppb3b4b5X06X:i12U5Ah:7BPUP:P:PBC5[[^06^:iP5Q0x,22Q0xP7PoO4b2DEWHP5O1n200110000021110111101b6WIP5O1n200110000021110111101b6WDP5O1n200110000021110111101b6WCP5O1n200110000021110111101b6WBP5O1n200110000021110111101b6WAP5O1n200110000021110111101b6W@P5O1n200110000021110111101b6W?P5O1n200110000021110111101b6W>P5O1n200110000021110111101b6W=P5O1n200110000021110111101b6W<P5O1n200110000021110111101b6W;P5O1n200110000021110111101b6W9Q03P5P7EVW7W9Q05P5P<EVW7P5O1b7P5O1b7WEP5O1Q0=Q0;5B4Q07Q0@9P4GQ0@Q0:5B4fD#7P5Q0B9P4GP4Q0>PGQ04Q01'6R<P5DWQ01,DFP4Q0APGQ05Q02'6R2P7DWQ05,DEf?RB,DEPEP5Q0CQ0CQ04C5Q05,DFQ0H[]9X86PEQ0FQ0FQ03C5Q04,DFPFPEQ0GQ0GP5C5Q0I#7]9X16PEQ0EQ0EPFC5PEPFQ0GP4PCPGP4PGPhP4PDPGP4PGPgP4PKPGP4PGQ0TP4PNPGP4PGQ0SP4PQPGP4PGQ0RP4PTPGP4PGQ0QP4PVPGP4PGQ0PP4PGPGP4PGQ0OP4PGG;F0F0F0F0F0F0F01F4GePkPjPlPmPn%9E==n1%9FRU9:n158nRSPqPSCzP?Ppb3b4b5X06PEP5P5PFC5PEP7P7PFC5[^06P5Q0IP7O2b2DEW9Q05P5P7EVW7W9Q06P5Q00EVW7P5O1b7P5O1b7WEP5O1Q0BQ0:5B4Q07Q08=P4<Q099B4<Q0D#7P5Q08=P42P4Q0>Q08Q0?,6BP5DWQ0?,DHP4Q0AQ08Q06Q03'6P7DWQ06,DFfA,DFPFP5Q0GQ0GPBC5Q06,DH%7r[]9X86PFQ0EQ0EQ05C51DHBPHPFPrPrP5C5Q0W]9X16PFQ0IQ0IPHC51ArWPrPWPWPrC@P3Q0V/1WQ0V,2WQ0YP5Q0X/1WPFPWP9P4PCPXP4PXPhP4PDPXP4PXPgP4PKPXP4PXQ0TP4PNPXP4PXQ0SP4PQPXP4PXQ0RP4PTPXP4PXQ0QP4PVPXP4PXQ0PP4PGPXP4PXQ0OP4PXPXP4PXQ0NP4PXG;F0F0F0F0F0F0F0F01F4XePkPjPlPmPn%9WRr9:n1RBPqPnA=nU1RUQ0U58nPqA8nUBF>P?Ppb3b4b5X06X:i115WAiF7:PFP:P:PWC5[[^06^:iP511AHPAP7P8O4b2DEW;P5O1Q0X,2W1A9YP9PYPYP9C@P311AY12YAQ0e#7P5Q0e/1Y%70Q0VQ0ZP7PoPoP5DCX16#HX86PWP4PWP5PWP=P=P5FNX16PY1I4xRAPWP0P0PYP4P>PxP4PxQ0dP4PsPxP4PxQ0cP4PtPxP4PxQ0bP4PuPxP4PxQ0aP4PvPxP4PxQ0`P4PwPxP4PxQ0_P4PxPxP4PxQ0^P4PxG;F0F0F0F0F0F0PAePkPjPlPmPn%9YRA9:n1R9PqPnA=nr1RrPqA8nr9F>P?Ppb3b4b5X06115Y12W7PWP:P:PYC5[[^06P5P=P7P8O3b2FJDLO1'KW<P5O1Q0e,2Y1A0ZP0PZPZP0C@P311=Z12Z=Q0fP511oZPYPZP~P4PCP[P4P[PhP4PDP[P4P[PgP4PKP[P4P[Q0TP4PNP[P4P[Q0SP4PQP[P4P[Q0RP4PTP[P4P[Q0QP4PVP[P4P[Q0PP4PGP[P4P[Q0OP4PXP[P4P[Q0NP4P[P[P4P[Q0MP4P[G;F0F0F0F0F0F0F0F0F01F4[ePkPjPlPmPn%9ZR09:n1RWPqPnA=nA1RAPqA8nAWF>P?Ppb3b4b5X06115Z12Y7PYP:P:PZC5[[^06P5P}P7P8O3b2DEW=P5O112Zo1A~\P~P\P\P~C@P311}\12\}Q0h#7P5Q0h/1\%7IP=Q0ZP7P@P@P5DCX16#HX86PZP4PZP5PZQ0gQ0gP5FNX16P\1I4yR=PZPIPIP\P4P>PyP4PyQ0dP4PsPyP4PyQ0cP4PtPyP4PyQ0bP4PuPyP4PyQ0aP4PvPyP4PyQ0`P4PwPyP4PyQ0_P4PxPyP4PyQ0^P4PyPyP4PyQ0]P4PyG;F0F0F0F0F0F0F0P=ePkPjPlPmPn%9\R=9:n1R}PqPnA=n01R0PqA8n0}F>P?Ppb3b4b5X06115\12Z7PZP:P:P\C5[[^06P5Q0gP7P8O3b2FJDLO1'KW>P5O1Q0h,2\1AI]PIP]P]PIC@P3Q0g/1]Q0g,2]Q0jP511@]P\P]P;P4PCP^P4P^PhP4PDP^P4P^PgP4PKP^P4P^Q0TP4PNP^P4P^Q0SP4PQP^P4P^Q0RP4PTP^P4P^Q0QP4PVP^P4P^Q0PP4PGP^P4P^Q0OP4PXP^P4P^Q0NP4P[P^P4P^Q0MP4P^P^P4P^Q0LP4P^G;F0F0F0F0F0F0F0F0F0F01F4^ePkPjPlPmPn%9]RI9:n1RZPqPnA=n=1R=PqA8n=ZF>P?Ppb3b4b5X06115]12\7P\P:P:P]C5[[^06P5Q0kP7P8O3b2DEW?P5O112]@1A;_P;P_P_P;C@P3Q0k/1_Q0k,2_Q0i#7P5Q0i/1_%7LQ0gQ0ZP7Q0lQ0lP5DCX16#HX86P]P4P]P5P]Q0nQ0nP5FNX16P_1I4zR;P]PLPLP_P4P>PzP4PzQ0dP4PsPzP4PzQ0cP4PtPzP4PzQ0bP4PuPzP4PzQ0aP4PvPzP4PzQ0`P4PwPzP4PzQ0_P4PxPzP4PzQ0^P4PyPzP4PzQ0]P4PzPzP4PzQ0\P4PzG;F0F0F0F0F0F0F0F0P;ePkPjPlPmPn%9_R;9:n1R@PqPnA=nI1RIPqA8nI@F>P?Ppb3b4b5X06115_12]7P]P:P:P_C5[[^06P5Q0nP7P8O3b2FJDLO1'KW@P5O1Q0i,2_1AL`PLP`P`PLC@P3Q0n/1`Q0n,2`Q0oP5Q0l/1`P_P`PJP4PCPaP4PaPhP4PDPaP4PaPgP4PKPaP4PaQ0TP4PNPaP4PaQ0SP4PQPaP4PaQ0RP4PTPaP4PaQ0QP4PVPaP4PaQ0PP4PGPaP4PaQ0OP4PXPaP4PaQ0NP4P[PaP4PaQ0MP4P^PaP4PaQ0LP4PaPaP4PaQ0KP4PaG;F0F0F0F0F0F0F0F0F0F0F01F4aePkPjPlPmPn%9`RL9:n1R]PqPnA=n;1R;PqA8n;]F>P?Ppb3b4b5X06115`12_7P_P:P:P`C5[[^06P5Q0pP7P8O3b2DEWAP5O1Q0l,2`1AJbPJPbPbPJC@P3Q0p/1bQ0p,2bQ0m#7P5Q0m/1b%7OQ0nQ0ZP7Q0qQ0qP5DCX16#HX86P`P4P`P5P`Q0sQ0sP5FNX16Pb1I4|RJP`POPOPbP4P>P|P4P|Q0dP4PsP|P4P|Q0cP4PtP|P4P|Q0bP4PuP|P4P|Q0aP4PvP|P4P|Q0`P4PwP|P4P|Q0_P4PxP|P4P|Q0^P4PyP|P4P|Q0]P4PzP|P4P|Q0\P4P{P|P4P|Q0[P4P|P|P4P|Q09P4P|G;F0F0F0F0F0F0F0F0F0F0PJePkPjPlPmPn%9bRJ9:n1R|PqPnA=nL1RLPqA8nL|F>P?Ppb3b4b5X06115b12`7P`P:P:PbC5[[^06P5Q0sP7P8O3b2FJDLO1'KWBP5O1Q0m,2b1AOcPOPcPcPOC@P3Q0s/1cQ0s,2cQ0tP5Q0q/1cPbPcPMP4PCPdP4PdPhP4PDPdP4PdPgP4PKPdP4PdQ0TP4PNPdP4PdQ0SP4PQPdP4PdQ0RP4PTPdP4PdQ0QP4PVPdP4PdQ0PP4PGPdP4PdQ0OP4PXPdP4PdQ0NP4P[PdP4PdQ0MP4P^PdP4PdQ0LP4PaPdP4PdQ0KP4PdPdP4PdQ0JP4PdG;F0F0F0F0F0F0F0F0F0F0F0F01F4dePkPjPlPmPn%9cRO9:n1R`PqPnA=nJ1RJPqA8nJ`F>P?Ppb3b4b5X06115c12b7PbP:P:PcC5[[^06P5Q0uP7P8O3b2DEWCP5O1Q0q,2c1AMePMPePePMC@P3Q0u/1eQ0u,2e%7PP511PeQ0v#7Q0sQ0ZP7Q0wQ0wP5DCX16#HX86PcP4PcP5PcPRPRP5FNX16Pe1I4{R3PcQ0vQ0vPeP4P>P{P4P{Q0dP4PsP{P4P{Q0cP4PtP{P4P{Q0bP4PuP{P4P{Q0aP4PvP{P4P{Q0`P4PwP{P4P{Q0_P4PxP{P4P{Q0^P4PyP{P4P{Q0]P4PzP{P4P{Q0\P4P{P{P4P{Q0[P4P{G;F0F0F0F0F0F0F0F0F0P3ePkPjPlPmPn%9eR39:n1R{PqPnA=nO1ROPqA8nO{F>P?Ppb3b4b5X06115e12c7PcP:P:PeC5[[^06P5PRP7P8O3b2FJDLO1'KWDP5O112ePPePHQ0vP4PCPfP4PfPhP4PDPfP4PfPgP4PKPfP4PfQ0TP4PNPfP4PfQ0SP4PQPfP4PfQ0RP4PTPfP4PfQ0QP4PVPfP4PfQ0PP4PGPfP4PfQ0OP4PXPfP4PfQ0NP4P[PfP4PfQ0MP4P^PfP4PfQ0LP4PaPfP4PfQ0KP4PdPfP4PfQ0JP4PfPfP4PfQ09P4PfG;F0F0F0F0F0F0F0F0F0F0F0F0F01F4fePkPjPlPmPnA=n31R3PqPnQ0U%9H9:n1R158nPqA8n31F>P?Ppb3b4b5X06X:i12e5Ah:7HPeP:P:PHC5[[^06^:iP512FRPRP7Q0XO4b2DEWDP5O1n200110000021110111101b6WCP5O1n200110000021110111101b6WBP5O1n200110000021110111101b6WAP5O1n200110000021110111101b6W@P5O1n200110000021110111101b6W?P5O1n200110000021110111101b6W>P5O1n200110000021110111101b6W=P5O1n200110000021110111101b6W<P5O1n200110000021110111101b6W;P5O1n200110000021110111101b6W9Q06P5P7EVW7W9Q0<P5Q01EVW7P5O1b7P5O1b7WEP5O1Q099B42g007_Q0F#7P5n010000000W7P5O1n200100000021100010000W7P5O1n200100000021100011000W7P5O1n200100000021100011000W9WFP7P5O2n2001000000121000000W7X16P7P5O2n2001000000121102000W7X86P7P5O2n2001000000121102000WJWFP7P5O2n2001000000121000000W7XK6o"). Qed.

(* [comment removed for export] *)
Lemma W_client_cover : forall Σ sp x, aclient (live Σ) (frames Σ) sp x -> ~ outside (W_client Σ sp) x.
Proof.
  intros Σ sp x H Ho. unfold W_client in Ho.
  apply outside_app_inv in Ho as [H1 Ho]. apply outside_app_inv in Ho as [H2 Ho]. apply outside_app_inv in Ho as [H3 Ho].
  apply outside_app_inv in Ho as [H4 H5].
  destruct H as [H|[H|[H|[H|H]]]].
  - cbn in H1. exact (proj1 H1 H).
  - exact (client_static_cover x H H2).
  - destruct H as (p & n & Hin & Hx). exact (outside_map_in live_iv _ (p, n) x Hin ltac:(cbn; lia) H3).
  - destruct H as (f & k & Hin & Hx). exact (outside_map_in frame_iv _ (f, k) x Hin ltac:(cbn; lia) H4).
  - destruct H as (f & k & Hin & Hx). exact (outside_map_in fshad_iv _ (f, k) x Hin ltac:(cbn; lia) H5).
Qed.

(* [comment removed for export] *)
Lemma munch_client : forall Σ sp (m m' : mem),
  (forall a : word, ~ aclient (live Σ) (frames Σ) sp (bv_unsigned a) -> m' a = m a) -> munch (W_client Σ sp) m m'.
Proof. intros Σ sp m m' H x Hx. apply H. intros Hc. exact (W_client_cover Σ sp _ Hc Hx). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dsj_map : forall {X} (f : X -> ivl) l a n, Forall (fun e => a + n <= fst (f e) \/ snd (f e) <= a) l -> disjoint_from (map f l) a n.
Proof.
  intros X f l a n H. induction l as [|e l IH]; [exact I|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map disjoint_from].
  cbv beta in H1. revert H1. destruct (f e) as [lo hi]. cbn. intros H1. split; [exact H1 | exact (IH H2)].
Qed.

Lemma avoid_client_intro : forall Σ sp a n, a + n <= sp -> disjoint_from CS_W a n ->
  Forall (fun pn => a + n <= fst pn \/ fst pn + snd pn <= a) (live Σ) ->
  Forall (fun fk => a + n <= fst fk \/ fst fk + fs_size (snd fk) - 8 <= a) (frames Σ) ->
  Forall (fun fk => a + n <= shad (fst fk) \/ shad (fst fk + fs_size (snd fk)) <= a) (frames Σ) ->
  disjoint_from (W_client Σ sp) a n.
Proof.
  intros Σ sp a n H1 H2 H3 H4 H5. unfold W_client.
  apply dsj_app; [cbn; split; [left; exact H1 | exact I]|]. apply dsj_app; [exact H2|].
  apply dsj_app; [apply dsj_map; exact H3|]. apply dsj_app; apply dsj_map; assumption.
Qed.

(* [comment removed for export] *)
Lemma dsj_CS_out : forall a n, a + n <= 0x10000 \/ SEGTOP_A <= a -> disjoint_from CS_W a n.
Proof. intros a n H. unfold SEGTOP_A in H. cbn. repeat split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Geo.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma geo_wf : rt_wf Σ.
Proof using Σ m HA. exact (ART_wf Σ m HA). Qed.
Lemma geo_layout : layout_ok L.
Proof using Σ m HA. exact (proj1 geo_wf). Qed.

(* [comment removed for export] *)
Lemma geo_grant : forall b n, In (b, n) (startup_grants L) -> grant_ok L b n.
Proof using Σ m HA.
  intros b n Hin. pose proof geo_layout as HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & G1 & _ & _ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  unfold startup_grants in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; assumption.
Qed.

Lemma geo_apart : forall i j g1 g2, (i < j)%nat -> nth_error (startup_grants L) i = Some g1 -> nth_error (startup_grants L) j = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof using Σ m HA. pose proof geo_layout as HL. unfold layout_ok in HL. repeat match type of HL with _ /\ ?R => destruct HL as [_ HL] end. exact HL. Qed.

(* [comment removed for export] *)
Lemma geo_prb : l_PRB L <= SB /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000 /\ SB mod 2 ^ 16 = 0.
Proof using Σ m HA.
  pose proof geo_layout as HL. unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & Hsb & Hsb2 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma geo_live : forall p n, In (p, n) (live Σ) ->
  (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n)
     /\ p = p_ubeg SB c i n /\ p_abeg SB c i + 16 <= p /\ p + n <= p_abeg SB c i + ClassSize c
     /\ rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + kUserCap /\ 0 <= n)
  \/ (exists s, In s (sec Σ) /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ s_mb s + 6144 + n <= s_mb s + smsz n /\ 0 <= n).
Proof using Σ m HA.
  intros p n Hin. pose proof geo_wf as (_ & HR & HV & HS & _). destruct HV as (_ & _ & HVin & _).
  destruct (HVin p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - left. exists c, i. split; [exact Hc|]. split; [exact Hn|]. split; [reflexivity|].
    destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & _ & W3 & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (nth_error_In _ _ Hn) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, rb, kUserCap in *.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 16 <= rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    repeat split; lia.
  - right. exists s. destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg. repeat split; try assumption; try reflexivity; lia.
Qed.

End Geo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sep.
Variables (Σ : rtsA) (m : mem) (sp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : rtA_sp0 Σ - STACK_WIN <= sp.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_client Σ sp).

(* [comment removed for export] *)
Lemma sep_frame : forall f k, In (f, k) (frames Σ) -> l_FSB L + 0x9000 <= f /\ f + fs_size k <= l_FSB L + 0xb09000 /\ 0 < fs_size k.
Proof using Σ m HA.
  intros f k Hin. destruct (rta_frame_in Σ m f k HA Hin) as (Hk & H1 & H2). split; [exact H1|]. split; [exact H2|].
  unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma sep_fshad : forall f k, In (f, k) (frames Σ) -> SHB <= shad f /\ shad (f + fs_size k) <= K_HIGH_SHADOW_hi.
Proof using Σ m HA.
  intros f k Hin. destruct (sep_frame f k Hin) as (H1 & H2 & H3). pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  unfold l_ACEIL, STACK_WIN in G3. pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi in *.
  unfold shad, K_HIGH_SHADOW_hi, SHB. split; [pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); lia|].
  assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma sep_fshad_app : forall a n, (a + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) ->
  Forall (fun fk => a + n <= shad (fst fk) \/ shad (fst fk + fs_size (snd fk)) <= a) (frames Σ).
Proof using Σ m HA.
  intros a n H. apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_fshad f k Hin) as [X Y].
  unfold K_LOW_SHADOW_lo, SHB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma sep_stack : forall a n, a + n <= l_ACEIL L -> a + n <= sp.
Proof using Σ sp Hsp. intros a n H. unfold l_ACEIL, rtA_sp0 in *. lia. Qed.

(* [comment removed for export] *)
Lemma ac_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros a n H1 H2 H3. pose proof (rta_sp0_range Σ m HA) as Hr. unfold rtA_sp0 in Hr.
  apply avoid_client_intro; [unfold rtA_sp0, STACK_WIN, SEGTOP_A in *; lia | exact H3 | | |].
  - apply Forall_forall. intros [p n'] Hin. cbn [fst snd]. pose proof (rta_live_range Σ m p n' HA Hin) as (_ & _ & X). unfold SEGTOP_A in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
    unfold SEGTOP_A in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_fshad f k Hin) as [X _]. unfold SHB, SEGTOP_A in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros b gn a n Hin HP HF H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn' & -> & X1 & X5)].
    + unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & _ & _ & HG). pose proof (proj1 (Forall_forall _ _) HG (b, gn) Hin) as Ha.
      cbn [fst snd] in Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _). unfold apart in HF. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros lo hi a n Hl Hh H0 H47 H1 H2 HF. pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_lo in *.
  assert (Hs : shad hi <= 2 ^ 44 + SHB) by (unfold shad; assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (Hs0 : SHB <= shad lo) by (unfold shad; pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)); lia).
  apply avoid_client_intro; [unfold rtA_sp0, STACK_WIN, SHB in *; lia | apply dsj_CS_out; unfold SHB, SEGTOP_A in *; lia | | |].
  - apply Forall_forall. intros [p n'] Hin. cbn [fst snd]. pose proof (rta_live_range Σ m p n' HA Hin) as (X1 & X2 & _).
    destruct (geo_live Σ m HA p n' Hin) as [(c & i & Hc & _ & _ & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs' & _ & Hn' & -> & Y1 & Y5)].
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
      pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs') as (_ & (_ & _ & _ & G4 & _) & _). unfold s_ubeg, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
      rewrite <- Hn' in Y1. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (HF f k Hin) as [X|X]; [left | right];
      unfold shad in *; [ assert (hi / 8 <= f / 8) by (apply Z.div_le_mono; lia) | assert ((f + fs_size k) / 8 <= lo / 8) by (apply Z.div_le_mono; lia) ]; lia.
Qed.

(* [comment removed for export] *)
Lemma ac_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros a n H1 H2 HL. pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & Hn' & -> & _)|(s & Hs & _ & Hn' & -> & X1 & X5)]; [exact (HL c i n' Hc Hn')|].
    pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & Ha & _). unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _).
    pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros k0 s0 a n Hk0 H1 H2 HU. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
  pose proof (proj1 (Forall_forall _ _) HSF s0 (nth_error_In _ _ Hk0)) as (_ & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & _).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)].
    + pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (Nat.eq_dec k k0) as [->|Hne].
      * rewrite Hk0 in Hk. injection Hk as <-. rewrite <- Hn'. exact (HU Hq).
      * pose proof (HSP k k0 s s0 Hk Hk0 Hne) as Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _). unfold apart in Hf. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 ->
  (forall f k, In (f, k) (frames Σ) -> a + n <= f \/ f + fs_size k - 8 <= a) -> disjoint_from W a n.
Proof using Σ m sp HA Hsp.
  intros a n H1 H2 HF. pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn' & -> & X1 & X5)].
    + pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha.
      cbn [fst snd] in Ha. unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & _ & Ha & _). unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. exact (HF f k Hin').
Qed.

End Sep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Comp.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
(* [comment removed for export] *)
Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
  (hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> disjoint_from W a n.
Hypothesis R_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Hypothesis R_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.

(* [comment removed for export] *)
Lemma slot_geo : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + r_muser (pr Σ c) /\ r_muser (pr Σ c) <= kUserCap
  /\ 32 <= ClassSize c /\ ClassSize c mod 32 = 0.
Proof using Σ m HA.
  intros c i st Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  unfold p_abeg, rb in *.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia). repeat split; lia.
Qed.

Lemma slot_apart : forall c i c' i' st st', 1 <= c <= 31 -> 1 <= c' <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  nth_error (r_st (pr Σ c')) i' = Some st' -> (c <> c' \/ i <> i') ->
  p_abeg SB c i + ClassSize c <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= p_abeg SB c i.
Proof using Σ m HA.
  intros c i c' i' st st' Hc Hc' Hn Hn' Hne.
  pose proof (slot_geo c i st Hc Hn) as (A1 & A2 & A3 & _). pose proof (slot_geo c' i' st' Hc' Hn') as (B1 & B2 & B3 & _).
  destruct (Z.eq_dec c c') as [<-|Hcc].
  - destruct Hne as [Hne|Hne]; [lia|]. unfold p_abeg. pose proof (ClassSize_range c Hc) as (Hcs & _).
    destruct (Nat.lt_ge_cases i i') as [Hl|Hl].
    + left. assert (Z.of_nat i * ClassSize c + ClassSize c <= Z.of_nat i' * ClassSize c).
      { replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
    + right. assert (Z.of_nat i' * ClassSize c + ClassSize c <= Z.of_nat i * ClassSize c).
      { replace (Z.of_nat i' * ClassSize c + ClassSize c) with ((Z.of_nat i' + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
  - unfold rb, kUserCap in *. lia.
Qed.

(* [comment removed for export] *)
Lemma live_in_slot : forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
  p_abeg SB c i + rz_size n' = p_ubeg SB c i n' /\ 16 <= rz_size n' /\ rz_size n' + n' <= ClassSize c /\ 0 <= n'.
Proof using Σ m HA.
  intros c i n' Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
  split; [reflexivity|]. split; [|lia].
  unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n') ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ac_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> p_abeg SB c i <= a ->
  a + n <= p_abeg SB c i + ClassSize c ->
  (forall n', st = CkAlloc n' -> a + n <= p_ubeg SB c i n') -> disjoint_from W a n.
Proof using Σ m W HA R_prb.
  intros c i st a n Hc Hn H1 H2 HU. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & _).
  pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  apply R_prb; [unfold rb in *; lia | unfold rb, kUserCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
  intros c' i' n' Hc' Hn'. destruct (Z.eq_dec c c') as [<-|Hne]; [destruct (Nat.eq_dec i i') as [<-|Hne]|].
  - rewrite Hn in Hn'. injection Hn' as ->. left. exact (HU n' eq_refl).
  - destruct (slot_apart c i c i' st (CkAlloc n') Hc Hc' Hn Hn' (or_intror Hne)) as [X|X];
      pose proof (live_in_slot c i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
  - destruct (slot_apart c i c' i' st (CkAlloc n') Hc Hc' Hn Hn' (or_introl Hne)) as [X|X];
      pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
Qed.

(* [comment removed for export] *)
Fixpoint dsjb (V : list ivl) (a n : Z) : bool :=
  match V with [] => true | (lo, hi) :: V' => ((a + n <=? lo) || (hi <=? a)) && dsjb V' a n end.
Lemma dsjb_sound : forall V a n, dsjb V a n = true -> disjoint_from V a n.
Proof using.
  induction V as [|[lo hi] V IH]; intros a n H; [exact I|]. cbn [dsjb] in H. apply andb_prop in H as [H1 H2].
  split; [|exact (IH _ _ H2)]. apply orb_prop in H1 as [X|X]; [left; apply Z.leb_le; exact X | right; apply Z.leb_le; exact X].
Qed.
Definition img_ok (r : Z * Z) : bool := ((0x10000 <=? fst r) && (fst r + snd r <=? SEGTOP_A) && dsjb CS_W (fst r) (snd r))%bool.
Lemma ac_lits : forall l, forallb img_ok l = true -> dsjl W l.
Proof using W R_img.
  intros l H. apply Forall_forall. intros [a n] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. unfold img_ok in X.
  cbn [fst snd] in *. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
  exact (R_img a n X1 X2 (dsjb_sound _ _ _ X3)).
Qed.

(* [comment removed for export] *)
Lemma ac_T : forall a n, l_T L <= a -> a + n <= l_T L + 4096 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_T L) 4096); [unfold startup_grants; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_TCX : forall a n, l_TCX L <= a -> a + n <= l_TCX L + 0x10000 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_TCX L) 0x10000); [unfold startup_grants; right; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 3 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DTV : forall a n, l_DTV L <= a -> a + n <= l_DTV L + 4096 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_DTV L) 4096); [unfold startup_grants; right; right; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 4 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_PAB : forall a n, l_PAB L <= a -> a + n <= l_PAB L + 0x800000 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_PAB L) 0x800000); [unfold startup_grants; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 1 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 1 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DNB : forall a n, l_DNB L <= a -> a + n <= l_DNB L + 0x100000 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_DNB L) 0x100000); [unfold startup_grants; do 6 right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 5 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.
Lemma ac_SSB : forall a n, l_SSB L <= a -> a + n <= l_SSB L + 0x800000 -> disjoint_from W a n.
Proof using Σ m W HA R_grant.
  intros a n H1 H2. apply (R_grant (l_SSB L) 0x800000); [unfold startup_grants; do 7 right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 5 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.

Lemma av_consts : consts_avoid W L.
Proof using Σ m W HA R_img R_grant.
  unfold consts_avoid, consts_rngs. unfold_consts.
  repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply R_img; [lia | unfold SEGTOP_A; lia | apply dsjb_sound; vm_compute; reflexivity] | apply ac_T; lia | apply ac_TCX; lia ] |]).
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma av_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W (l_T L) c.
Proof using Σ m W HA R_grant R_shad R_prb.
  intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  split; [|unfold pclass_avoid, pc_addr, cacheT; apply ac_T; lia].
  unfold reg_avoid. split; [|split].
  -  apply R_prb; [unfold rinfo, RIS_of; lia | unfold rinfo, RIS_of; lia|].
    intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
    pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). right. unfold rinfo, RIS_of, rb, kUserCap in *.
    assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  -  apply R_prb; [unfold fa, rb; lia | unfold fa, rb, kFaCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
    intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
    pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). unfold fa, rb, kUserCap, kFaCap in *.
    destruct (Z.eq_dec c c') as [<-|Hne]; [right; lia|]. destruct (Z_lt_le_dec c c'); [left | right]; lia.
  - 
    set (auser := ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    assert (Hau : auser mod 8 = 0).
    { unfold auser. rewrite Z.mul_comm. apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide in Hm32; [|lia].
      apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm32]. }
    assert (Hrb : rb SB c mod 8 = 0) by (unfold rb; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
      [apply Z.mod_divide in P3; [|lia]; apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3] | exists (c * 2 ^ 29); lia]).
    assert (Hmu : r_muser (pr Σ c) mod 8 = 0) by (unfold kUMap in W2; apply Z.mod_divide; [lia|]; apply Z.mod_divide in W2; [|lia];
      apply (Z.divide_trans 8 0x40000); [exists 0x8000; reflexivity | exact W2]).
    apply (R_shad (rb SB c + auser) (rb SB c + r_muser (pr Σ c))).
    + rewrite Z.add_mod by lia. rewrite Hrb, Hau. reflexivity.
    + rewrite Z.add_mod by lia. rewrite Hrb, Hmu. reflexivity.
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _).
      unfold rb. assert (0 <= auser) by (unfold auser; apply Z.mul_nonneg_nonneg; lia). lia.
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
      pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + lia.
    + assert (shad (rb SB c + auser) + Z.max 0 ((r_muser (pr Σ c) - auser) / 8) = shad (rb SB c + r_muser (pr Σ c))); [|lia].
      unfold shad. rewrite Z.max_r by (apply Z.div_pos; lia).
      replace (rb SB c + r_muser (pr Σ c)) with ((rb SB c + auser) + (r_muser (pr Σ c) - auser)) by lia.
      assert (E1 : (rb SB c + auser) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hrb, Hau; reflexivity).
      assert (E2 : (r_muser (pr Σ c) - auser) mod 8 = 0) by (rewrite Zminus_mod, Hmu, Hau; reflexivity).
      apply Z.mod_divide in E1, E2; try (clear; lia). destruct E1 as [q1 E1]. destruct E2 as [q2 E2]. rewrite E1, E2.
      replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia.
    + intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
      pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma mod8_of : forall z k, 0 < k -> z mod k = 0 -> (8 | k) -> z mod 8 = 0.
Proof using. intros z k Hk H D. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. exact (Z.divide_trans _ _ _ D H). Qed.

Lemma abeg_mod8 : forall c i, 1 <= c <= 31 -> p_abeg SB c i mod 8 = 0.
Proof using Σ m HA.
  intros c i Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm).
  unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
  - apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3].
  - exists (c * 2 ^ 29). lia.
  - apply Z.divide_mul_r. apply Z.mod_divide in Hm; [|lia]. apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm].
Qed.

(* [comment removed for export] *)
Lemma ac_slot_shad : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i) + ClassSize c / 8 -> disjoint_from W a n.
Proof using Σ m W HA R_shad.
  intros c i st a n Hc Hn H1 H2. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
  pose proof (abeg_mod8 c i Hc) as M1. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  assert (M2 : ClassSize c mod 8 = 0) by (apply (mod8_of _ 32 ltac:(lia) S5); exists 4; reflexivity).
  assert (E : shad (p_abeg SB c i + ClassSize c) = shad (p_abeg SB c i) + ClassSize c / 8).
  { unfold shad. apply Z.mod_divide in M1, M2; try (clear; lia). destruct M1 as [q1 E1]. destruct M2 as [q2 E2].
    rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
  apply (R_shad (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [exact M1 | rewrite Z.add_mod, M1, M2 by lia; reflexivity | | | exact H1 | rewrite E; exact H2 | |].
  - unfold rb in S1. lia.
  - pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
    pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma rz_facts : forall n, rz_size n mod 16 = 0 /\ 16 <= rz_size n.
Proof using.
  intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
  split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma slot_room : forall c n, 1 <= c <= 31 -> 0 <= n -> rz_size n + n <= ClassSize c ->
  rz_size n + ru8 n <= ClassSize c /\ rz_size n + 16 <= ClassSize c.
Proof using.
  intros c n Hc Hn H. pose proof (ClassSize_range c Hc) as (Hcs & Hm). pose proof (rz_facts n) as (R1 & R2).
  assert (Hd : exists k, ClassSize c - rz_size n = 16 * k).
  { exists ((ClassSize c - rz_size n) / 16). pose proof (Z.div_mod (ClassSize c - rz_size n) 16 ltac:(lia)) as D.
    assert ((ClassSize c - rz_size n) mod 16 = 0); [|lia]. rewrite Zminus_mod. rewrite R1.
    replace (ClassSize c mod 16) with 0; [reflexivity|]. symmetry. (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hm; [|lia]; apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact Hm]). }
  destruct Hd as [k Hk]. unfold ru8. split.
  - assert (8 * ((n + 7) / 8) <= 16 * k); [|lia]. assert ((n + 7) / 8 < 2 * k + 1); [|lia]. apply Z.div_lt_upper_bound; lia.
  - destruct (Z_le_dec n 0) as [Hz|Hz].
    + assert (n = 0) by lia. subst n. unfold rz_size, rz_log in *. cbn in *. lia.
    + lia.
Qed.

Lemma ushadow_len : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = ru8 n / 8.
Proof using.
  intros n Hn. unfold ushadow, ru8. rewrite length_app, repeat_length. replace (8 * ((n + 7) / 8) / 8) with ((n + 7) / 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length].
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite E in D. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
    replace (n + 7) with ((n / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). cbn [Z.of_nat Pos.of_succ_nat].
    replace (n + 7) with ((n / 8 + 1) * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1) 8) by lia. lia.
Qed.

Lemma av_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof using Σ m W HA R_shad R_prb.
  intros c i st Hc Hn. unfold pchunk_avoid. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
  assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
  { intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
  pose proof (abeg_mod8 c i Hc) as M1. apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
  apply Z.mod_divide in S5; [|lia]. destruct S5 as [s1 E4].
  assert (ES : ClassSize c / 8 = 4 * s1) by (rewrite E4; replace (s1 * 32) with ((4 * s1) * 8) by ring; apply Z.div_mul; lia).
  assert (EA : shad (p_abeg SB c i) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
  destruct st as [|n|n|].
  - apply (ac_slot_shad c i CkIdle); [exact Hc | exact Hn | lia | lia].
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
    pose proof (ushadow_len n F2) as U. rewrite length_app, Nat2Z.inj_add, farun_len, U.
    apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
    assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
    assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
    split; [apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
    split; [intros Hr; apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
    split; [apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | lia | rewrite ER, EU, ES, EA; lia]|].
    assert (EB : shad (p_abeg SB c i + rz_size n + ru8 n) = a0 + 2 * r1 + u0 + SHB).
    { unfold shad. rewrite E1, E2, E3. replace (a0 * 8 + r1 * 16 + u0 * 8) with ((a0 + 2 * r1 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
    assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
    { rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
    apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | rewrite EB, EA; lia | rewrite EB, EC, ES, EA; lia].
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
    rewrite !length_app, !Nat2Z.inj_add, !farun_len, fdrun_len.
    apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
    assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
    assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
    assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
    { rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
    split; [apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
    split; [intros Hr; apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
    apply (ac_slot_shad c i (CkQuar n)); [exact Hc | exact Hn | lia | rewrite ER, EU, EC, ES, EA; lia].
  - apply (ac_slot_shad c i CkBatch); [exact Hc | exact Hn | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma map_geo : forall k s, nth_error (sec Σ) k = Some s ->
  64513 <= s_n s <= 0x8000000 /\ grant_ok L (s_mb s) (smsz (s_n s)) /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
  /\ smsz (s_n s) mod 4096 = 0 /\ 6144 + ru8 (s_n s) <= smsz (s_n s).
Proof using Σ m HA.
  intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & G & _ & Hf & _).
  split; [exact Hn|]. split; [exact G|]. split; [exact Hf|]. split.
  - unfold smsz, pg_up. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
  - unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ac_map_shad : forall k s a n, nth_error (sec Σ) k = Some s ->
  shad (s_mb s) <= a -> a + n <= shad (s_mb s) + smsz (s_n s) / 8 -> disjoint_from W a n.
Proof using Σ m W HA R_shad.
  intros k s a n Hk H1 H2. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & _).
  assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  assert (M3 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) M2); exists 512; reflexivity).
  assert (E : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8).
  { unfold shad. apply Z.mod_divide in M1, M3; try (clear; lia). destruct M1 as [q1 E1]. destruct M3 as [q2 E2].
    rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
  apply (R_shad (s_mb s) (s_mb s + smsz (s_n s))); [exact M1 | rewrite Z.add_mod, M1, M3 by lia; reflexivity | lia | | exact H1 | rewrite E; exact H2 | |].
  - pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN in *. lia.
  - intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & Y & _). unfold apart in Hf. lia.
  - unfold apart in Hf. lia.
Qed.

Lemma av_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof using Σ m W HA R_shad R_secmap.
  intros k s Hk. unfold schunk_avoid. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & Hroom).
  assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [q E2].
  set (u0 := (s_n s + 7) / 8). assert (E3 : ru8 (s_n s) = u0 * 8) by (unfold ru8, u0; ring).
  assert (Hu0 : 0 <= u0) by (apply Z.div_pos; lia).
  assert (EA : shad (s_mb s) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
  assert (EM : smsz (s_n s) / 8 = 512 * q) by (rewrite E2; replace (q * 4096) with ((512 * q) * 8) by ring; apply Z.div_mul; lia).
  assert (EU : ru8 (s_n s) / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
  assert (Eb : shad (s_mb s + 4096 + 2048) = a0 + 768 + SHB).
  { unfold shad. rewrite E1. replace (a0 * 8 + 4096 + 2048) with ((a0 + 768) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
  assert (Ec : shad (s_mb s + 4096 + 2048 + ru8 (s_n s)) = a0 + 768 + u0 + SHB).
  { unfold shad. rewrite E1, E3. replace (a0 * 8 + 4096 + 2048 + u0 * 8) with ((a0 + 768 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
  assert (Ed : (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) / 8 = 512 * q - 768 - u0).
  { rewrite E2, E3. replace (q * 4096 - 4096 - 2048 - u0 * 8) with ((512 * q - 768 - u0) * 8) by ring. apply Z.div_mul. lia. }
  unfold s_ubeg in *.
  split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
  split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
  split; [apply (R_secmap k s); [exact Hk | lia | destruct (s_quar s); lia | intros Hq; rewrite Hq; unfold s_ubeg; lia]|].
  split; [apply (ac_map_shad k s); [exact Hk | lia | rewrite EM, EA; change ((4096 + 2048) / 8) with 768; lia]|].
  split; [apply (ac_map_shad k s); [exact Hk | rewrite Eb, EA; lia |]|].
  - destruct (s_quar s); [rewrite fdrun_len, EU | rewrite (ushadow_len (s_n s) ltac:(lia)), EU]; rewrite Eb, EM, EA; lia.
  - apply (ac_map_shad k s); [exact Hk | rewrite Ec, EA; lia | rewrite Ec, Ed, EM, EA; lia].
Qed.

Lemma av_sec : sec_avoid W Σ.
Proof using Σ m W HA R_img R_grant.
  split; [apply ac_lits; vm_compute; reflexivity|]. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
  apply ac_PAB; lia.
Qed.

Lemma av_quar : quar_avoid W Σ.
Proof using Σ m W HA R_img R_grant R_prb.
  split; [unfold qcacheT; apply ac_T; lia|]. split; [apply ac_lits; vm_compute; reflexivity|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  apply (ac_slot 24 i CkBatch); [lia | exact Hi | lia | change (ClassSize 24) with 8192; lia | intros n' E; discriminate E].
Qed.

Lemma av_dep : dep_avoid W L.
Proof using Σ m W HA R_img R_grant. split; [apply ac_lits; vm_compute; reflexivity|]. split; [apply ac_DNB | apply ac_SSB]; lia. Qed.

Lemma av_ia : dsjl W ia_lits.
Proof using W R_img. apply ac_lits. vm_compute. reflexivity. Qed.

Lemma av_static_shad : Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.
Proof using Σ m W HA R_shad.
  apply Forall_forall. intros r Hr.
  assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x66e828) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
  apply (R_shad 0x10000 SEGTOP_A); [reflexivity | reflexivity | lia | unfold SEGTOP_A; lia | | | |].
  - unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
  - unfold shad, SEGTOP_A. assert ((snd r - 1) / 8 < 0xcde00) by (apply Z.div_lt_upper_bound; lia). change (0x66f000 / 8) with 0xcde00. lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _). unfold SEGTOP_A in *. lia.
  - unfold SEGTOP_A in *. lia.
Qed.

Lemma av_shadow : shadow_avoid W L.
Proof using Σ m W HA R_shad.
  unfold shadow_avoid. split; [|exact av_static_shad]. pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & X3). unfold rtA_sp0 in *.
  assert (M1 : l_ACEIL L mod 8 = 0) by (unfold l_ACEIL, STACK_WIN; apply (mod8_of _ 16 ltac:(lia)); [rewrite Zminus_mod, X3; reflexivity | exists 2; reflexivity]).
  apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
  apply (R_shad (l_ACEIL L) (2 ^ 47)); [rewrite E1; apply Z.mod_mul; lia | reflexivity | unfold l_ACEIL, STACK_WIN, sp_window_lo in *; lia | lia | lia | | |].
  - unfold shad. rewrite E1, Z.div_mul by lia. rewrite Z.max_r by (apply Z.div_pos; unfold l_ACEIL, STACK_WIN, sp_window_hi in *; lia).
    replace (2 ^ 47 - a0 * 8) with ((2 ^ 44 - a0) * 8) by ring. rewrite Z.div_mul by lia. change (2 ^ 47 / 8) with (2 ^ 44). lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & G3 & _).
    right. lia.
  - pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & G3 & _).
    right. lia.
Qed.

(* [comment removed for export] *)
Definition art_avoid_but_fs (W' : list ivl) (Σ' : rtsA) : Prop :=
  consts_avoid W' (lay Σ')
  /\ (forall c, 1 <= c <= 31 -> reg_avoid W' (l_SB (lay Σ')) c (pr Σ' c) /\ pclass_avoid W' (l_T (lay Σ')) c)
  /\ (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ' c)) i = Some st -> pchunk_avoid W' (l_SB (lay Σ')) c i st)
  /\ (forall k s, nth_error (sec Σ') k = Some s -> schunk_avoid W' s)
  /\ sec_avoid W' Σ' /\ quar_avoid W' Σ' /\ dep_avoid W' (lay Σ') /\ dsjl W' ia_lits /\ shadow_avoid W' (lay Σ').

Theorem art_avoid_gen : art_avoid_but_fs W Σ.
Proof using Σ m W HA R_img R_grant R_shad R_prb R_secmap.
  split; [exact av_consts|]. split; [exact av_reg|]. split; [exact av_pchunk|]. split; [exact av_schunk|].
  split; [exact av_sec|]. split; [exact av_quar|]. split; [exact av_dep|]. split; [exact av_ia | exact av_shadow].
Qed.

End Comp.

Section CompFs.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from W a n.
Hypothesis R_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 ->
  (forall f k, In (f, k) (frames Σ) -> a + n <= f \/ f + fs_size k - 8 <= a) -> disjoint_from W a n.

#[local] Notation ac_T := (ac_T Σ m W HA R_grant).
#[local] Notation ac_DTV := (ac_DTV Σ m W HA R_grant).
#[local] Notation ac_lits := (ac_lits W R_img).

(* [comment removed for export] *)
Lemma frame_apart : forall FSB c p c' p', (c = 0 \/ c = 1 \/ c = 6 \/ c = 2) -> (c' = 0 \/ c' = 1 \/ c' = 6 \/ c' = 2) -> 0 <= p < NF c -> 0 <= p' < NF c' ->
  (c <> c' \/ p <> p') -> frame_addr FSB c p + fsz c <= frame_addr FSB c' p' \/ frame_addr FSB c' p' + fsz c' <= frame_addr FSB c p.
Proof using.
ltac2:(KReplay.run1 (kr_t_RT_sep ()) ["CompFs"] "h03Hneh14__x1h24__x2h34__x3h41Hh53Hp'h64__p1h74__p2h84__p3h92Hah:7__arithh;4__ffh<6__sat0h=6__sat1h>6__sat2h?6__sat3h@6__sat4hA6__sat5hB8__varmaphC5__withD2c'hE6__sat6hF6__sat7hG6__sat8hH6__sat9hI2HphJ1chK3FSBhL2HchM3Hc'hN1phO2p'p%0p%1p&0p;1p;2p;3p;4p;7p;6p;8g00IXj1DTg00B>j1`Tg00AYj1TTg008<R0j22Tg04kBk100Tg00`Dj20Tg01C4j2=Tg02:Wj21Tg00dYj2eTg003Sj1lTg004lj3WTg01]Mj2PTg001Gj29Tg01^5j3STg01`hj2nTg01`Ij1rTg003lk105Tg000gk104Tg00CJj2vTg00`ak403Tg00Chk10CTg00DFk10BTg00K0j2_Tg00E1j2uTg00ETk10ATg00j^j1ZTg01cOk302Tg00FZk20@Tg00<mk20?Tg00G<k20>Tg00Ghk30=Tg00HGk40<Tg02`Nj2fTg002?j2JTg001cj2<Tg04l:j3~Tg04m:j1}Tg01b:j3qTg01bcj2|Tg02G]j2{Tg004Lj3xTg00KSj4kTg00L>j7jTg03?Ek60:Tg013Xj7iTg00a?j3zTg02HIk301Tg00MFj8tTg02=Uj8yTg02a7k309Tg00F6k608Tg00Lbk707Tg007AR1f0R2g00VYR33Wp=?f1R4=W12p=3f2R5=W14/22p=L19351<42'Jp=RAW142#lp=8AW154#l/22p=>%T2#Tp=U1=42,15p=X1054/02p=Hf3R6/051142'0p=5f5R7f4R8'0/961054/92'2p=I1086/951942'2p=7AW132p=c%l4/22p=F19861054/92'2p=a1932p=41<42,J5p=:1<32p=OAq142g01dQR9'|p>06g00TmR:1{54;x2p=wP1P4g01e=P2Ckp=hP4g00O;R;g00OZR<P<g00P:R=P2g00QAR>Fjp=GP4P;P<P<P=P2J0:p=gP5P;P<P<P=P4P2Fip=pAz142p=QB02142p=YB011429z15p=@B01142p=oP5P;P<P<P=P1P4g00QaR?P2CkP>Fjp=MP7P;P<P<P=P8P6P5P;P<P<P=P4P2FiGtp=m1142,05p=6P1P3P7P8P6P5P4P2Gyp=dB09142p=NAq1549q16/|9,{8=x:2p=KP4P;P<P<P=P2J08p=sP5P;P<P<P=P4P2K07p=VP1P4g00PZP2Ckp=^P1P4P?P2Ckp=CP6P;P<P<P=P5P;P<P<P=P4P>FjP2Fip=[f6R?P;P<P<P=P7P8P6P;P<P<P=P5P4P2GtGtp=A1954/22p=b1054/92p=BP1P?P7P8P6P5P4P2Gyp=;19651942'2p=EP6P;P<P<P=P5P4P;P<P<P=P2P>FjFip=]1942,25p=\1065/94/22p>0;%?6g00THR>#DR;%`>R9#TS00#DR@%T>RA#DRB,365L65L6'2%?5135B9L5@9L5;'2&0079R88&0089R66f7RC18?87>7P0f8RD#?13DB9LD@9LD;f:RE%TAS01#`#U#U#U#U#U#U#DRF'0RGf9RH%`A#URI#DRJ,=BRK'1S02Q01#US03#TS04#T#DRL?XBHS05,1DS063HRMQ05PG11CKP?AXLBCRGC5RNPNPGPMEIP8%?H%`9#TRM#DRG/e2,=BRN9REEf;RO/8H9>4Ef>RP/0FS07115KRQf<RRAXLB5RSC5RTPSQ0711OKS08AXLBOS09,1ES0:3HS0;Q0;Q09'0S0<PTD7]0]IXJ11eG3RT,=BRU9RHH%cH18ED'FP0%?E13E;S0=13EB9LE@S0>'2Q07113KRVPR1=B3RW,1LRXC5RYPXQ0;Q0<PYD7PC%?OARRRNS0?%c4#lRYf?RZf=R['8S0@'2fBR\/0FS0APVf@R]PXC5R^/0XR_Q0A/0QS0B11PSS0C'0R`P`PSP^Da]0]5XD1%4OS0D?:OUAW133R`18PRS0E'F1PB3S0F%OBRa1933%OW[[S0G%4BRbg00:CRcASB34UW9S0H%4W\c^9bS0I1PBTS0J%4T%OU[\aS0KASBT4VcX9bS0L%4U\c^9bS0M1PBJRT%4J%OK[\aRWASBJ4VcX9bRJ%4K\c^9bRdg01d2Re,n1Rf%reRe#rRg#r,n1Rh-06fRi1n1e&05:Re7wi3wS0N&04:R:P11v15P41v16H03Ri&0C1Rj&0B1Rk1_13Rl/hl,Gk,gk1u1ARm1u19R9'h,Gk,gkS0O5pk&0A<R<Pk1u1>1_1F'QS0P1_1BRn%ZI'YS0Q7@lRI1_1LS0Rg03oS:021n'oRo7@mRp/QoRqA@I9oRI5Mk1QIoS0S=MkpEm20@k=R=P2P5g00UYRpg00V9RI+0?20>25=WpIdB0=134H0<R3b;bBbCX11X21X31g007_S0T\`1345Q0T[S0U'2104FS0V/0VR`?65XRIPX116XRp,0`R`P`PXPIEI[^11^21^31P2fDRIfFR`fHS0WPCO4b:b<b=b>b?b@bAfARo?HFVRr11ZXS0X'0RsPXA6r[XRrPrPXPsEIeW0W5PRP2PCP5EdW4P2O113O;S0Y13OB9LO@S0Z'2P013R;S0[13R@S0\13RBS0]'2S0^10]FS0_PVPPPXC5RsPXQ0_11[KS0`AXLB[S0a,1RS0b3HS0cQ0cQ0a'0S0dPsD7P213[;S0eP;ARPPNS0f18oZS0g,2Y10IFS0hPVP\PXC5RsPXQ0h11]SS0i7HQS0jQ0j/0SS0kPsD7]0]5XD1%4[S0l1eG;Rs,=BRr7:[%c;18]PS0m'F1PBsS0n%4s%Or[\aS0oASBs4VcX9bS0p%4r\c^9bS0qQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MPTPWPJPd1PB;S0r%4;1=B;Rs#O[\aS0sASB;4VcX9bS0t%4s\c^9bS0up-0RtPfPf1f1BS0v/Nh1n1gRgPeDKS0wP:PiPjPkAMkl91sk7S0x5VkS0yP<Pk1sk?S0z%ZM,YnS0{,^m,Gk5VkS0|P<PkPkQ0P1_1;S0}Q0Q3@S0~Q0R%Z>,Yn'oS107@9S11,Cq1skCR>C[FAP=P3b;bBbCX11X21X31X6tX7tW8%45S12/J6RM1=BG,<5S13,J7S14105FRu/0VS15?HpXS1611;KRp,0uS1711LsRs768S18;bC[[^11^21^31^6t^7t^8tP2fNRv/0FRw/0pS19fJRx;6s10wVS1:fLRw/1XS1;'07Bs%4wS1<1<xrPxPwPvPRP\O8b:b<b=b>b?b@bAbEbFbGbHfCRy/0FRz/0VS1=11oXS1>'0R{PX10zpS1??6ZsRzPzPsP{EIeW0W5PPP2PHP8F;W4P2O113[@S1@13[BS1A'2S1BP013P@S1C13PBS1DP_Q0A11ZKPPAXLBZR_C5S1EQ1E/0_S1FP^CEP213Z@S1GP@AR]]NS1H18yoS1I,2Y10`FS1JPVPIPXC5RYPXQ1JPQP\PSC5S1KQ1K/0SS1LPYD7]0]5XD1S1M%4ZS1N1eG@RY,=BR^7:Z%c@18\]R_'F1PBYS1O%4Y%O^[\aS1PASBY4VcX9bS1Q%4^\c^9bS1RQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MPTPWPJPd1PB@S1S%4@1=B@RY#O[\aS1TASB@4VcX9bS1U%4Y\c^9bS1VPfPf1f1LS1W/NhPgPeDKP:PiPjPkQ0yP<PkQ0|P<PkPkQ0P1_1@S1XQ0Q3@S1YQ0RQ00#Z,Yn'oS1Z7@9R{,CqP>C[FAP=P3b;bBbCX11X21X31X6tX7tX8tQ14Q1611@KRz,0uS1[11LYRY768S1\;bC[\M^11^21^31^6t^7t^8tP2fPR|/0FS1]/0zS1^?6wYQ1]/0VS1_?6vXS1`7BY%4vS1a1<w^PwPvP|PRPIO8b:b<b=b>b?b@bAbEbFbGbHfER}/0FR~/0VS1b?6yXS1c/0XS1d10~zS1e?6oYRVPVPYQ1cDaeW0W5P]P2POP?F;W4P2O113ZBS1fPBQ1MQ1N1eGBRG,=BRV7:Z%cB/F_1PBBS1M1=BBS1g#O\b\aS1hASBB4VcX9bS1iQ1g#4\c^9bS1jQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0M1PBGS1k%4G%OV[\aS1lASBG4VcX9bRG%4V\c^9bRbPTPWPJPdPfPfQ01#D,f1S01/NhPgPeDKP:PiPjPkQ0yP<PkQ0|P<PkPkQ0PQ0Q7@nS0QQ0R%ZA,Yn'oRA7@9Rc,CqP>C[FAP=P3b;bBbCX11X21X31X6tX7tX8tQ14Q1611BKRq,0uS0RQ1g,1LRu768S1g;bC[\M^11^21^31^6t^7t^8tP2Q1]/0qS1]?6wuQ1`7BuQ1a1<wVPwPvP|PRPIO8b:b<b=b>b?b@bAbEbFbGbHQ1d10~qS1d?6ouRaPaPuQ1cDaeW0W5P]P2POP?F;W4P2O1n200100001021100011000W4P2O1n200100001021100011000W4P2O1n200100001021100011000W0WIPEP2P8P5EdW4P2O113HB9LH@9LH;P0Q0=Q0>10RFRaQ08Q0:3HS0:Q09Q02Q065HaRaPaQ05Q0:EIP2Q0YP;Q0?18[O9>4RQ0_Q0C7HQRaPSQ0cQ0dPaD7]0]IXJ1Q0D?:Or18RE9>;OP0%?RQ0[Q0^'2Q0_PpPPPsC5REPsQ0cQ0dPED7PH%?[Q0f18;4REQ0g'2Q0hPpP\PsC5S0g/0sS0dQ0jQ0kQ0gCE]0]5XD1Q0l?:[U%?;Q0m'FQ0nQ0oQ0pQ0qQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MPTPWPJPdQ0rQ0sQ0tQ0uPfPfPhQ0v/NgPeDKS0vP:PiPjPkQ0xQ0{,^9,Gk5VkS0{P<PkAMklmQ0z5VkS0mP<PkP>PkQ0SQ0~Q107@mRl'CC]FAP=P3b;bBbCX11X21X31X6tX7tX8tQ13,J6S13Q12/J7RaQ15118X;HXS15Q17116sS12'0S175\C[[^11^21^31^6t^7t^8tP2Q19?6wsQ1:?6xX7Bs1<wr%4xPxPwPvPRP]O8b:b<b=b>b?b@bAbEbFbGbHQ1?11osS1:'0S1?PsQ1=Q0X'0S1=Q1=PXQ1?EIeW0W5PPP2PHP5EdW4P2O1Q0eQ1B'2P013P;S1BQ1CQ1D'2S1DQ0APpP]PsC5S1CPsQ1EQ1FQ1CD7P213Z;S1CP;Q1HQ1I,2EQ1JPpPIPsC5S0ePsQ1KQ1LQ0eD7]0]5XD1Q1N?:Zr13;;S0e/F_Q0nQ0oQ0pQ0qPTPWPJPdQ0rQ0sQ0tQ0uQ0NP:PiPjPkQ0}Q0}'h,Gk,gkQ0O5pkP<PkQ10,QlS0}Q115MkQ11Q10'QS11=MklEmP=P3b;bBbCX11X21X31Q0eQ0T[Q0U'2Q0V/0pRl?65sS0ePsQ12,0lRlPlPsQ0eEI[^11^21^31P2Q0WPxPwPCO4b:b<b=b>b?b@bA10~pR~11ysS0e'0RlPsQ1:,0~R~P~PsPlEIeW0W5P]P2POP8F;W4P2O1Q1GQ1f'2S1fP013]@S1G13]BS1:Q0dQ0h11oKP]AXLBoRlC5S0dQ0d/0lS12Q0gCEP213o@S0gP@AR\\NS1018}yS1?,2EQ0W/0FS1=PpP`PsC5REPsQ1=PQPIPSC5S0XQ0X/0SS19PED7]0]5XD1S0~%4oS0k?:o^18I\RE9>;@Q1OQ1PQ1QQ1RQ0nQ0oQ0pQ0qPTPWPJPdQ0rQ0sQ0tQ0uQ1SQ1TQ1UQ1VPfPfQ04#D,f1S04/NhPgPeDKP:PiPjPkQ0yP<PkQ0zQ00#`Rl#Z,YnS0j,^m,Gk5VkS0cP<PkPkQ0}/C{P>C[FAP=P3b;bBbCX11X21X31X6tX7tX8t%Dl,=B,<5S0_,J7S0^Q17/0sS17Q1\;bC[\M^11^21^31^6t^7t^8tP2fRRl/0FS0[/0zS0D11vYS0?'0Q0[/0pS0C?6|sS0:7BY%4|S051<v^S06PvP|PlPRPIO8b:b<b=b>b?b@bAbEbFbGbHfGR~/0FS02/0pS09?6}sRp/0sS08Q02/0zS0>11yYS0='0S1cQ1cPYPpDaeW0W5P\P2P[P?F;W4P2O113oBS1cPBQ0~Q0k?:oVA>;BEQ0nQ0oQ0pQ0qQ1MQ1hQ1iQ1jQ1kQ1lPGPbPTPWPJPdQ0rQ0sQ0tQ0uQ0wP:PiPjPkQ0yP<PkQ0cP<PkPkQ0}/CcP>C[FAP=P3b;bBbCX11X21X31X6tX7tX8tQ0^Q17Q1g;bC[\M^11^21^31^6t^7t^8tP2Q0[/0qS0[11vuS0^'0Q0:7BuQ051<vVS0:PvP|PlPRPIO8b:b<b=b>b?b@bAbEbFbGbHQ08Q02/0qS0211yuS08'0S17Q17PuPpDaeW0W5P\P2P[P?F;W4P2O1n200100001021100011000W4P2O1n200100001021100011000W4P2O1n200100001021100011000W0WIPRP2P?P8F;W4P2O1Q0ZP0Q0\Q0]Q07Q0`Q0b3HRpQ0aQ0;Q0<PpD7P2Q1@P@Q0fQ0@9>4PQ0BQ0i'0RpPSQ1EQ1FPpD7]0]IXJ1S0fQ0l?:[^Q0E9>@[P0%?PS0iQ1BQ1D'2S1DQ0APzP]PYC5RpPYQ1EQ1FPpD7PO%?ZS1BQ1H18@4RpQ1I'2Q1JPzPIPYC5S0B/0YS0@Q1KQ1LQ0BCE]0]5XD1Q1N?:ZUS1N%?@/F_Q1OQ1PQ1QQ1RQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MPTPWPJPdQ1SQ1TQ1UQ1VPfPfPhQ1W/NgPeDKP:PiPjPkQ0{P<PkQ0mP<PkP>PkQ0SQ1YQ1Z7@mRU'CC]FAP=P3b;bBbCX11X21X31X6tX7tX8tQ13Q15Q1[116YS1Y'0S1[5\C\a[^11^21^31^6t^7t^8tP2Q1^Q0?'0Q1_Q1;'0S1_7BYQ06Q1<PwPvP|PRP]O8b:b<b=b>b?b@bAbEbFbGbHQ1eQ0='0S0=PYQ1bQ1>'0S1bQ1b/0XS1>Q0=D7eW0W5P]P2POP5EdW4P2O1Q1CQ1f'2S1fP013];S1CQ1GQ1:'2S1:Q0hPzP\PYC5RXPYQ0dQ12PXD7P213o;S1GP;Q10Q1?,2pQ1=PzP`PYC5RXPYQ0XQ19PXD7]0]5XD1Q0k?:orS0kA>@;EQ1OQ1PQ1QQ1RQ0nQ0oQ0pQ0qPTPWPJPdQ0rQ0sQ0tQ0uQ1SQ1TQ1UQ1VPfPfPhQ04/NgPeDKP:PiPjPkQ0xQ0j,^9,Gk5VkS0jP<PkQ0mP<PkP>PkQ11/CUC]FAP=P3b;bBbCX11X21X31X6tX7tX8tQ0_,J6S0_Q18/0sS18Q1[5\C\a[^11^21^31^6t^7t^8tP2Q0D11|YS04'0Q0C?6vsS0C7BY1<|^S0DQ1aPvP|PlPRP\O8b:b<b=b>b?b@bAbEbFbGbHQ0>11}YRr'0RoPYQ09Q0e'0RX10XsS09PoD7eW0W5P\P2P[P8F;W4P2O1Q0gQ1c'2S1cP013\@S0g13\BS0eQ0@Q1J11yKP\AXLByRLC5RK10KLS0@Q0BCEP213y@S0BP@ARIINS0>18~}S0=,2p10xFS1ePzQ0WPYC5RxPYQ1ePQP`PSC5RQ10QSS06PxD7]0]5XD1Rx%4yRS?:y^S1;13@@Rp18`IRN'FQ1OQ1PQ1QQ1RPTPWPJPdQ1SQ1TQ1UQ1VQ0NP:PiPjPkQ1XQ1X'h,Gk,gkQ0O5pkP<PkQ1Z,QU=Mk{Q1Z,Q{=MkUEmP=P3b;bBbCX11X21X31Q0T\pQ0U'2Q0V/0zRp?65YRLPYQ1Y,0pRpPpPYPLEI[^11^21^31P2PwPvP|PCO4S1Yb:b<b=b>b?b@bAfI/0FRL/0zRp?6~YRo/0YRs10prRp10pYS1ZPoCEeW0W5PIP2PZP?F;W4P2O113yBS1XPBPxA:SyVS0?A>@BNQ1OQ1PQ1QQ1RQ1MQ1hQ1iQ1jQ1kQ1lPGPbPTPWPJPdQ1SQ1TQ1UQ1VPfPfPhQ03#D,f1RS/NgPeDKP:PiPjPkQ0xQ00#TRy#Z,YnRx,^9,Gk5VkP<PkQ0mP<PkP>Pk1QcAR9/CUC]FAP=P3b;bBbCX11X21X31X6tX7tX8t%Dy,=B,<5Ry,J6Q1g/0uQ1[5\C\a[^11^21^31^6t^7t^8tP2fTRU/0FRF/0zRz?6lY10FqRF11|uRr'07BY1<l^Q05P|PlPUPRPIO8b:b<b=b>b?b@bAbEbFbGbHPs10LqRL11}uR}'0Rs10suS05PoCEeW0W5PIP2PZP?F;W4P2O1n200100001021100011000W4P2O1n200100001021100011000W4P2O1n200100001021100011000W0WIPPP2PDP?F;W4P2O1Q1APBQ0fQ0l?:[VQ0E9>B[P0Q0iQ1DQ0APqP]PuC5RoPuQ1EQ1FPoD7POQ1BQ1H18B4R4Q1I'2Q1JPqPIPuC5Ro/0uS1JQ1KQ1LPoCE]0]5XD1Q1N%?B/F_Q1MQ1hQ1iQ1jQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ1kQ1lPGPbPTPWPJPdPfPfPhQ01/NgPeDKP:PiPjPkQ0{P<PkQ0mP<PkP>PkQ0SQ0Q?@mAR_'CC]FAP=P3b;bBbCX11X21X31X6tX7tX8tQ13Q15Q0R116uR6'0R^5\C\a[^11^21^31^6t^7t^8tP2Q1]Q0^'0Q1_7BuQ0:Q1<PwPvP|PRP]O8b:b<b=b>b?b@bAbEbFbGbHQ1dQ08'0RwPuQ1bQ1>PwD7eW0W5P]P2POP5EdW4P2O1Q1fP0Q1CQ1:Q0hPqP\PuC5ROPuQ0dQ12POD7P2Q1GP;Q10Q1?,24Q1=PqP`PuC5R`PuQ0XQ19P`D7]0]5XD1Q0kA>B;EQ0nQ0oQ0pQ0qQ1MQ1hQ1iQ1jQ1kQ1lPGPbPTPWPJPdQ0rQ0sQ0tQ0uQ0vP:PiPjPkQ0jP<PkQ0mP<PkP>PkQ11/C_C]FAP=P3b;bBbCX11X21X31X6tX7tX8tQ0_Q18=\C^\a[^11^21^31^6t^7t^8tP2Q0[/0rQ0C7Bu1<|VQ1aPvP|PlPRP\O8b:b<b=b>b?b@bAbEbFbGbHQ02/0}R}PuPXQ09P}D7eW0W5P\P2P[P8F;W4P2O1Q1cP0Q0gQ0eQ1JPKQ0@PoCEP2Q0BP@Q0>Q0=,24Q1ePqQ0WPuC5R4PuPQQ06P4D7]0]5XD1R4Q1;A>B@NQ1OQ1PQ1QQ1RQ1MQ1hQ1iQ1jQ1kQ1lPGPbPTPWPJPdQ1SQ1TQ1UQ1VPfPf1NShPgPeDKP:PiPjPkQ0yP<PkQ0z1^mx,Gk5VkP<PkPk1Q_ARA/C{P>C[FAP=P3b;bBbCX11X21X31X6tX7tX8t1J7yP^PuQ1\PCH0;[\M^11^21^31^6t^7t^8tP2Q04,0zA6Flu7BY%4lQ0DP|PlPUPRPIO8b:b<b=b>b?b@bAbEbFbGbHA6L~uRL/0uR~PpQ1ZPLCEeW0W5PIP2PZP?F;W4P2O1Q1XPBP4Q0?13BBRB/FNQ1MQ1hQ1iQ1jQ1kQ1lPGPbPTPWPJPdQ0NP:PiPjPk1hnn,Gk,gkQ0O5pkP<PkAMkAcAMk9_EmP=P3b;bBbCX11X21X31Q0T\BQ0U'2Q0V/0qRq?65uR5Pu10q6RqPqPuP5EI[^11^21^31Q1Yb:b<b=b>b?b@bAP~PsQ05PLCEeW0W5PIP2PZP?F;W4P2O1n200100001021100011000W4P2O1n200100001021100011000W4P2O1n200100001021100011000W0WIPPP2PDP?F;W4P2O1n200100001021100011000W4P2O1n200100001021100011000W4P2O1n200100001021100011000A~HDCRC%}DA~H?7RHPH%}?PCEIeW0W5WIWMWLXO1XD1XN1XJ1XK1o"). Qed.

Lemma fs_size_fsz : forall k, fs_size k = fsz (Z.of_nat k).
Proof using. intros k. unfold fs_size, fsz. rewrite Z.shiftl_mul_pow2 by lia. ring. Qed.

Lemma nth_indep_Z : forall (l : list Z) n d d', (n < length l)%nat -> nth n l d = nth n l d'.
Proof using. intros l n d d' H. apply nth_indep. exact H. Qed.

Lemma av_fs_cls : forall k, (k = 0 \/ k = 1 \/ k = 6 \/ k = 2)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using Σ m W HA R_shad R_fsb.
ltac2:(KReplay.run1 (kr_t_RT_sep ()) ["CompFs"] "p'0h01Hh14__x1h24cstrh36__sat4h47__arithh54__ffh68__varmaph75__with81zi001zh92Hah:4__x2h;6__sat5h<6__sat6h=4__x3h>3Hinh?2Hbh@2HfhA3Hp'hB3HnehC6__sat7hD2k'hE1phF1EhG6__sat8hH1ahI4HlenhJ2_HhK1fhL1khM4__p1hN4__x4hO1bhP5cstr0hQ1ni011nhR1xi021xhS3HflhT3Hk'hU2HphV1XhW6__sat9hX2G2hY2M1hZ2M2h[4__x5h\4__x6h]2a0h^2fkh_1mh`2E1ha2E2hb2F0hc2F2hd2F4he3FC2hf2G1hg2G3hh2G4hi2G5hj2H1hk2H2hl2HFhm3HFBhn3HFrho3Haphp2Hchq3Hc'hr3Heqhs2Hkht2Hqhu3Hwfhv2R1hw2R2hx2X1hy2X2hz3_H0h{3_H1h|3_H2h}3_H3h~3_H4i032b0i041ei051oi062p'i071qi081si091yp%0p%1p%2p&0p&1p&2p;1p;3p;4p;2p;6p;<p;7p;5p;;p;8p;:g01`Ik108Tg01FHk323Tg01edk11uTg0162k11]Tg016jk11VTg017hk11JTg018dk11CTg019`k11>Tg01:[k118Tg01;Wk12=Tg01<Qk129Tg01=Ok125Tg01>Gk122Tg01?Ak11}Tg01@;k11{Tg01A7k41tTg01B8k11lTg00AYj1;Tg00IXj1<Tg00`Dj24Tg01C4j2ATg001cj2HTg01CQk11QTg00B>j1GTg01DOk11ITg01EKk11FTg002?R0j29Tg01Pnk11?Tg01nNR1j10Tg04nQj2qTg04oKk40TTg050Lk117Tg051Dk20QTg052Bk12<Tg053:k12;Tg0542k12:Tg000Gk212Tg024Lj1NTg00<4S00k20]Tg00X0k121Tg00nck30jTg02OGk21|Tg01mnk20LTg001Gj21Tg054jj1dTg055hk10FTg056ck21sTg057Ck31pTg057^k10KTg058[k11iTg00dYj2KTg02:Wj27Tg059Vj2pTg00^ck30^k61yTg02=Uk60>k70Uk81bm;0YTg04kBj1ETg008<R2j26Tg004lj38k11STg03>?k11RTg00<mj2zTg02Q:m<0_Tg03>]j6[Tg02DEj1@Tg003lk10sTg000gk11HTg013:k11GTg00Chk11ETg00DFk11DTg00K0k20qTg00FZk21BTg00G<k21ATg00Ghk31@Tg00HGk40pTg036Hj4tTg01JXk11=Tg01MHk11<Tg01NBk11;Tg01O:k11:Tg01P4k119Tg004Lj3eTg0000j3fTg00JVk30RTg00Mjk303Tg01GAk116Tg02cek615Tg01KRk314Tg01I>k20HTg01^Yk20`Tg00E1k213Tg00ETk128Tg02bik626Tg00c]j1kTg01`hk211Tg01bck20kTg00oaj3cTg05:Tk210Tg05;Qj4sTg04l:j3>Tg04m:j1CTg00fTj1~Tg02fZj2MTg01]Mj2OTg01^5j3STg02<Pk31zTg03<]k21xTg003Sk10:Tg00J6S01k21wTg05;mk31rTg01\5k20dTg02YYk21nTg0435k21kTg05<Lk51jTg005ck60Xm;1cTg05=Jk11hTg03mgk41fTg05=lk61eTg00I9k21dTg006ak40ZTg05>Jm:1aTg05?Hk11`Tg05@Fk51_Tg03c>j2wTg03c^k31\Tg01cOk30tTg00=Gk40ITg03j5k51[Tg03jok30vTg05ALk31ZTg01_Jk11gTg01_hk21YTg01aQk30eTg02`Nk21XTg02a7k31mTg02G]k20yTg02dak31WTg02e^k11qTg01HDk11TTg03gWk30aTg008Vk40iTg00?<k31vTg00>_k30|Tg048am<0}Tg00KSk406Tg00L>k70ATg013Xk71PTg00CJk21~Tg00`ak420Tg00MFk80[Tg00a?k30PTg01b:k30lTg02HIk30~Tg00j^k11NTg00e6k31MTg00F6k61LTg00Lbk727Tg03?Ek61KTg00iDR3f0R4g01d2R538p=Xf1R6=834p==f3R7f2R8583A8364'6p=F1664,68p>091964,98p>0Wf4R9P7%081q64H0Tp=WP9P7P81q64H0Tp>0ng007AR:@1v34p=Pg00VYR;/14p=3%E4,H6p=}f7R<:0|:3f6R=f5R>;>958:P:P71q86#dP;Cs=8:4'9p>001986/94p=iA8:64p=2A8386/64p>0=1q64#dp=R20L:4p=lA8:4;p=DA8:=;A8:>9A8:78A8:64'6'6'6p=gA8:;4p>0hP3P:P:P:P1P1P7P8P6P5P;P4N<0}p>1OP:P:P4P6P8P7P9P;P>P=P<f8R?N<0_p>0m20q:4p=UP8g00O;R@g00OZRAPAg00P:RBP:P6g01e=RCP4H06g00QARDK0Ap=ZP9P@PAPAPBP7P@PAPAPBP:P8PCP6H06PDK0AP4K1Pp=\P3P:P:P:P1P1P>P9P7P8P6P4N<0}p>0cP:P:P<P=P>P9P7P8P6P;P;P4N<0_p>0bP:P:P4P6P8P7P9P>P=P<P?f9S02N<0_p=n%;4#;#;#;p>04%;4#;p=u%;4#;#;#;#;#;#;#;p>0GP:P:P6P4H0Zp>011H;4p=B1186/64p=_1486/14p=51q64#d-0L:p=Q%04,1;p=I21~:4p>0EP:P8P6P4H20p=]213:4p>02P8P@PAPAPBP:P6g00QaR1P4H06PDK0Ap=LP7P@PAPAPBP8P6P4L0[p>0OB0P:64p=TP:P6P1P4H06p>0DP9P@PAPAPBP7P@PAPAPBP8PDK0AP6P4L0[p=mP:P3P8P6H0Z=f74p={211:4p>0CB0l:64:0l:8p>0NP:P6g00PZP4H06p>0M1764,48p=^%d4-0L:p>241H64,98p=bA8:97A8:86/64'6p>0?B0~:64:0P:8p>0\P:P;P7P8P6P4J0>p>0@A8:78A8:64'6p>0BP:P9P7P8P6P4J0>p=:P7P@PAPAPBP:B0P:86P1P4H06PDK0Ap=j1K64,A8p=|1K64,48p=`&1N4:0t:6p=aB1M:64p>0;P:P3P6P4H0Zp=Y%C4,46p>0{B0|:36=8:4p>0oP:P71q86#dP;Cs=8:4p>0SA8:64$0:p=J11;6/94p>0VA>86498:7p=oP:P6P4P;Csp>1oP6P@PAPAPBP4J1Lp>0xP6P@PAPAPBP4PDK0Ap>0rP8P@PAPAPBP6P4K27p>0wP:P8P6P;Cs=8:4p>051164,68p>1^1A64,78p=r14781764'4p=x20H64=8:;p=VP6P@PAPAPBP4J1Kp>0f1764,48,w7p=h1464,w8p>0u1486/44p>0J1786/44p>0<14971786'4=8:4p=vB0~:64p=?B0P:86>0P:4p=yB0l:64p>0gP=P@PAPAPBP>P9P7P@PAPAPBP8P6P4L0[L0[p>0zP:P6PCP4H06p>1Ug02i5S03,44p>07%X4&085RC,=4P4&08CR@$08RD$08S04$08S05$08R1P4P@CF409REp,2ΣRFp,1mS06p,2HAS07423&1uFP0&1]FRG$1VS08&1JFS09&1CFS0:&1>FS0;&18FS0<&2=FS0=&29F&25FRH&22GRI&1}GRJ&1{GRKH1t&1lHg00THS0>#;S0?#<RL'4Q0?#;S0@#;S0A#;RM#<S0B,AL'H&1QHQ0>#GRN#GS0C#GS0D#G#G#G#G#<'4Q0?#GS0E#;S0F#;S0G#<S0H,ALRO'H&1IH&1FF'940W40WS0I'9S0J'9S0K'9S0L'9S0M'9S0Np,1WRH&1?GRP%07S0O1qF7S0PH0TP4Q08Q0NP0Q09Q0MPHPPP<PFP<DWP4Q09Q0MP0Q0:Q0LPHPPf;RQPFPQDWP4Q0:Q0LP0Q0;Q0KPHPPf?RRPFPRDWP4Q0;Q0KP0Q0<Q0JPHPPfCRS#0S0QPFPSI0nP4Q0<Q0JP0Q0=Q0IPHPPfGS0RPFQ0RDWP4Q0=Q0IP0&17FRT-0Q;S0SQ0>#<RU&2<FRV+0QS0T%;NS0U#<RW&2;FRX+0QS0V&2:FRY-0QLS0W'9S0X212:3RZ%P4R[#X1=[CP[P1P[P@CF409%34R\%P6R]#0R^,}4P6PPP^P4%N4S0YPFP]PUL003iXE:-0]:'9X^ZS0Z&21FR]40jS0[21|Z]20LZ]#0Q0B'11qF6R^#d$0F#021s[8X^Z>1pZ]-0LZ#0'2\E^L3&0K^Q0C#;S0\#<R^,ALR[g05B5&1iF'K'7'1\E^L3'940WS0]'9S0^'9S0_'9S0`PHPPfKS0aPFQ0aDWP6Q0SQ0`P0Q0TQ0_PHPPfOS0bPFQ0bDWP4Q0TQ0_P0Q0XQ0^PHPPfSREPFPEDWP4Q0XP0Q0VQ0WQ0^PHPPfWREPFPEDW[P4Q0VQ0WQ0^P0Q0[Q0]PHPPf[S0cPFQ0cDWP4Q0[Q0]P2f^RE#XPEP1PEP@CF:0=ECf_R_#0R`1RF_Ra'pf]%X_P3P5%04S0d1RF4Rb'pXL3Rc%dTRd,p;&0KTRT#3Q0D#;#G#<,ALRe,HT&0Fd#0Q0B'13i<0^Sf`RdP4J0>W0P4O1P_P1P_P@CF:0=_CP21=dCPdP1PdP@CFfaR_#0RT1RF_Rf'pP41=_CP3PCPc%dVRg,pU&0KVRV#31HVe&0Fg#0Q0B'13ifARg40^fbRVP4J0>W0P4O1P_P1P_P@CFP21=V11=V@fcS0e#0R_Q0e,RF'pP4Q0e/=1RhP3P1Pc%dXRi,pW&0KXRX#31HXe&0Fi#0Q0B'13if<Ri40^fdRXP4J0>W0P4O1Q0e/=@RjP3P@Pc%dYRc,pL&0KYRY#31HYe&0Fc#0Q0B'13i<0^QPXP4J0>W0P4O1n200100000021000010000W0P4O1n200100000021000011000W0P4O1n200100000021000011000%0E1RFE'pP0%la#0%E`'2%D4S0f124US0g'6X8:R`>0j:aPHPPPdPFPdDWP4%lf#0%ET'21RFV:0j:`P2Q0e#XQ0e16hj80=C%0XRjPjPUPjPWPjPLFgPV%XXP3P5%lb#0Q0d#E'2%06S0hQ0hPUQ0hPWQ0hPLFg]IXL3Rb1RF5S0i#lRV#0Rj%05Rh#ES0j'2%DhR`12hURT12hWRf12hLRd'6Ra'6RE'6S0kA8:;;Rc&0hUS0l&0hWRY&0hLRe'6Rk'6Rl'6S0mP`PEPcPlP:P:&1S:RlP4XR:RcPl1264$1RZ09:XR:REPhP;PcPcQ0d,z:XR3R`1z:;S0nH1ORmP;P;Q0nN<0_PTPaQ0lPkPlPcPlPEPhPmPUPU1z:URkN90mPfPdPYPePlPcPlPEPhPmPWPW1z:WReN90mPlPcPlPEPhPmPLPL1z:LRmN90mE[E[E[S0o%@V%3jg00TmS0p$0sRjQ0p$1HRV&1G:RY&1E:Rd&1D:RfPf20q:;RaPaPfPfPa%UURTPfPfPa%UWRn%ULRo9ZfaD\D\D\21BfBRBP4P8g00UYRpg00V9Rq'zS0q21A48=8pqdB1@:;6S0rH0pRqb5b6b7Q0mP4b4S0sb2CtQ0keWIfeRpP4P7K0UW0P4O1PXP1PXP@CF:0=XCP21=pCPpP1PpP@CFffRp#0RXPXPUPXPWPXPLFgP41=pCP3PCPb1RFCS0t#lRr#0Rs%0CRt#ES0u'2%DtRu12tURv12tWS0v12tLS0w'6Rw'6Rx'6S0x%DURy12UURz12UWR{12ULR|'6R}'6R~'6S0yPuPxPyP~PlPcPlPEPtPUPcPcP`PCPUPkJ0cR~Q0nL0bPvPwPzP}PlPcPlPEPtPUP~PUPUPkM:nQ0vQ0wP{P|PlPcPlPEPtPUP~PWPWPeM:nPlPcPlPEPtPUP~PLPLPmM:nE[E[E[S0w%@r%3sPjPVPYPdPfPfPTPaPfPfPTPTPfPfPTPnAZfToD\D\D\PBPqb5b6b7Q0yP4b4S0vb2CtQ0xeWIfgRsP4P>K0UW0P4O1PpP1PpP@CFP21=s11=s@fhS0z#0RsPsPUPsPWPsPLFgP4Q0z/=1P3P1Pb1RF1S0{#lRs#0Rr%01R~#ES0|'2%D~R|12~US0}12~WS0~12~LS10'6R{'6R}'6S11%DWRz12WURw12WWRv12WLRy'6Rx'6Ru'6S12P|P}PzPuPlPcPlPEP~PWPcPcP`P1PWPeJ0cRuQ0nL0bQ0}P{PwPxPlPcPlPEP~PWPuPUPUPkM:nQ0~Q10PvPyPlPcPlPEP~PWPuPWPWPeM:nPlPcPlPEP~PWPuPLPLPmM:nE[E[E[S10%@s%3rPjPVPYPdPfPfPnPaPfPfPnPTPfPfPnPnAZfnoD\D\D\PBPqb5b6b7Q12P4b4S0~b2CtQ11eWIfiS0}P4P<K0UW0P4O1Q0z/=@P3P@Pb1RF@S13#lRb#0Rr%0@Rs#ES14'2%DsRu12sUS1512sWS1612sLS17'6Ry'6Rv'6S18%DLRx12LURw12LWR{12LLRz'6R}'6R|'6S19PuPvPxP|PlPcPlPEPsPLPcPcP`P@PLPmJ0cR`Q0nL0bQ15PyPwP}PlPcPlPEPsPLP`PUPUPkM:nQ16Q17P{PzPlPcPlPEPsPLP`PWPWPeM:nPlPcPlPEPsPLP`PLPLPmM:nE[E[E[S17%@b%3rPjPVPYPdPfPfPoPaPfPfPoPTPfPfPoPnAZfooD\D\D\PBPqb5b6b7Q19P4b4S16b2CtQ18eWIQ0}P4P<K0UW0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000P_P_PUP_PWP_PLFgPFQ06Q07PPQ0E#GS0}$04#G#u#G$04$0G#<R_212::Rr&1=G%uMS15#u$04RM#;#uS1:#;Rb$04Rm#G#;#u#G$04$0G#<+01201P_R`38&1<G%;m#uS1;#<S1<+01RE&1;G%<MRM+01Rl&1:G%<bRb+01Rc&19G001MRe%<m-01IQ1<-01J&0sr5er5erRJ9er`RI5erRm5erRz5erR{5er9fr`A8rE`Afr`{A8rl`Afr`zA8rc`Afr`mA8re`Afr`IA8r``Afr`J1zr`40R403403403403403&16G9fr`eJ15B14GP_P0%BPS1=20HPMR`#DS1>14P_Rr/1KS1?g02jmg02ij/1P5_rS1@g014</1P9_rbS1A'9S1B'9S1C'9S1DPHPPPXPFPpI0nP4Q1=Q1DP0Q1>Q1CPHPPfjRpPFPpDWP4Q1>Q1CP0Q1?Q1BPHPPfnRpPFPpDWP4Q1?Q1BP0Q1@Q1APHPPfrRpPFPpDWP4Q1@Q1A11P6RpQ0@#GS1E#u$04S1F#u$04#<RX,4PRb9586RKp,5R_fsbS1GP7P8fyRJ,QFRI#@Re%IIRI20`PMRm%3P%3M%3`[[R`PjPV&0E8S1H?]6YS1IPdPfQ0>-13:RcQ0?$02Rz5LfS1J&28ARAQ1JH0OPBPqb5b6b7X1:X::11461168S1K[^1:^::P4P=PPP9O3b4b3b2PePIPmP`PjPVQ1H&0E7S1L7]6S1MPdPfPf1TczRI&02NS1N%UXS1O'T+0DPAQ1N%U_S1P'T9LfIS1QDmPBPqb5b6b7X1:X::X=:1446S1R148XS1S'11468S1T147_'1S1U[^1:^::^=:P4PPP>P=P7O4b4b3b2PZP6P4P]C{S1VPFQ06Q07P8P6P4J2611b8%k6RN,48S1W/1r%BN40WP011b7%k8RN,47S1X/1r%BN'914?<%k7,49S1YQ0A#<RN'KS1Z/1?7_9P411b>%k>Re=5=r%Be'9f:S1[=5Q<%k=,4</KN/1Qp+01BS1\,QFRe#@%IePmP`Q0p&0CDS1]&0C@S1^211:5S1_40Ng01dQS1`+0k;ejPV&0E99]Y8Q1L7]6PdPfPfQ0U$02RDQ1O'TReQ1N+0DPAPfPf20DIePAPfPf20MaDPAQ1N9LfIS1aDmDmDmPBPqb5b6b7X1:X::X=:XN:A57X8Q1T149X'1%B>1479S1b/1>[[[^1:^::^=:^N:P4PPQ1[f=RDf>ReP9PQfLS1cO7b4b3b240RWJWVP6P4O2n2001000000121000000b]W>XD3XK:O5WkWjXQ:XH:AcH78\K\p^Q:^H:fvRp#0S1d9^PNRK=cHNQ1d-10PS1e1qFpS1f$24#0S1g5cHS1hfw#0Rp#E9b\4S1iP:%N6S1jfxRr,RFRlPUCs#DS1k%0JRJ=>P8R{%CJRE5cH%~{1MEN5cH'9[[^E:S1l'9P4PKPNP2Q1d#DS1mQ1dPUQ1dPWQ1d/2LI0?S1nA^PNpS1o,1PfBRK%DpS1pA^PN4RE,1PX8:R{%llRl#@S1q%IlS1rPmP`PjPV&0E6RlPd%UNRk>0\caS1s9LfcPBPqb5b6b7X1:A^4N;S1t,14^1:P4PPO1R}b4b3b2%0rS1uP4H0@W0P4O1PpPUPpPW12pLI0?S1vP2Q1u/2US1wQ1uPWQ1uPLH0BS1xA^PNJRr,1PP412JUS1yPUP{fzRw,QFRy#@S1z%IyS1{PmP`PjPVPlPdB0\ckTS1|9LfcPBPqb5b6b7X1:A^4NURy,14^1:P}b4b3b2%0wRwP4D:W0P4O1PJPWPJPLH0BS1}P212wWS1~12wLS20f{#0R|9^PNRx,1PP412|WS21PWP{f|Rv,QFRu#@S22%IuS23PmP`PjPVPlPdB0\cknS249LfcPBPqb5b6b7X1:A^4NWRu,14^1:P}b4b3b2%0vS25P4D:W0P4O112|LS26PLP{Q22Q23PmP`PjPVPlPdB0\ckoS279LfcPBPqb5b6b7X1:A^4NLR{,14^1:P}b4b3b2Q25P4D:W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000P2Q1mQ1nQ1o?5NbPKQ1pA5ENbX8:REQ1qQ1rPmP`PjPVPlPdPfQ1sPkQ1O,TcS1sCjPBPqb5b6b7X1:Q1t144XRv75N^1:P}b4b3b2Q1uP4H0@W0P4O1Q1vP2Q1wQ1xA5rNbP4Q1yPUPEQ1zQ1{PmP`PjPVPlPdPfQ1|PkQ1sCjPBPqb5b6b7X1:A5yNv^1:P}b4b3b2PwP4D:W0P4O1Q1}P2Q1~Q20A5xNbP4Q21PWPEQ22Q23PmP`PjPVPlPdPfQ24PkQ1sCjPBPqb5b6b7X1:A5uNv^1:P}b4b3b2Q25P4D:W0P4O1Q26PLPEQ22Q23PmP`PjPVPlPdPfQ27PkQ1sCjPBPqb5b6b7X1:A5{Nv^1:P}b4b3b2Q25P4D:W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000O4Q1hQ1lP4Q1eQ1gP2Q1mQ1n14PMR{Q1:#<REQ0D#<Ru=|Lp3`S1:,1PPKQ1pA|Lu49`{ES1l,1PX8:S1hQ1qQ1rPmP`1Ku;S27,OLS24%BLRxQ27#3Q27,ALS1|#B[[S1t%3LRyg00:CRrQ27=SL6UW9S27Q1|#3\r^9yS1oPjPVPlPd%UMS28,TcS29%UES2:Q0D,ao+0;'TS0D9LfcPBPqb5b6b7X1:144MS2;1ALu7`ES2<,14^1:P}b4b3b;b<b2Q1|9`{ES1|,1PeQ1uP4H0@W0P4O1Q1vP2Q1wQ1xA|LuJ9`{ES2=,1PP4Q1yPUQ1hQ1zQ1{PmP`1KuUS2>,OLS2?Q2>#3Q2>,ALS2@#B[\xS2AQ2>=SL6VrX9yS2>Q2@#3\r^9yS2BPjPVPlPdQ29Q2:Q0\,aoS0\+0;'TS2C9LfcPBPqb5b6b7X1:Q2;?`E[S2D,14^1:P}b4b3b;b<b2Q2@9`{ES2@,1PePwP4D:W0P4O1Q1}P2Q1~Q20A|Lu|9`{ES2E,1PP4Q21PWQ1hQ22Q231KuWS2F,OLS2GQ2F#3Q2F,ALS2H#B[\xS2IQ2F=SL6VrX9yS2FQ2H#3\r^9yS2JPmP`PjPVPlPdQ29Q2:Q1E,ao+0;'TS2K9LfcPBPqb5b6b7X1:Q2;Q1E#<,AL7`ES1E,14^1:P}b4b3b;b<b2Q2H9`{ES2H,1PeQ25P4D:W0P4O1Q26PLQ1hQ22Q23PmP`1KuLRu,OLS1h%3u1ALuS2L#B[\xS2MASLu6VrX9yS2NQ2L#3\r^9yS2OPjPVPlPdQ29Q2:Q0U#GRu,aoS2P+0;'TS299LfcPBPqb5b6b7X1:Q2;%<u,ALRu7`ES2;,14^1:P}b4b3b;b<b2Q2L9`{ES2L,1PeQ25P4D:W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000Q1e,1PeQ1d#ES2:210Pp?54bX8:P2Q1mQ1nQ1:A|L^p;5bPKQ1pQ1lA|L^4;5bX8:RpQ1qQ1rPmP`Q24Q1tQ27Q1o1K^;RE,OL%3E1ALER{#B[\xASLE6VrX9y%3{\r^9yPjPVPlPdPfQ0DQ0\Q1sCjPBPqb5b6b7X1:Q2<?5[v^1:P}b4b3b;b<bCbGb2Q1|?5{beQ1uP4H0@W0P4O1Q1vP2Q1wQ1xQ2=A|L^J;5bP4Q1yPUPpQ1zQ1{PmP`Q2?Q2AQ2>Q2B1K^URJ,OL%3J1ALJR{#B[\xASLJ6VrX9y%3{\r^9yPjPVPlPdPfQ2CQ2PQ1sCjPBPqb5b6b7X1:Q2D?5uv^1:P}b4b3b;b<bCbGb2Q2@?5{bePwP4D:W0P4O1Q1}P2Q1~Q20Q2EA|L^|;5bP4Q21PWPpQ22Q23Q2GQ2IQ2FQ2JPmP`1K^WR{,OL%3{1AL{Ru#B[\xASL{6VrX9y%3u\r^9yPjPVPlPdPfQ2KQ0A,aoQ1sCjPBPqb5b6b7X1:Q1E1ALN;5v^1:P}b4b3b;b<bCbGb2Q2H?5ubeQ25P4D:W0P4O1Q26PLPpQ22Q23PmP`Q1hQ2MQ2NQ2O1K^LRp,OL%3p1ALpRu#B[\xASLp6VrX9y%3u\r^9yPjPVPlPdPfQ29Q0U#;Rp,aoQ1sCjPBPqb5b6b7X1:Q2;%<p,AL;5v^1:P}b4b3b;b<bCbGb2Q2L?5ubeQ25P4D:W0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000Q1eQ2:;5beQ1gfDRuD:O4Q1iQ1kQ1VQ0[AfZ4]Q0ZP6O1[^RZR}[Q0[\}Q0Z>1zZ]Q0b1Y86R}P4J1y%P}R}#X1=}CP}P1P}P@CF4091Y78R}#PRp#0R{,}4P}PPP{P4Q0YPFPpPUL005i\XE:-0]:'9P0%Xp1=pCPpP1PpP@CF4091Y97Rp#PR{#0R},}4PpPPP}P4Q0YPFP{PUL005i\XE:-0]:f~#0R{=>P<R}00{{S0ZQ1Y/1}7_9P41Y>9#PR}#X1=}CP}P1P}P@CF4091Y<=R}#PR{#0Rp,}4P}PPPpP4Q0YPFP{PUL005i\XE:-0]:Q00P:1Y?<R{#PRp#0R},}4P{PPP}P4Q0YPFPpPUL005i\XE:p+01CS1g#0S2:=>PQS1eQ2:#CS1v'4S1}%k<S26Q1e55?7_?P4Q1[Q02'YRp#PR}#0R{,}4PpPPP{P4Q0YPFP}PUL005i\P0%36S0YQ1[,YQR}#PR{#0Rp#E7b6P}PPPpP6Q1jPFP{PUL00p+01G#0S2L=>PRS2;Q2L+0{%kQQ2;55i7_iP4%37S291YDi#P#0#E7b71YeDR{PP%P{R{#0P9%N9PFP{PUL00P01YReR{%P{R{#0=>P>+0o%N>PFP{PUH0Sp+01KS2O#0S2N=>PSS2MQ2N#CS1h'4f@R{%kRQ2M55{3_P41Yg{Rp%Pp#0=>P<+0o%N?PF1YKg#PPUH0S%0KRp#Cp+01O#0R}Q0R5>PRJ%C}S23'4REA5u4J7_uX8:Q029>PpQ0Q#C=54J9_E4XK:p+01NS22#0S2101xpQ21/2pRp&0:pS2H+1wQ01Q0Q,2}R}&0:}p+01P#0S01%0uS1E'2S0A$0:S2KfHR}/JQ'6P4Q0Ap+01Q#0S2JfERp#0'JS2FfIRE/2iS2I$0:S2GQ2IP:PDp+01SRJ#0#E9b\4P:Q1jp+01TS1j,RFPUCs#Dg007_S2E]S]UXE:%3DS20p+01R#0#E7bDP:%Ne1RFJPUCs#DQ1j@1r}7Q1j/=}P3p+01US1~PZQ0aP4P]C{S1y%X61=6CP6P1P6P@CF409%08S2@,}S-0VSfNS2DPPQ0OPuCo%NpRJPFP9PUH0SQ2E]?]@]A]T]>XD3PZfJS0OQ1~P]C{p+01VS2P#XQ2P/=CQ2PP1Q2PP@CF409%3KS2Cp+01WS2B#0S2>#E7bKfMS2APPp+01XS2?#0S1{PSCo%NuS1zPFp+01YS2=PUH0SP:p+01ZS1x,RFS1w-1oJQ0gX8:P4P:PJQ1wPUCsS0gQ1wPJP;PUP020d64Q2@Q0h'HRJ[Q0hQ0d'H20d86[S0d20d78\J21n64P4n2001000000120000000X_3XQ3Q0d^_3^Q3P4fFRJ#NS0dp+01[S1p,RFS1u#lS1|Q1p#0#EQ0R#N#0/H4X8:PJp+01\#0S1p,}4X8:Q1|#@S2<Q1|#0S1|#3S0DPmP`p-0S1oPjPVQ1IPdPf20xf920Mcz-0rfS2760wfPAQ27H0OPBPqb5b6b7X1:X::WMQ1oAb8461H68[^1:^::]MP4%3Ep+01^#0#ES27PEPQO4b4b3b2Q0d#0Q2<Q0DPmP`Q1oPjPVPlPdPfALfacS0D20xf760wfPAQ0DH0OPBPqb5b6b7X1:WMQ1o19\6Q0Y[^1:]MP4Q27,HEPEPQO3b4b3b2-1kJD:Q1|Q0zD:O3b0I1jJ0XQ0g/2UP:P;P:&1hJQ1uPUCsR\PUP:P\P;P<H1fP4J1eQ0lP:P;P:Q1oP4PrQ2EQ2En011000003001000010000Z04:g00:_PUP4J0XQ2EQ2E01d4b0brb?W?W@WAWTW>PEP4P}PuPiP?P<N;1cbFWSWUQ0OP4PEP}L1bW0Q2Ge403WFP4O1Q2KQ2FQ2G<0R4WFP4O1n200110800021110410101c08Q2HQ02,JJ'6P2%XSPSP1PSP@CF:0=SCQ1EQ1EPUQ1EPWQ1EPLFgPe%XuP3P5PZQ0RP4P]C{Q0h#ES0h,He-0VePEPPQ2@PRCo%N{Q0P#dS0P<05UQ2P#0%09R\'JQ2D/Jg'6%0>S2HQ2HPUQ2HPWQ2HPLFgS2H]B]?]@]A]>XD3P:P3PJP5H0Z=fZ]Q20Q0j7bDP}PPPhPeCo%NRQ0i<05UQ1~#0/JhQ2A/J{'6Q0kQ0mQ0oQ2P,QFRh#@%IhPmP`Q0sb3b2CtQ0keWBW?W@WAW>PpP4PuP?P9P7P8N;0YW0P4O1PuP1PuP@CF:0=uCP21=pCPpP1PpP@CF%0JRhPhPUPhPWPhPLFgP41=JCP3PCPZPEP4P]C{Q0h,H{-0V{Q0aPPQ2@PgCo%NKQ0P<05UQ1{/J\fP/JS'6Q2H]B]?]@]A]>XD3PZP}PCP]C{Q0u,HR-0VRQ0OPPPtP{Co%NgQ0t<05UQ2>/JtQ0b/JK'6Q0xQ0yQ0wQ2?,QFRt#@%ItPmP`Q0vb3b2CtQ0xeWBW?W@WAW>Q0RP4PJQ1[P=P>P9N;0YW0P4O1PJP1PJP@CFP2Q0R/=1Q0R/=@%0}RtPtPUPtPWPtPLFgP41=}1P3P1Q1yQ2CQ0h7bKQ2APPQ2@PSCoQ1zQ0P<05UQ1x#0/J\fRS1x/Jp'6Q2H]B]?]@]A]>XD3S1yPZQ0OP1P]C{%3gR\Q0|7bgQ1cPPP~PKCo%NSRtQ0{<05UQ2=#0RC/J~fQ/JuR~'6Q11Q12Q10Q1w#lRh#@R5%IhRhPmP`Q0~b3b2CtQ11eWBW?W@WAW>PEP4P}PiP?P<P=N;0YW0P4O11=}@P3P@Q1yPZQ0OP@P]C{Q149b\gQ1cPPPsPKCoQ13>05tU1JCs/6~Q18Q19Q17P5PhPmP`Q16b3b2CtQ18eWBW?W@WAW>PEP4P}PiP?P<P=N;0YW0P4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000Q0QQ0QPUQ0QPWQ0QPLFgPPQ01P}Q1EPQQ0cP4Q0RP<P6N:1abqbBPSP6D:%kKRh&1`KD:Q21=>PJR5Q21#CS21'4S0RA5Sh57_SeW?W@P6P4O2n2001000000121000000W0WAP6P4O2n2001000000121000000W0Z06:P6P4O2n2001000000121102000W0WTP6P4O2n2001000000121000000bHW>XD3XK:Q1VQ25=>P>RhQ25#CR~'4Q1W/1h7_8[^D3^K:PPPwP7PJP8I1_A>Pw7RC,1b%Cwg05C1,4PRw55C'9P0A>P|9RC,1b%C|=5CwAcHh~%~h1M~N5cH'9P4f}#0=>P=,1bQ0Z/1wp+01@Rw#0R~=>P?Rh%C~RC5cH%~h1MCN5cHQ1GPhPC1QFwRw#@RC%IwRwPmP`PjPVQ1IPdPfPfQ1s00DzPAQ1JDmPBPqb5b6b7X1:X::11v6Q1K[^1:^::P4Q1ePPP9O3b4b3b2PCPwPmP`PjPVQ1MPdPfQ1QPAQ1QH0OPBPqb5b6b7X1:X::X=:Q1R148_'1Q1U[^1:^::^=:P4PPQ1vQ1eP7O4b4b3b2Q1VP?P8P6P4O3Q1}Q1WQ1e'17_8P2p+01D#0R|=>PiRs%C|;57Q1X/1sp+01E#0Rs=>PDRD%CsS1X;59RtQ1Z<1^DP4p+01FR\#0R]=>PeR@%C]S1Z;5>RZ%k9,4>/KN/1@R@<0R4XVtP4O1Q1Y/1D1QF\R\#@%I\PmP`PjPVQ1MPdPfQ1aPA20;IkQ1N5LfH0OPBPqb5b6b7X1:X::X=:Q1R/18Q1T/KN/17[^1:^::^=:P4p+01IS1T#0R\=>PgQ26P?P7O4b4b3b2:03Z@WVP4O1n200100000021000011000c05W>XD3XK:O5Pb17~OP?Q15#<R@?rL~CxP@PCPwPmP`PjPVPYPd%U@Rw-0Ma-0rfPBP4P8Q0qQ0rH0pb5b6b7%B@P4b4b3b2Q0f$0:RCP01V861w87S0f[R~1w681V78RZ[Rt1w79\ZB1\864S0rP6n2001000000120000000UXO:XH:S0qP~\C^O:^H:S15P4PPPMp+01AS1V,QFRZ#@%IZPmP`PjPVPYPdQ28=Zfa-0ffPBPqb5b6b7%DMQ2E[P4b4b3b2PuO41wMPP0P~PtQ0f1V97[Q0rP4n2001000000120000000VCXO:XH:Pt\C^O:^H:P4PbQ2:/7OPQQ2:9r@LCxP@Q1g,QFRQ#@S1g%IQS0rPjPVPYPdAZfwa-0ffPBPqb5b6b7%D@Q2E[P4b4b2Q00P:174MS0f,2PS26X8:P@A^b|OPiAr@L|S1aChP6Q26176Mp+01H#0Ri/7ORb,4vAr@Li,7{Rv60u@X8:P2Q2L#DQ2LPUQ2LPWQ2L/2LI0?178M@0JXb>0u@vQ1x%DiP@B0<9MXS1x174ORv'4PKAr@L4RbChX8:P:Q1x17;ORQPK1AL;RC,7@S1Y174@RtDvX8:177@Q1F#<R~<0JgQ1T#@%3\p+01JS1F,QFRZ#@%IZ1OL;11;;%BC[\xASL;6VrX9y%3C\r^9yQ0H,OLS1}Q0H#3%BO[\xS1WQ0H=SL6VrX9yS0H%3O\r^9yS1vPjPVQ1IPdQ28,?cQ1O'TRCQ0G,aoR;,?ag03oS:0t:o,?w,?z3y1?cw%U~'TRZ/Tz/?w5ZfPBPqb5b6b7X1:X::Q0f/4XS0fPQP6Q1Y14t~S0G/46/7@Dv^1:^::P4P}Q1[O2b4b3b;b<bCbPb2H0IP@177M@0JXQPgQ1YCheP\P4H0@WFP4O1PiPUPiPW12iLI0?P212\UP\PWP\PLH0BP@Q1xQ1F#0Rg;^OPKAr@LgChP412gUPUP@B0<=MXS1x/4vPuPbChX8:P:Q1x17UOS1FPu1ALURQ,7@S1YPtDvX8:B0<>@~17U[S28PLPSCxQ2O#@Q2N#3p+01LS2O,QFS1U#@Q1U#I1OL^S1U%3^%B[[\xS1QASL^6VrX9yS1K%3[\r^9yS1JQ1}Q1WQ0HQ1v1OLU%3U%BQ[\xASLU6VrX9y%3Q\r^9yPjPVQ1IPd1?T;Q0>,ao,?w,?z5yCQ0\,?T1?oz5yZ/?w5ZfPBPqb5b6b7X1:X::Q0fQ1FP6Q1YQ0GQ28PLP6Cx/7@Dv^1:^::P4Q1cPeO2b4b3b;b<bCbGbWbPb2H0IP@17>MQ1F80JXPSQ1YCheQ2NP4D:WFP4O1PgPWPgPLH0BP2Q2N/2WQ2N/2LP@Q1xQ2O#0Rg;^OPuAr@LgChP412gWPWP@B0<?MXS1x/4vPJPbChX8:S2OP:Q1x17WORvPJ1ALWRT,7@S2NPtDvX8:B0<<@~S1Y17W[S1FP@PpCxp+01MR~#@S28%0~R~#3S1sQ22,QFRQ#@R^%IQRQQ1UQ1QQ1KQ1JQ1}Q1WQ0HQ1v1OLW%3W%BT[\xASLW6VrX9y%3T\r^9yPjPVQ1IPd1?n;Q0U,ao,?w,?z5yCQ0\,?n1?wz5yZ/?w5ZfPBPqb5b6b7X1:X::Q0fPvP6Q2NQ0GQ1FP@P6Cx/7@Dv^1:^::P4Q2DP{O2R{b4b3b;b<bCbGbWbPb2H0IP@B0<<MXRX/4vPpQ2NCheP~P4D:WFP4O112gLPLQ2OP:Q1x17LOROPJ1ALLRJ,7@RgPtDvX8:Q1Y17L[R[Q0@#<RtPpCxQ28Q1sP^PQ1OLL%BJ\y\xASLL6VrX9y%3J\r^9yQ1UQ1QQ1KQ1JQ1}Q1WQ0HQ1vPjPVQ1IPd1?o;Q0?,ao,?w,?z5yCQ0\,?o%Ut/?z5yZ/?w5ZfPBPqb5b6b7X1:X::Q0fPOP6PgQ0GP[PtP6Cx/7@Dv^1:^::P{b4b3b;b<bCbGbWbPb2H0IP@14XOPpPgCheP~P4D:WFP4O1n200100000021100011000W0P4O1n200100000021100011000W0P4O1n200100000021100011000PPP4D:WtZ07:P6P4O2n2001000000121102000O4b0bXb0P:174NRg,2@X8:PN17NN,z:H0II1[1VhNRhePhP2Q1V#0Rh#DPhPUPhPW12hLI0?Q1\#0RO9r@L/VNQ1c%DO1VbNX8:RbQ0nQ2:P4H0@W0P4O1POPUPOPW12OLI0?P2Q2:/2UQ2:PWQ2:PLH0BQ1a/VNP412|UPUPbQ0nPsP4D:W0P4O1P|PWP|PLH0BP212sW12sLAr@L]/VNP412]WPWPbQ0nQ2LP4D:W0P4O112]LPLPbQ0nQ2LP4D:W0P4O1n200100000021000010000W0P4O1n200100000021000010000W0P4O1n200100000021000011000%Ch/VNRhePhQ0qQ15P4Q1ePNQ1gQ0rPmP`20`DN%3D%3NRhQ2;00HN#3[[Q1Z00`NQ1Z#3%Ci00HN#3\h[PjPVPYPdAZfka-0ffPBPqb5b6b7%DNQ2E[P4b4Rib3b;b<b2P8O4Q1e,wNQ00P:12DgX8:%~DQ1X/MN5cHP4Q2;/2gQ0qQ15P4%C\R\PNQ1T,QFRD#@%IDPmP`Q1h00`NQ1h#3%C~R~00HN#3\h[Pib3b;b2P<O41wN\Q00P:Q1h/2gX8:Q2M#~Q1h/MN5cHP412~gp,6R_shadP5Q0R%~5R~Q21/MNRg17<NR\1V4NX8:RhP^PQPmP`Pib3b2Ri:0v<NP5P=D:P\Q23,44RD/VNX8:176NRb17?NR]/44RW/VNX8:P:14<6R@/7NRsPhB0v@Ni14\bRhB1Z<6NR2J0XQ21P4D:P5P=D:P^PQPmP`Q0pQ0>$1g-1Y:R|Q1]60e:Q1_+0g21X:NQ1_61m:RUQ04$0CROQ1]Q1^+0g40NQ1`+0k+0y;ejPVQ1HQ1L?]7Y7]7?]6YPdPfQ0F$02/?k9ZfcRXPAPfPfQ0@$02R{Q1OPcCjPAPfPf20Ma{PAQ0DDmK0zPBPqb5b6b7X1:X::X=:178NR{,24Q1S/16%B7Q29[[[^1:^::^=:P4Q1[PPQ2J=>PEREQ02PKfXO6b4b3b2Q06Q0761WFg01Z?&1qFRK'1Rtg01[:,1KR['9RwQ0B,VKRK'9P0PwPKQ01=>P}Q01#CQ0}#G#GR}#<RZ,ALRC35P4P0PtP[Q1j#0R0Q1c5>P%C0;5C\KP4Q2B,QFRF#@%IFPmP`1OLZ%3Z%BC[\xASLZ6VrX9y%3C\r^9yQ0pQ05$0CRyQ1_80NO&081$0C&0C1:0e:|B0e:|yQ1]-0gO40N60NUQ1`+0k+0y;ejPV&0E>?]=Y9]Y8Q1L&0E=?]9Y7]=7]6PdPfPfQ0C$02RYQ1;$0G$0G$0G#<RU#U+0DPAPfPfQ0}$02/?k-1UzPAPfPXPAPfQ0E$02RXQ1P'TRk9LfIPAPfPfQ1<#U-0;Y-0DkPAPfPf20MaXPA1ao}9LfIDmDmK0zDmDmPBPqb5b6b7X1:X::X=:XN:X[:X\:117U17=N,28RUQ1b14>_'1Q1<,K<95=_%B<A5=<C[[[\U[[^1:^::^=:^N:^[:^\:P4PRPp&1TGPPQ1p#CQ1pfT5>PP=PePuQ1cQ0cQ0eO<b4b3b;b<b2Q2>Q0b5>PQ2>#C;5CeXJKXy[XxtP6P4O2n2001000000121000000X0wP6P4O2n2001000000121000000b0P^PQPmP`PjPVPlPdALfccPBPqb5b6b7X1:1144^1:P4%~EO1b4b3b2P\1M4NRE$07RlQ23/MN1MDN$0735X8:Pb1M]N$07R]1MWN$0775EX8:P:Ps1M{NR{=5]lX8:P<&074R]14?8/7N/MN$07Rl75{X8:P6&07?R??54lX8:P@A5?8]X8:P^PQPmP`PjPVQ1MPdPfPIQ1NQ1N=yczCjPBPqb5b6b7X1:X::X=:Q1RB0J486758^1:^::^=:P4P9Q03Q1[O3b4b3b21MsNB0a@NiD:1MbNB0a6NiD:1M\NB0a<NiD:PhP2J0XQ21P4D:P5P=D:Q0R#~95~gePSO;WaZ03:P6P4O2n2001000000121102000bZb0W`X]:P6P4O2n2001000000121102000bYb0bZbYH0iWwWvP6P4O2n2001000000121000000b0boWSWUXE:H0iH0iPHPPQ1dQ1fH0TebmWiWhP6P4O2n2001000000121000000W0WgP6P4O2n2001000000121000000W0WXP6P4O2n2001000000121000000W0WfP6P4O2n2001000000121000000b0bpWJWIP6P4O2n2001000000121000000buWJWnP6P4O2n2001000000121000000W0WeWdP6P4O2n2001000010121000000W0P6P4O2n2011000000121000000W0WcP6P4O2n2011000000121000000W0WbP6P4O2n2011000000121000000W~WlP6P4O2n2001000000121000000W0W}P6P4O2n2001000000121000000W0W|P6P4O2n2001000000121000000W0W{P6P4O2n2001000000121000000W0WzP6P4O2n2001000000121000000W0WJP6P4O2n2001000000121000000b0WsXL3o"). Qed.

Lemma av_fs : fs_avoid W Σ.
Proof using Σ m W HA R_img R_grant R_shad R_fsb.
ltac2:(KReplay.run1 (kr_t_RT_sep ()) ["CompFs"] "p'0h01Hh14__x1h27__arithh34__ffh48__varmaph55__with64__x2h71zi001zh83Hf'h93Hp'h:4__x3h;3Hinh<2Hah=2Hfh>4Hin'h?2Hph@1xi011xhA1XhB2_HhC1khD1pi021phE2k'hF6__sat3hG6__sat4hH3Hc'hI1ahJ4cstrhK5cstr0hL1fhM2fkhN1AhO2EkhP2EphQ1PhR3_H0hS3_H1hT3_H2hU4__x4hV2f'hW1lhX1ohY2p'hZ1si031sh[1yh\2G1h]2HFh^3HFrh_3HNDh`2Hcha3Hfzhb2Hkhc3Hk'hd2R1he2R2hf3_H3hg3_H4i041ei051np%0p%1p&0p&1p;1p;2p;3p;6p;4p;9p;<p;5p;:p;7p;8g0162k11NTg01Pnk11MTg00AYj1@Tg00B>j1FTg00IXj1;Tg000GS00k20ITg01JXk10wTg004lj37k10HTg01MHk10eTg01NBk10\Tg01O:k11LTg01P4k11ATg01>Gk11?Tg01?Ak11;Tg003lk10NTg004Lj3eTg0000j3?Tg00<mj2iTg00JVj3qTg00Mjj3UTg01GAk10yTg02cek60xTg01KRk30vTg01I>k20rTg00`Dj25Tg01@;k10qTg001Gj21Tg002?R0j26Tg05D5k20aTg00oaj3ETg050Lk10[Tg04oKj4sTg052Bk10YTg053:k11KTg0542k11ITg04Jgk21ETg00X0k11>Tg00ncj3pTg000gk10PTg00CJj2zTg00Chk11:Tg00DFk118Tg00E1j2|Tg00FZk216Tg00G<k215Tg00Ghk314Tg00HGk413Tg02bik60}Tg00c]j1kTg013:k10{Tg00`aj4{Tg00ETk10zTg01`Ij1lTg008<R1j23Tg01nNR2j10Tg0393k20uTg039Vk30tTg03>]j68Tg00K0k20GTg036Hj4`Tg05E2j2xTg008Vj4cTg03E:k30pTg04K`k40oTg05Enm90nTg03IFm90mTg01FHk30lTg01edk10kTg016jk10jTg017hk10iTg018dk10hTg019`k10gTg01:[k10fTg01;Wk10dTg01<Qk10cTg01=Ok10bTg01A7k40`Tg01B8k10_Tg01C4j2NTg001cj2dTg01CQk10^Tg01DOk10]Tg01EKk10ZTg051Dj2tTg024Lj1oTg00<4S01k203Tg02OGk21JTg01mnk20XTg04nQk20UTg054jk10CTg055hk11HTg056ck21DTg057Ck31CTg057^k11BTg058[k11@Tg00dYj2MTg02<Pk30STg00^ck60DTg04l:j34Tg04kBk10ATg006ak40:Tg03>?k11=Tg02Q:l<fTg02=Um90@k60LTg05@Fk519Tg04m:j1=Tg01]Mj2}Tg01^5k300Tg01cOj3~Tg02HIk301Tg00j^k10=Tg01`hk208Tg01b:k30KTg01bck217Tg00e6k302Tg03<]k20OTg003Sj1_Tg00J6S02k20ETg02DEj1wTg005cj6uTg05>Jm:0JTg05?Hk10TTg00>_k30VTg00?<k312Tg00a?k311Tg00KSk404Tg00L>k70BTg00MFk810Tg013Xk70~Tg05;Qk41FTg02:Wk21GTg048am<0WTf0R3#@#@p=h%@3#@#@#@p=Jg007AR4P4f1R5P3H0:p=bg00VYR6/d3p=[A7436p=Af3R7f2R8'11153'3p=v1653,68p=Og00iDR9>0V43p=rB12493p=B%k5,58/M3p=Z20G43p=GB11453p=CP8g00O;R:g00OZR;P;g00P:R<P4P5g00QaP3H04g00QAR=K0Bp=91585/13p=>P4P9P5P3H0:p=<%k3,55p>0|1M85/13p=QP7P:P;P;P<P8P5P3L10p=Vg01d2R>=793p>0<A7463p>0;A7453p=2A7953p=:P9P4f4R?P2P7P8P>P6P5P>P6P3M<fp>0sP9P4f6R@P2f5RAP?P>P6P7P8P5P3M<fp>07P8P:P;P;P<P4P5g01e=RBP3H04P=K0Bp=yP?P:P;P;P<P7P:P;P;P<P4P8PBP5H04P=K0BP3K0~p=KA793>p=RP9P4P@P2PAP?P7P8P5P>P6P3M<fp>05P9P4P3P2P5P8P7P?PAP@f7R=f8RBM<fp=YA7978A7953'3p=]1353,38p=I1163p=H&0A3,d5,68p=gA48539747p=SP4P720U85$0CP6H1F=743p=T21G53,18p=\B0V495=743p=j&0A3,d5p=n1165/63p=WA7485/63p>0RA7985/33p>0QA7478A7453'3p=PP9P4P4P4P2P2P7P8P5P>P6P3N<0Wp>1<P4P4P3P5P8P7P?P6PAP@P=PBM<fp>06P9P4P4P4P2P2PAP?P7P8P5P3N<0Wp>0?P4P4P=P@PAP?P7P8P5P6P6P3M<fp>09P4P4P3P5P8P7P?PAP@P=PBf9R2M<fp=^P9P=P@PAP?P7P8P5P3N90@p=m%=3,55p=X1585/M3p=DA7485/33p>0MP4P?P7P8P5P3J0Lp=L1578/15/33p=a1185/33p>0>A4785/53p>0Fp,2ΣR:p,1mRCp,2HARD&1N:RE$1MRFg00THRG#@RH#FRI#F#@#hRJ#@#F#h#F#J#J#J#;RK20I44RL&0wE%@HS03#@RM#@RN#hS04#h#JRO#JRP#JRQ#F#@#h#F#J#J#J#;'b1bFKRR37&0eE%@Q#h#;RS'bRT&0\ERU%;ORO'bRV&1LE%;PRP'bRW&1AERX/bORY&1?ES05%;Q'b&1;ES06/bS&0NL5eL5eLRS9eLRRQ5eLRZ5eLR[5eLR\5eL9?LRA7LTRA?LR\A7LVRA?LR[A7LWRA?LRZA7LYRA?LRQA7LRRA?LRS1iLR3q3U3U3U3U3U&0yE9?LReJ0xB0vEFKP0%[FS0720rFO#A15FKRR&0qES08'1PRg02jmg02ijPFCvPRPPg014<PFCv'63OS09p,1WRP00a:S0:P3Q07Q09%;JRJ,5FRSQ03#FRQ#;RY5EPPPPFP6&0[:RZCsRWPPPF%;GR[&0Y:RVCsS0;PPPF%FGS0<#@R\#;RT&1K:R]CsS0=PPPF%;HR^&1I:R_CsS0>'6S0?g05FgR`-1EPS0@%h\Ra#;Rb,5XS0A%;MRM5EPS0B%@a#;Ra,5US0C%;NRN5EPS0D20I49Rc%r3%B3Rd;ZM=EPMXMcS0E&1>:Re3pRf'6S0F'6S0G'6S0H'6S0I'6Rg'6p,5R_fsbS0JPSPYg00TmS0K$0NRhQ0K$0PRi1z45Rj&1:4Rk&184Rl1|4GRm%GJ,CmRn39216l<R<P3P8g00UYRog00V9Rp'iS0L21538=7opdB14465H13Rqb3b4b5X14153JRr,13^14P3PFO1Rsb2PhPiPjPk%GY,CnRn%GKS0M,Cm59lP<Pqb3b4b5X14153K9>rY^14Psb21<53=?ceS0NP:PCPDP8P5P3J0}%JQ#J#J#;RQ,5FRs/18%k5Rr=>8R%[r3OP011s7%k8Rr=>7R%[r'615SYRrP?AZ?7MS0OPSCvP311sA%kARt=>@R%[t'611r=20|=@?QMSPhPiP41z48S0PP5&0{4RSC{S0QPkPl%GQ,Cm1|4HRr59lS0R&0z;R;A9lnrCVP<Pqb3b4b5X14X64A>3Q5155J?>Y8[^14^64P3PBPFP8O3b23qWBWAP5P3O2n2001000000121000000bIW;XE9XL4O5PWPgA79>>Rg%l>RW$0<RY%lWRJ#l#l#l#lRn$0<Rt&0<JRR'3Ru'3Rv'3A7466S0S&0;[S0T&0;TS0U&0;^S0V'3S0W'3Rw'3RxPgPvQ0SPw&0H9Rv&0H4Rg%05Ry%03S0X'21:5320u5340tX[9X@9Rz1i46R{P{I0sPYPuQ0TQ0WPvPgPzP{PWP[1i4[RuK07PtPRQ0UQ0VPvPgPzP{PnPT1i4TRRK07PvPgPzP{PJP^1i4^RtK07E8E8E8PhPiPSPkPlPl20G46RYPYPlPlPY%G[R|PlPlPY%GTR}%G^R~9ylYDKDKDKP<Pqb3b4b5PxP3b2S0YC`,x>Q0;Q0I%RWS0I1:WWS0;1:WnS0Z1:WJS0['3S0\'3S0]'3%A[S0^12[[S0_12[TS0`12[^S0a'3S0b'3S0c'3S0dQ0IQ0]Q0^Q0cPvPgPzPWP[PuP{K05Q0;Q0\Q0_Q0bPvPgPzPWP[PuPWP[PuM9YQ0ZQ0[Q0`Q0aPvPgPzPWP[PuPnPTPRM9YPvPgPzPWP[PuPJP^PtM9YE8E8E8PhPiPSPkPlPlP|PYPlPlP|P|PlPlP|P}Ayl|~DKDKDKP<Pqb3b4b5Q0dP3b2S0[C`,xWQ0?Q0HQ0=Q0>%RnS0>1:nWS0=1:nnS0H1:nJS0?'3S0Z'3S0\'3%ATS0;12T[S0]12TTS0I12T^S0e'3S0f'3S0g'3S0hQ0>Q0\Q0;Q0gPvPgPzPnPTPRP{K05Q0=Q0ZQ0]Q0fPvPgPzPnPTPRPWP[PuM9YQ0HQ0?Q0IQ0ePvPgPzPnPTPRPnPTPRM9YPvPgPzPnPTPRPJP^PtM9YE8E8E8PhPiPSPkPlPlP}PYPlPlP}P|PlPlP}P}Ayl}~DKDKDKP<Pqb3b4b5Q0hP3b2S0?C`,xn%RJS0H1:JWS0Z1:JnS0=1:JJS0\'3S0>'3S0i'3%A^S0j12^[S0k12^TS0l12^^S0m'3S0n'3S0o'3S0pQ0HQ0iQ0jQ0oPvPgPzPJP^PtP{K05Q0ZQ0>Q0kQ0nPvPgPzPJP^PtPWP[PuM9YQ0=Q0\Q0lQ0mPvPgPzPJP^PtPnPTPRM9YPvPgPzPJP^PtPJP^PtM9YE8E8E8PhPiPSPkPlPlP~PYPlPlP~P|PlPlP~P}Ayl~~DKDKDKP<Pqb3b4b5Q0pP3b2S0\C`,xJCcQ0@Q0GPPp,5R_imgP`Q0Lg03EV>0pL`=7opdH0oQ0BQ0FP:PCPPPDp,7R_grantRpQ0APMPhPiPjPk%Gb,CmRo99lmP<Pqb3b4b5X14153bRb,13^14P3PXO1RXb2PhPiPjPk%GMR`,Co%GO,CmRo59lP<Pqb3b4b5X14153ORO9>bM^14PXb2N90nQ0DPfP:PCPPPDPpQ0CPNPhPiPjPk%Ga,CmRp99lmP<Pqb3b4b5X14153aRa,13^14P3PUO1RUb2PhPiPjPk%GN,Cp=9loP<Pqb3b4b5X14A>aNO^14PUb2N90mB0l:CD&0k:P0&0jES0C&0i:S0D&0h:S0A&0g:S0F&0f:S0B&0d:S0L&0c:&0b:REQ05Q06Q08H0`&0_E/5^1N^N'd&0^EQ0<#FRD#F#F#F#F#F#;'5%hI#;,N^'d&0]E&0Z:'63O3OS08'6S06'6S05'6S0G'6S0@'6S0=PfP3Q0CQ0=P0Q0DQ0@PfP3Q0DQ0@P0Q0AQ0GPfP3Q0AQ0GP0Q0FQ05PfP3Q0FQ05P0Q0BQ06PfP3Q0BQ06P0Q0LQ08PfP3Q0LQ08P01t6ZS0>1t[VS0Z1tT]1t^_'6S0i%Rd1:dWPdPnPdPJC]3I%H3R_%B5R]#0RV7g3%r5RZPFPVP3CS%o3RVP:P]P[CT3OXD4-034'6XMcRE=pceRI21JceS0H20Xce#0/1N%R31:3WP3PnP3PJC]3IRN20U:5RC$0C$1H#021Dd8XMc>1Cce-0Xc#0'2[^C9&1BC%@D#;,N^g05B5&1@:'M3\\N^C93OS0q'6S0r'6S0s'6S0t'6S0uPfP5Q0>Q0uP0Q0ZQ0tPfP3Q0ZQ0tP0Q0iQ0sPfP3Q0iQ0sP0PIQ0rPfP3Q0rP0Q0HQ0qPfP3Q0HQ0qg00oDp4p710Rfp-0\3RN&0P5RDP0Ap853A??38P?P5O1[^@7RC[A?735P7P5O1[^@8Ap785[RdAp?78\CB0S853P3n2001000000120000000WWWQWNPd^WD^QN^NfP3PcQ0EPeQ00P4P9A?c3eRfAZZ]M=EPM[P3Q0NPEP5O1\f^@cRf\IS00PI\fS0EB0ScEeS0vf<RE1<85RfP3J0D%BfRZ#R1:ZWPZPnPZPJC]3I1<78R]#BRN#0RD9g_3A4FD3,j]PVP:PNP[CT3OXD4-034'6S0wP0%RN1:NWPNPnPNPJC]3IS0x1<?7RN#BR]#0RD9g_3A4FD3,jNPVP:P]P[CT3OXD4-034S0yQ0O=EPMP31<A?#BR]#R1:]WP]PnP]PJC]3IS0z1<=@R]#BRN#0RD9g_3A4FD3,j]PVP:PNP[CT3OXD4-034S0{Q01P41<B=RN#BR]#0RD9g_3A4FD3,jNPVP:P]P[CT3OXD4S0|AZB=MS0}=EPMP3f:R]/<2RN#BRD#0Rd9g_3A4Fd3,jNPVP:PDP[CT3OS0~P0f;RD/<]RV#BRN#0Rd,n5,W5S10%rVA4Fd5%o5P:PNP[CT40RS11AZEDMS12=EPMP3f=RN/<E#B#0,n7,W7S13f>Rd/<NRV#r%BVRV#0=4F?%o?P:PVP[CT40RS14P0f?RV/<dR_%B_R_#0=4FA'jS15%oAP:P_P[CTS16f@R_?ZVMS17=EPMP3fARC/<_RU%BU#0=4F='jS18%oBP:fBR:/<C#BP[CTS19P1%R:S1:P:PnP:PJC]:0Q:WS1;fCRU#0Ra#A12a[PaPTPaP^CP3IS1<PN%RUS1=P9P>fFRO/<3=?ceS1>&0AyRy,dN,WNS1?fHRoPF%08RpPdCSS1@%07Rj#A12j[PjPTPjP^CP3IRj]=]?];XC9P4P9fERXP>H0:=?ceS1A%0>Rb,nE,WES1BfGRLPFPbPNCSS1C%AbR}12b[R|12bTS1D12b^RY'3Rz'3Rv'3S1EPxP}PvQ0SPwP4P4PgP3X@4RwPg1253$1=X[4X@4RvPbP6PwPwQ0X,i4X@9S0XP{H1<R}P6P6P{M<fP|PzQ0TQ0WPgPwPgPvPbP}P[P[PuN906Q1DPYQ0UQ0VPgPwPgPvPbP}PTPTPRN906PgPwPgPvPbP}P^P^PtN906E8E8E8Q0YC`Q1EeS1EW=W?W;fDR}P3PUP=P7N90@W0P3O1PUPnPUPJC]:0QUWS0YP11:}WS0VP}PnP}PJC]S0U%0XRb#A12b[PbPTPbP^CP3IS1DP31:XWS0WPW1<o3=?ceS0T1dVy,WVS0SfJRYPFPpP_CSS1FPj]=]?];XC91<LW=?ceS1G%0WRz,nd,WdS1HfIR|PFPzPVCSS1I%AzS1J12z[S1K12zTS1L12z^S1M'3S1N'3Rx'3S1OQ0dQ1JPxQ0^Q0cPgPwPgPvPzP[PwPwQ0XPWP[PuJ0?RxP{L09Q1KQ1NQ0_Q0bPgPwPgPvPzP[PxP[P[PuM:^Q1LQ1MQ0`Q0aPgPwPgPvPzP[PxPTPTPRM:^PgPwPgPvPzP[PxP^P^PtM:^E8E8E8Q0[C`Q1OeS1OW=W?W;POP3PXP2PAGmW0P3O1PXPnPXPJC]S0[P11:OnS0a1:OJS0`%0LRx#A12x[PxPTPxP^CP3IS1MP31:LnS1LPn1<Y3=?ceS0b1dCy,WCS0_fLS1NPFPpP:CSS1KPj]=]?];XC9S0c1<|n=?ceS0^%H_S1J%0nRp7g_S0dfKRyPFPpPCCSS1P%ApS1Q12p[S1R12pTS1S12p^S1T'3S1U'3Rz'3S1VQ0hQ1QPzQ0;Q0gPgPwPgPvPpPTPwPwQ0XPnPTPRJ0?RzP{L09Q1RQ1UQ0]Q0fPgPwPgPvPpPTPzP[P[PuM:^Q1SQ1TQ0IQ0ePgPwPgPvPpPTPzPTPTPRM:^PgPwPgPvPpPTPzP^P^PtM:^E8E8E8Q0?C`Q1VeS1VW=W?W;PoP3PLPDP=GmW0P3O11:LJS0?PJQ0c1<|J=?ceS0cQ1J%0JRe7g_S1JPyPFPePCCSS0e%AeRz12e[S0I12eTS1T12e^S1S'3S0f'3Rp'3S0]Q0pPzPpQ0jQ0oPgPwPgPvPeP^PwPwQ0XPJP^PtJ0?RpP{L09Q0IQ0fQ0kQ0nPgPwPgPvPeP^PpP[P[PuM:^Q1TQ1SQ0lQ0mPgPwPgPvPeP^PpPTPTPRM:^PgPwPgPvPeP^PpP^P^PtM:^E8E8E8Q0\C`Q0]eS0]W=W?W;PoP3PLPDP=GmW0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000%0:Rt#A12t[PtPTPtP^CP3IS0\PFPaP]P3P@I19A4Fa]S0m,1sQ0m%=aS0lg05C1,5FRt3>'6P0%0}Rp=4FDRe,1s%=pS1S=>etAZOXM=EPMP3%0ORe=4FNS1T,1sA4FxdS0n/XxS0k/1t%0oRt#=RxADY3M=EPMX74A4FtVRs%0|Rv#=S0f=D3M=EPMXL4P1%AtPtPTPtP^CP:0Mt[Q04#;Rt1N^v5\MPA%AvP4P61N^39\MtX74S041}^6%[^Rg11661N^6Rw#[[[%H^RRg00:CRuB00^65UW<%Hw\u^<RPhPiPSPk%GtR6g03oS9~4~601499l`P<Pqb3b4b5A\MtwRwP3b2bFbGPwe%0YRwP3J0LW0P3O1PvPTPvP^CP:0Mv[P112w[PwPTPwP^CP%0yRy,N^9\MtP312y[P[Q041}^[%H[1N^[R{#[[\gB00^[5VuX<R%H{\u^<RPhPiPSPk&0=G9~4~:014699l`P<Pqb3b4b5A\Mt{R{P3b2bFbGP{eQ1N#0R{P3DLW0P3O1PyPTPyP^CPP112{T12{^fMS0I#0RG,N^9\MtP312GTPTQ041}^T%HT1N^TRz#[[\gB00^T5VuX<R%Hz\u^<RPhPiPSPk&0=\9~4~:014699l`P<Pqb3b4b5A\MtzRzP3b2bFbGPzefNS0X#0RzP3DLW0P3O112G^P^Q041}^^1N^^R\#[\R\gB00^^5VuX<R%H\\u^<RPhPiPSPk&0=H9~4~:014699l`P<Pqb3b4b5A\Mt\R\P3b2bFbGP\ePzP3DLW0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n20010000002110001100011MxR\eP\Q0JA4Fv_R\Q0f'5S0f/MMS0JPMQ0K2084J2084W2084>60K460K4g01dQ+17;ehS0KPiP4Q0PP51z47S0PC{RtPkPlQ0<,|4R699l`P;PlQ0RP;1Cr6>024`99lmCVCVP<Pqb3b4b5X14X64X:411M8S0RA>5Q8AD7?M,18[[^14^64^:4P3%=wRQA4FwCR~PFP5P7O5b2PhPiPtPkPl1CmrRmQ0M,C6RH59lP;B024m`RR/C`S0M=9lHCVP<Pqb3b4b5X14X64X:41535RH158K'1AD58M/5MS0<157K'1[^14^64^:4P3PFPQP~P8O4b2Q0NQ00Q0EQ0vfWRKPfP3J0DQ0wP0Q0xQ0yA4FzX%=z;DMRuPMP?Q0O/1uCaP3Q0zQ0{Q01P4Q0|fR#0Ru=4F|%=u;DMRuPMPBQ0}/1uCaP3Q0~P0Q10Q11fVS11#0RuQ0I54F%=u;DMRuPMPEQ12/1uCaP3Q13Q14P0Q15Q16fZR0#0RufQRg54F%=u;DMRuPMP_Q17/1uCaP3Q18Q19P1Q1:Q1;Q1<PNQ1=P9P>Q1>Q1?Q1@Pj]8]9]>XE9Q1AQ1BQ1CQ1EW8W9W>P}P3PUP=P7N90@W0P3O1Q0YP1Q0VQ0UQ1DP3Q0WPWQ0TQ0SQ1FPj]8]9]>XE9Q1GQ1HQ1IQ1OW8W9W>POP3PXP2PAGmW0P3O1Q0[P1Q0aQ0`Q1MP3Q1LPnQ0bQ0_Q1KPj]8]9]>XE9RjQ0^Q0dQ1PQ1VW8W9W>PoP3PLPDP=GmW0P3O1Q0?PJPjQ0cQ1JQ0eQ0]W8W9W>PoP3PLPDP=GmW0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000Q0\Q0lf_RD#0RjQ1154F%=j;DMRJ/5MRn15X3?QMJ80>XX74Q0mQ1S,53?QMJ:0>n3XV4f^Rn#0RJ00Oa12JaRJ%_J+0EQ0212jpRj%_jf`#0Rj=4FK%=j;DMRpPMA4FbERJ1XJb?QMpCaP312jbS1SfXRj00ON12jNRb%_bS0m+0EQ02fYS02/2dRd%_dfc#0Rd=4F0S11/XdS0l/MMRdPMPs15sxS0\?QMdCaS0YP3120VR0fdRV#0Rdf[Rx54FS0[/XdS0?/MMRb?>M\RpQ0J/1bRbP4PdPFP3PC%=3S0JH0FfeRC#0RJf\54FRa%=JRW'5R>/MMRu7QMX74P4PxPFPJP3PWH0F?QMuXY4%wV%Hd%wY%HwPhPiQ0QPkA9lRRP<Pqb3b4b5X14X641MHMRw/1w^14^64P3fg#0Rw#=RVA4FwnRnO2b2bKbJP_P3EuPvP7Eu3UWPP3O1%_0PFPdPxPvP_PgP@PKPE12dv#_12x_#_;U3N:0JQ0?P\Q0fQ0[CvP111>~A>~Qaff#0R>f]R\54FRx/X>R>/MMR_PMA4Fy:Rd1XdyRy?QM_CaP311>d15nVRd/MMR>A4F{UR_7>MRv1X_{?QM>R>P4Pwfh#0R_=4FDRD/X_RE/MMRKA4F3}R07>MX74P{11E0X74P3PwP@DLA4FwURE,1dPG%A3123[P3PTP3P^CP3IX74P]P_P=DLR]%A_12_[P_PTP_P^CP3IR^PzfPPFP3POCSX74PNfi#0RzPBDLRBfOR_PFPzPXCSRX%0_1nL3,WLX74P:fj#0RLP2DLR_1nOL,WOROfkRL#wRz%0L#HRL%wgRT%0g#HRgPhPiPtPkPlA9lm6RmP;Q0M=9l6CVP<Pqb3b4b5X14X64X:4Rh11H8RHQ0</17[^14^64^:4R[P3fn#0RG=4FYRY%=GRdA4FGCRGP@O4b2bKbJb9b8bHbAP{P@Eu3qWAP3O111yxP4PwQ0J,50R0?QMKX74P{110DX74P3PwP@DLA>EVnP]P^PBPXP_POPzPLPTPgQ0KPiPtPkPlPmP;PlA9l`rP;1C6r>024`99lRCVCVP<Pqb3b4b5X14X64X:4Q0RAD87MRrAD?7M'1[\H^14^64^:4P3PGPdPYP@fUO5b2bKbJb9b8bHbAP{P@Eu9Uv>WAP3O1n200100000021100011000bXWPP3O1n200110300021110411105bZWOP3O1Q1S#_PFfa#0R>PjPePNQ0XP7fTR7P212>e#_Q0m;q3N:0JA4F>jRj/X>Q1TQ1T%=e;>j40>P1fb#0R1Q0254FRj%=1Q0n3>Q0k/1jQ0YP3Q0l/1sPhP[P3P~PWPaP5O4b29qpbWAP3O1Q0\Q11'1Q0KPiP4P41z4?P8PSC{P5Q0PC{PkPlPmP;PlQ03,|4Rm99l`P;1C6m>024`99lRCVCVP<Pqb3b4b5X14X64X:4XU411M?AD?AM,1r[\H^14^64^:4^U4P3PWPaPQP~P5Q1NO6b29UpbWAP3O1n200100000021100011000bXWOP3O1n200110300021110411105bZP}P8DL%kU&0TUDLbH%0\R\=4F7%=\;DMR\PMPUAZU:MRU/1\CaeWBW8P5P3O2n2001000000121000000W0W9P5P3O2n2001000000121000000W0XY4P5P3O2n2001000000121101000W0WcP5P3O2n2001000000121000000bIW>XE9XV4O5baP|P=DL%ko&0ToDLWeWdP5P3O2n2001000000121000000b0b`AEPUMeWBW=P5P3O2n2001000000121000000W0W?P5P3O2n2001000000121000000W0XD4P5P3O2n2001000000121101000W0WbP5P3O2n2001000000121000000bI%rf?ZZM=EPMeW;XC9XL4P5P3O2n2001102000121100105X@cO4b0WTW_P5P3O2n2001000000121000000W0X^IP5P3O2n2001000000121000000W0WSP5P3O2n2011000000121000000W0WRP5P3O2n2011000000121000000W0WBP5P3O2n2011000000121000000WgW]P5P3O2n2001000000121000000W0WfP5P3O2n2001000000121000000W0WTP5P3O2n2001000000121000000W0WSP5P3O2n2001000000121000000W0WRP5P3O2n2001000000121000000W0WBP5P3O2n2001000000121000000b0CcCcCcCcCcCcCcQ0:eWBW\P5P3O2n2001000000121000000b0o"). Qed.

End CompFs.

(* [comment removed for export] *)
Theorem art_avoid_client : forall Σ m sp, ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp -> art_avoid (W_client Σ sp) Σ.
Proof.
  intros Σ m sp HA Hsp.
  destruct (art_avoid_gen Σ m (W_client Σ sp) HA (ac_img Σ m sp HA Hsp) (ac_grant Σ m sp HA Hsp)
              (fun lo hi a n H1 H2 H3 H4 H5 H6 H7 _ => ac_shad Σ m sp HA Hsp lo hi a n H1 H2 H3 H4 H5 H6 H7)
              (ac_prb Σ m sp HA Hsp) (ac_secmap Σ m sp HA Hsp)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof (av_fs Σ m (W_client Σ sp) HA (ac_img Σ m sp HA Hsp) (ac_grant Σ m sp HA Hsp) (ac_shad Σ m sp HA Hsp) (ac_fsb Σ m sp HA Hsp)) as A10.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [exact A7|]. split; [exact A10|]. split; [exact A8 | exact A9].
Qed.


(* [comment removed for export] *)
Theorem ART_client_frame : forall Σ (m m' : mem) (sp : Z), ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp ->
  (forall a : word, ~ aclient (live Σ) (frames Σ) sp (bv_unsigned a) -> m' a = m a) -> wmono asegs m m' -> ART_A Σ m'.
Proof.
  intros Σ m m' sp HA Hsp H WM. apply (ART_transport (W_client Σ sp) Σ m m' HA (munch_client Σ sp m m' H) WM).
  exact (art_avoid_client Σ m sp HA Hsp).
Qed.
