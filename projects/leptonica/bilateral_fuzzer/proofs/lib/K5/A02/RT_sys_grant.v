(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require AsanPlanCore.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS02 Require AsanTablesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require AsanPlanSound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS02 Require AsanPlanImages.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require AsanNodesMmLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Unforced.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout RT_iface RT_frmkit D_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_state RT_rep RT_init RT_sys_stmt RT_sys_fixed RT_sys_munmap.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import AR.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_sys_grant () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List3revC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib7Sorting;Permutation;Permutation00K46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes6option02C46Stdlib7Sorting;Permutation?Permutation_indK46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List6filterC69OSSVerify5KrLib2K53A028RT_state4vposC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53A028RT_state7sum_clsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib2K53A028RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_SSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6reg_wfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53A028RT_state2caC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4r_flC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4r_stC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A028RT_state7ca_initC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53A028RT_state8sec_nresC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53A028RT_state3s_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4s_mbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4smszC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2K53A028RT_state5apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5pg_dnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5pg_upC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5r_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc69OSSVerify5KrLib2K53A02<RT_sys_grant>sum_cls_nonnegC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2K52AG;R_sizeclass6rz_logC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib7Sorting;Permutation?Permutation_revC46Stdlib7Sorting;Permutation?Permutation_symc69OSSVerify5KrLib2K53A02<RT_sys_grant?live_bytes_permC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6mod_leC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib5Lists4List7map_revC69OSSVerify5KrLib2K53A02<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7dep_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state8rt_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state9budget_wfC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53A028RT_state8rt_eagerC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List9nth_errorI35stdpp4base5NoDup00C69OSSVerify5KrLib2K53A028RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state>startup_grantsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state8grant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state2awC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List:fold_rightI69OSSVerify5KrLib2K53A028RT_state5secst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6secmapC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state4ckst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5kUMapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6kFaCapC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I69OSSVerify5KrLib2K53A028RT_state4rtsA00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state5regst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4reg0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A028RT_state4ckst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7SEC_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state8kUserCapC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53A028RT_state6creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6secsumC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A028RT_state7CREDIT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4l_f0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_tidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_al0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7l_maps0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state8maps0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state>pairwise_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_DTVC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state7layoutA00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib2K53A028RT_state:shadow_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep6ARTM_AC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC69OSSVerify5KrLib2K53A028RT_state7rt_mapsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC69OSSVerify5KrLib2K52AS8AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep8artm_sysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep>lazy_in_maps_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep9confined0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep;shadow_lazyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant<rt_wf_budgetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant:rt_wf_nsecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant<maps0_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant=secmaps_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS9sum_sizesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant?live_bytes_app'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grantFlive_bytes_filter_vposC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027RT_initDlive_bytes_sum_sizesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC79OSSVerify5KrLib2K52AS=AsanPlanSound3APS:res_len_okC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC79OSSVerify5KrLib2K52AS8AsanPlan2AP5n_resC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib5Arith8PeanoNat3Nat6add_wdC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsBsubrelation_properC69OSSVerify5KrLib2K53Lib;NodesA_madv<noaccess_posC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_revK46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03C69OSSVerify5KrLib2K54Spec8Unforced:gap_weightC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec8Unforced@gap_weight_sizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec8Unforced:gap_existsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec8Unforced6gap_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common2ARDvm_gap_available_iffC1?~~~~~~~~~~~~~~~zzzzzzK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib6Common2AR@vm_gap_availableC1?~~~~~~~~~~~~~~~zzzzzzI46Stdlib5Lists4List>ForallOrdPairs00C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC69OSSVerify5KrLib2K53A026RT_rep;maps_zboundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC69OSSVerify5KrLib2K53A028RT_state7VMLIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6E0_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep8iv_apartC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify5KrLib2K54AS02>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanPlanImages>asan_res_sizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1ZAProper_instance_0C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC69OSSVerify5KrLib2K54AS02>AsanPlanImages<asan_res_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool>andb_false_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC47Corelib4Init5Logic5proj1c69OSSVerify5KrLib2K53A02<RT_sys_grantAregion_free_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;RT_sys_stmt9sgrant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_sys_fixed<maps0_shadowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant8maps0_e3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_sys_fixedBl_maps0_in_rt_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_sys_fixed<artm_in_mapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant@grant_apart_mapsC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K52AS>AsanNodesMmLib:hull_coverC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP6img_loC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP6img_hiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib2K53A026Layout?K_LOW_SHADOW_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout@K_HIGH_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS02>AsanPlanImages?asan_hull_coverC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K53Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC69OSSVerify5KrLib2K53A02<RT_sys_fixedAA_bytes_rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state:allow_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm;mdl_mmap_rwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm:grant_ok34C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm<lazy_in_mapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant:ledger_gapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02<RT_sys_grant?grant_placementC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01K46Stdlib7Sorting;Permutation;Permutation02C46Stdlib7Sorting;PermutationAPermutation_transC69OSSVerify5KrLib2K53A026RT_rep?filter_cons_posC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mmBmdl_mmap_rw_vmmapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib2K52AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mmEeager_used_mmap_rw_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mmDmodel_ivs_wf_mmap_rwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mmDlazy_in_maps_mmap_rwC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List>ForallOrdPairs02C69OSSVerify5KrLib2K52AS>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm@mdl_mmap_rw_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep5shregC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC56Stdlib6ZArith6BinInt1Z4succC69OSSVerify5KrLib2K53Lib;NodesA_madvDnoaccess_pos_mmap_rwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm?mdl_mmap_rw_fdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9NodesA_mm>mdl_mmap_rw_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_frmkitBast_mmap_anon_rw_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:cps_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ARTMC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2K53Lib5RzCPS5nretAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC69OSSVerify5KrLib2K53A026RT_rep3RTAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A026D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;RT_sys_stmt:grant_nodeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] l1 IH]; intros l2; cbn [app live_bytes]; [lia| rewrite IH; lia]. Qed.

Lemma live_bytes_perm : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof.
  intros l l' H. induction H as [|[a s] l l' _ IH|[a s] [b t] l|l l' l'' _ IH1 _ IH2]; cbn [live_bytes]; lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_filter_vpos : forall l, live_bytes (List.filter vpos l) = live_bytes l.
Proof.
  induction l as [|[a s] l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos (a, s)) eqn:E; cbn [live_bytes]; rewrite IH; [lia|].
  unfold vpos in E. cbn [snd] in E. apply Z.ltb_ge in E. pose proof (bv_unsigned_in_range _ s) as R. unfold bv_modulus in R. lia.
Qed.

Lemma sum_cls_nonneg : forall f k, (forall c, 1 <= c <= Z.of_nat k -> 0 <= f c) -> 0 <= sum_cls f k.
Proof.
  intros f k. induction k as [|k IH]; intros H; cbn [sum_cls]; [lia|].
  pose proof (H (Z.of_nat (Datatypes.S k)) ltac:(lia)). specialize (IH ltac:(intros c Hc; apply H; lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma secmaps_bytes : forall Σ, rt_wf Σ -> live_bytes (map secmap (rev (sec Σ))) <= rt_eager Σ.
Proof.
  intros Σ HW. pose proof HW as (_ & (R1 & _) & _ & (S1 & S2 & _ & S4 & _) & _).
  assert (Hcls : 0 <= sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31).
  { apply sum_cls_nonneg. intros c Hc. destruct (R1 c ltac:(lia)) as ((M1 & _) & _ & _ & _ & (F1 & _) & _). lia. }
  assert (Hnres : 0 <= sec_nres Σ) by (destruct S2 as [E|E]; rewrite E; lia).
  unfold rt_eager.
  assert (H : live_bytes (map secmap (rev (sec Σ))) <= fold_right (fun s acc => smsz (s_n s) + acc) 0 (sec Σ)).
  { assert (HF : Forall (fun s => 0 <= smsz (s_n s)) (sec Σ)).
    { apply Forall_forall. intros s Hs. unfold smsz, pg_up, needed, rounded, rz_size.
      assert (X1 : 0 <= (Z.max (Z.max (s_n s) 1) 8 + 7) / 8) by (apply Z.div_pos; lia).
      assert (X2 : 0 <= 2 ^ rz_log (s_n s)) by (apply Z.pow_nonneg; lia).
      assert (X3 : 0 <= (8 * ((Z.max (Z.max (s_n s) 1) 8 + 7) / 8) + 16 * 2 ^ rz_log (s_n s) + 4095) / 4096) by (apply Z.div_pos; lia).
      lia. }
    clear -HF. rewrite map_rev.
    assert (E : forall l, live_bytes (rev l) = live_bytes l)
      by (intros l; apply live_bytes_perm; apply Permutation_sym, Permutation_rev).
    rewrite E. induction (sec Σ) as [|s ss IH]; cbn [map live_bytes fold_right secmap fst snd]; [lia|].
    inversion HF as [|? ? Hs Hss]; subst. specialize (IH Hss).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. pose proof (Z.mod_le (smsz (s_n s)) (bv_modulus 64) Hs ltac:(unfold bv_modulus; lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rt_wf_budget : forall Σ, rt_wf Σ -> A_bytes (aw Σ) <= CREDIT0 /\ rt_eager Σ <= 2 ^ 38.
Proof. intros Σ HW. pose proof HW as (_ & _ & _ & _ & _ & _ & (B1 & _ & B3 & B4 & _) & _). lia. Qed.

Lemma rt_wf_nsec : forall Σ, rt_wf Σ -> Z.of_nat (length (sec Σ)) <= SEC_MAX.
Proof. intros Σ HW. pose proof HW as (_ & _ & _ & (S1 & _) & _). exact S1. Qed.

Lemma maps0_bounds : forall L, layout_ok L -> Z.of_nat (length (l_maps0 L)) <= 64 /\ live_bytes (l_maps0 L) <= 2 ^ 45.
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H1 & H2) & _). lia.
Qed.

Lemma ledger_gap : forall Σ mo len, rt_wf Σ -> ARTM_A Σ mo -> 0 < len -> len mod 4096 = 0 -> len <= 2 ^ 32 ->
  vm_gap_available (m_vmmaps mo) len = true.
Proof.
  intros Σ mo len HW HA Hlen Hal Hsz. pose proof HA as (Hperm & Eres & _ & _ & (_ & _ & _ & Hisp & _ & _ & Hzb)).
  unfold maps_zbound in Hzb.
  pose proof HW as (HL & _). pose proof (rt_wf_budget _ HW) as (_ & Heg). pose proof (rt_wf_nsec _ HW) as Hns.
  pose proof (maps0_bounds _ HL) as (Hn0 & Hb0). pose proof (secmaps_bytes _ HW) as Hsb.
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  set (h := m_vmmaps mo) in *. set (L := vm_reserved h ++ vm_maps h).
  assert (HLb : live_bytes L <= 0x652000 + 2 ^ 38 + 2 ^ 45).
  { unfold L. rewrite live_bytes_app', Eres, RT_init.live_bytes_sum_sizes, AsanPlanImages.asan_res_sizes.
    rewrite <- (live_bytes_filter_vpos (vm_maps h)).
    rewrite (live_bytes_perm _ _ Hperm). unfold rt_maps. rewrite live_bytes_app'. lia. }
  assert (HLn : Z.of_nat (length L) <= 4 + SEC_MAX + 64 + 1).
  { unfold L. rewrite length_app, Eres, AsanPlanImages.asan_res_len. cbn [AsanPlanCore.APC.n_res AsanTablesA.ASAN_A].
    rewrite (Permutation_length Hperm) in Hzb. unfold rt_maps in Hzb.
    rewrite length_app, length_map, length_rev in Hzb. lia. }
  assert (Htop : alloc_top h = l_sp0 (lay Σ) - 2 ^ 23) by (unfold alloc_top, stack_max_size; rewrite Hisp; lia).
  unfold sp_window_lo, sp_window_hi, SEC_MAX in *.
  destruct (Unforced.gap_exists L len 4096 (alloc_top h) ltac:(lia) ltac:(lia) ltac:(rewrite Htop; lia)
              ltac:(reflexivity) ltac:(rewrite Unforced.gap_weight_sizes; nia))
    as (g & Hgal & HgF & Hgtop & Hgfree).
  apply (proj2 (vm_gap_available_iff h len)). exists (Z_to_bv 64 g).
  rewrite unsigned_lit by (rewrite Htop in Hgtop; lia).
  split; [exact Hgal|]. split; [lia|]. split; [exact Hgtop|]. exact Hgfree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_apart : forall l (lo n : word) e, region_free l lo n = true -> In e l ->
  apart (bv_unsigned lo) (bv_unsigned n) (bv_unsigned (fst e)) (bv_unsigned (snd e)).
Proof.
  intros l lo n [b s] H Hin. pose proof (region_free_In _ _ _ _ _ H Hin) as X. unfold iv_overlap in X. cbn [fst snd].
  unfold apart. apply andb_false_iff in X as [X|X]; apply Z.ltb_ge in X; lia.
Qed.

Lemma maps0_e3 : forall L, layout_ok L -> In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (HM & _ & _) & _).
  exact (proj1 (Forall_forall _ _) HM (0x8fff7000, 0x20000000000) ltac:(apply in_or_app; right; right; left; reflexivity)).
Qed.

Section Placement.
Variables (Σ : rtsA) (mo : Model) (len : Z) (a : word).
Hypothesis HW : rt_wf Σ.
Hypothesis HA : ARTM_A Σ mo.
Hypothesis Hlen : 0 < len < 2 ^ 64.
Hypothesis Hg : (bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + len <= alloc_top (m_vmmaps mo))
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 len) = true.

Lemma grant_apart_maps : forall e, In e (vm_maps (m_vmmaps mo)) -> apart (bv_unsigned a) len (bv_unsigned (fst e)) (bv_unsigned (snd e)).
Proof using Hlen Hg.
  intros e He. destruct Hg as (_ & _ & _ & Hf). pose proof (region_free_apart _ _ _ e Hf ltac:(apply in_or_app; right; exact He)) as X.
  rewrite unsigned_lit in X by lia. exact X.
Qed.

Lemma grant_placement : sgrant_ok Σ (bv_unsigned a) len.
Proof using HW HA Hlen Hg.
  pose proof HW as (HL & _). pose proof HA as (Hperm & Eres & _ & _ & (_ & _ & _ & Hisp & _)).
  destruct Hg as (G1 & G2 & G3 & G4).
  pose proof (maps0_shadow _ HL) as (HE2 & HE4). pose proof (maps0_e3 _ HL) as HE3.
  assert (Hin : forall e, In e (l_maps0 (lay Σ)) -> In e (vm_maps (m_vmmaps mo)))
    by (intros e He; exact (artm_in_maps Σ mo e HA (l_maps0_in_rt_maps Σ e He))).
  pose proof (grant_apart_maps _ (Hin _ HE2)) as D2. pose proof (grant_apart_maps _ (Hin _ HE3)) as D3.
  pose proof (grant_apart_maps _ (Hin _ HE4)) as D4.
  cbn [fst snd] in D2, D3, D4. rewrite !unsigned_lit in D2, D3, D4 by lia. unfold apart in D2, D3, D4.
  split.
  - unfold grant_ok. split; [exact G2|]. split; [unfold page_size in G1; exact G1|].
    split; [unfold l_ACEIL, STACK_WIN; unfold alloc_top, stack_max_size in G3; rewrite Hisp in G3; lia|].
    split; [unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi; lia|].
    destruct (Z_le_gt_dec (bv_unsigned a + len) 0x10000) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec SEGTOP_A (bv_unsigned a)) as [Y|Y]; [right; exact Y|]. exfalso.
    pose proof AsanPlanImages.asan_hull_cover as (_ & HC).
    cbn [AsanPlanCore.APC.img_lo AsanPlanCore.APC.img_hi AsanTablesA.ASAN_A] in HC. unfold SEGTOP_A in Y.
    destruct (HC (Z.max (bv_unsigned a) 0x10000) ltac:(lia)) as (iv & Hiv & Z1 & Z2).
    pose proof (region_free_apart _ _ _ iv G4 ltac:(apply in_or_app; left; rewrite Eres; exact Hiv)) as D.
    rewrite unsigned_lit in D by lia. unfold apart in D. lia.
  - apply Forall_forall. intros e He. exact (grant_apart_maps e (artm_in_maps Σ mo e HA He)).
Qed.
End Placement.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem grant_node_ok : grant_node.
Proof.
  intros Σ Σ' PMc Pm K len HPMc _ HW Hlen Hlal Hsz Heg HΣ' Hm.
  pose proof HW as (HL & _). pose proof (rt_wf_budget _ HW) as (Haw & Heg38).
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold sp_window_lo, sp_window_hi in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  assert (EA : forall P, rtA_allow (Σ' P) = rtA_allow Σ).
  { intros P. destruct (HΣ' P) as (EL & Eaw & _). unfold rtA_allow. rewrite Eaw, EL. reflexivity. }
  unfold ASTA. cbn [rt_allow ARTM RTA].
  eapply (cps_conseq asegs).
  - apply (ast_mmap_anon_rw_f asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
             (fun a => sgrant_ok Σ (bv_unsigned a) len) (fun a => K (bv_unsigned a))
             (fun a mo => ARTM_A (Σ' (bv_unsigned a)) mo /\ PMc mo) len).
    + lia.
    + intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4 & S5 & S6). repeat (split; [assumption|]).
      intros a Ha. rewrite Hrd. pose proof (S6 (bv_unsigned a) Ha) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
    + intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
      rewrite Hrd.
      split; [exact Hwf|]. split; [exact Hlz|]. split; [exact (ledger_gap Σ mo len HW HA Hlen Hlal Hsz)|].
      split; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
      intros a Ha. destruct Ha as (G1 & G2 & G3 & G4 & G5).
      assert (Hg : (bv_unsigned a mod page_size = 0) /\ (0 < bv_unsigned a) /\ (bv_unsigned a + len <= alloc_top (m_vmmaps mo))
                   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 len) = true)
        by (repeat split; assumption).
      split; [exact (grant_placement Σ mo len a HW HA ltac:(lia) Hg)|].
      destruct (HΣ' (bv_unsigned a)) as (EL & Eaw & Hperm' & Heg1 & Heg2).
      assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
      assert (Han : bv_unsigned a + bv_unsigned (Z_to_bv 64 len) <= 2 ^ 64).
      { rewrite Eul. unfold alloc_top, stack_max_size in G3. rewrite Hisp in G3. lia. }
      split.
      * 
        split.
        { rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. rewrite filter_cons_pos by (cbn [snd]; rewrite Eul; lia).
          apply (Permutation_trans (l' := (a, Z_to_bv 64 len) :: rt_maps Σ)).
          - constructor. exact Hperm.
          - apply Permutation_sym. rewrite Z_to_bv_bv_unsigned in Hperm'. exact Hperm'. }
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_reserved]; exact Eres|].
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_limit]; exact Elim|].
        split.
        { pose proof (eager_used_mmap_rw_le mo a (Z_to_bv 64 len) (proj1 Hwf) Han) as Hle. rewrite Eul in Hle. lia. }
        split; [exact (model_ivs_wf_mmap_rw mo a _ Hwf Han)|].
        split; [exact (lazy_in_maps_mmap_rw mo a _ Hlz)|].
        split.
        { rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. constructor; [|exact Hsep].
          apply Forall_forall. intros e He. pose proof (grant_apart_maps mo len a ltac:(lia) Hg e He) as D.
          unfold apart in D. unfold iv_apart. cbn [fst snd]. rewrite Eul. lia. }
        split; [rewrite mdl_mmap_rw_vmmaps; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
        split.
        { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_mmap_rw_vmmaps, mdl_mmap_rw_lazy in Hz. cbn [vm_noaccess] in Hz. exact Hz. }
        split.
        { intros x Hx. rewrite mdl_mmap_rw_lazy, mdl_mmap_rw_vmmaps. cbn [vm_noaccess]. exact (Hsl x Hx). }
        split; [|apply NodesA_madv.noaccess_pos_mmap_rw; exact Hnp].    
        unfold maps_zbound in Hzb |- *. rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps].
        rewrite filter_cons_pos by (cbn [snd]; rewrite Eul; lia). cbn [length]. rewrite !Nat2Z.inj_succ. clear - Hzb. lia.
      * apply (HPMc mo); [apply mdl_mmap_rw_fds| apply mdl_mmap_rw_fs| exact HPc].
    + intros mo (HA & _). pose proof HA as (_ & _ & _ & _ & (_ & _ & _ & Hisp & _)). unfold alloc_top, stack_max_size. rewrite Hisp. lia.
  - intros c Hc. exact Hc.
  - intros c (a & Ha & Hc). exists (bv_unsigned a). split; [exact Ha|]. rewrite (EA (bv_unsigned a)). exact Hc.
Qed.
