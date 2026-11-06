(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Exec RzCPS MState ITree Nodes.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_mmapfixed R_ensurefa R_ensurefa_B R_return R_return_T R_return_A R_return_B R_prim_lists R_prim_poison RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo RT_drain_cdk RT_drain_cfast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_drain_cslow () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A028RT_state5batchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K52AG;R_sizeclass>MaxCount_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K52AG;R_sizeclass8MaxCountC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A028RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4r_flC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53A028RT_state5r_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs8round_faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6reg_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7r_muserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4r_stC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass6neededC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7ClassIDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K53A028RT_state2caC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegI46Stdlib5Lists4List5NoDup00C35stdpp4base?NoDup_ListNoDupC46Stdlib5Lists4List;Forall_implC69OSSVerify5KrLib2K53A02=RT_drain_pure?nodup_len_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib2K53A02;R_prim_defs;round_fa_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z;div_le_monoC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC56Stdlib6ZArith6BinInt1Z8le_transC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC46Stdlib6ZArith4Zdiv:Zminus_modK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K53A028RT_state8kUserCapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5kUMapC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A028RT_state4ckst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6kFaCapC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A028RT_state4ckst01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z;le_preorderI47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A028RT_state8rt_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_drain_defs4recpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2K53A02=RT_drain_defs:cdeal_fullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_drain_defs4uregC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_drain_defs6dh_mfaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53Lib3Arr3updC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A028RT_state5regst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk<cd_full_trueC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib2K53A02=RT_drain_pure8recp_mfaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_led=rt_eager_recpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk6cd_geoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs4tsepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk6cd_msDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk7cd_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_drain_defs6set_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep:consts_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep8prim_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep9cache_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep9chunk_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep7sec_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep8quar_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep7dep_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep6fs_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep6ia_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep:shadow_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep7vis_repC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53A02<RT_drain_geo9dg_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs:inst_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs9mm_gcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_thread<thread_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_poison8ps_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_prim_kit7rwc_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk5cd_pcC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2K53A02<R_cache_defs7pc_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs8pc_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep3cpwC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53A02<R_cache_defs;cstat_allocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC69OSSVerify5KrLib2K53A02<RT_drain_cdk=dk_stk_withinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_freeA2<fl_c8_of_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_freeA29fl_two_c8C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk6cd_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep7reg_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs7ri_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs7ri_coreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs7ri_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_glue_defs5farunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs6fl_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>RT_drain_cfast<ri_tail_normC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_kit5dk_rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_prim_defs2faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_kit8dk_auserC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027RT_fkit;fk_shad_le2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027RT_fkit<fk_shad_monoC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z7div_posC69OSSVerify5KrLib2K53A02:RT_maltail6stk_CBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdeallocEcdealloc_drain_A_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs6cacheTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdeallocEcdealloc_drain_A_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs6cstatsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_return_A:rta_A_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_return_A:rta_A_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_mmapfixed9rmap_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_ensurefa;efs_A_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02>RT_drain_cslow6cs_svcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<RT_drain_cdk4W_CDC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib9micromega;ZifyClasses7rew_iffK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02>RT_drain_cfast:bv64_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr@u32arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_thread9tsd_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53A02=R_prim_poison:PCP_framedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses6eq_iffK46Stdlib9micromega7EnvRing3Pol03C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53A02>RT_drain_cslow6zal_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs:i_spacebegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs;i_premappedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A02>RT_drain_cslow7cs_numsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53A028R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdealloc>cdealloc_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdealloc>drainhalf_retBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdealloc9rta_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_cdealloc=cdealloc_retDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_ensurefa8efs_retBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_ensurefa=str_freearrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;R_mmapfixed=mmap_ecall_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:R_return_A8rta_retEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_thread@g_tsd_key_initedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_thread9g_tsd_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_thread7pth_tsdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028R_threadBg_pthread_tsd_mainC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_drain_cslow ()) [] "h04__x1h11rh21Hh32Hkh47__arithh54__ffh66__sat0h78__varmaph85__with91kh:1qh;1xp;2p;3p;1p;4p;6p;8p;7p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8g000nj28Tg001Jj22Tg001jj30Tg002Dj23Tg002aj27Tg003>j25Tg003[j2CTg004Lj21Tg004hj1=Tg005Hj1<Tg005hj2;Tg006Fj1:Tg006dj19Tg007Oj2LTg0082j2KTg008Uj44Tg009@j1JTg009bj6ITg00:Fj8BTg00:jj2@Tg00;Lj2ATg00;fj2?Tg00<Rj3>Tg00=1j4DTg00=cj3ETg00>Dj6FTg00>`j4GTg00?:j7HTf1R1g00?^R0g00@=R2P2g00@]R3f0R4g00A=FHp=6g00A]R5g00B;R6f2R7'8f3R8,27=051P5f4R9f5R:/34/78505X:51589P51289159:,3:/749059X151C891168116:f6R;,2:,16[[g00BYR:#=%<:1;51%:5%95R:P0P2P2P3P51L56R<g00CEg00Cl,K5R=C4,6:%J2P:P0P2P2P3P5P=g00DQP<C4,6:EIGB1@:3P4P7g00E8R:g00EXR3'A1?47=0:3dA>561CDb5b7b8X051864A0516g00F8[[^05P4P;P8O2b4b69E89P7P4EFCGW2W3X15X;5W9o"). Qed.
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

Section CSlow.
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
Hypothesis Hfull : Z.of_nat (length (ca Σ c)) = MaxCount c.
Hypothesis Hgrow : r_mfa (pr Σ c) < 4 * (Z.of_nat (length (r_fl (pr Σ c))) + MaxCount c / 2).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation mc := (MaxCount c).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation mfa := (r_mfa (pr Σ c)).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation new := (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + MaxCount c / 2))).
#[local] Notation sp1 := (Z_to_bv 64 (bv_unsigned sp - 112)).
#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

(* [comment removed for export] *)
Lemma cs_nums : 1 <= mc / 2 <= 8 /\ mc - mc / 2 + mc / 2 = mc /\ 2 <= mc <= 16 /\ 0 <= nf < 2 ^ 27 /\ 0 <= mfa <= 2 ^ 29
  /\ mfa mod 2 ^ 18 = 0 /\ 4 * (nf + mc / 2) <= new < 4 * (nf + mc / 2) + 0x40000 /\ new mod 2 ^ 18 = 0 /\ new <= 2 ^ 29
  /\ mfa < new /\ (new - mfa) mod 4096 = 0 /\ (new - mfa) mod 8 = 0 /\ (new - mfa) mod 4 = 0 /\ 4 * Z.of_nat (length (r_fl r)) <= mfa.
Proof using Hc HRW Hgrow.
ltac2:(KReplay.run1 (kr_t_RT_drain_cslow ()) ["CSlow"] "p'0h04__x1h17__arithh24__p1h37__sat12h47__sat13h57__sat14h67__sat15h77__sat16h87__sat17h94cstrh:5cstr0h;5cstr1h<4__ffh=8__varmaph>5__with?7__sat18h@7__sat19hA7__sat20hB7__sat21hC7__sat22hD1HhE4__x2hF7__sat23hG7__sat24hH7__sat25hI7__sat26hJ7__sat27hK4__p2hL4__x3hM4__p3hN4__x4hO4__x5hP2HahQ1zhR4__p4hS4__x6hT1ahU1xi001xhV6__sat3hW4__x7hX1bhY2HxhZ2_Hh[4__p5h\4__p6h]1lh^3CS1h_2D1h`2D2ha2D3hb2H2hc2HDhd2HNhe3Hflhf4Hmodhg4Hnewhh3Hsthi3MC1hj3MC2hk2RGhl2W1hm3W10hn3W11ho2W2hp2W3hq2W4hr2W5hs2W6ht3W6'hu2W7hv2W8hw2W9hx1Xhy3_H0hz7__sat28h{7__sat29h|6__sat4h}1ih~1qi012sti021np%0p%1p&0p;2p;1p;3p;4p;6p;5p;7p;8p100FUp4p70p100GOp4p710p8p100Glp4p7210g00HXR0p4p710p8g00I6k20cTg00J;j15Tg00J`j18Tg00K>k10;Tg004LS00j22Tg00L=R1j20Tg001Jj2?Tg003>j2gTg00LXj2XTg002aj2DTg00M5k202Tg00Mlk10bTg00Nej2rTg00OEj1pTg00Oej1@Tg00PJj2_Tg000nj2:Tg00Pgk10LTg00Qak10CTg00Rak20ATg00S\k10?Tg00TXk10>Tg00UXk10:Tg002Dj26Tg00VQj2iTg00Vfk106Tg00WHj1mTg00Whj3kTg00XFk201Tg001jj3STg0000j3{Tg00Xhk10aTg00Yfk10^Tg00Zck10YTg00[aj1qTg00\Fk20WTg003[j2ITg00]=j2cTg00]ej3bTg00^Ik20VTg004hk10UTg005Hj1|Tg006Fk10TTg006dk10STg007Oj2zTg0082j2yTg009@k10OTg00:jk20NTg00;Lj2xTg00;fk20MTg00<Rk30KTg00=1k40JTg00_:j2oTg00_Vk20FTg00`3k60ETg00`Sk50DTg00a\k20BTg00bbj5wTg00cPj1VTg00coj2vTg00dXj3`Tg00eAj2hTg00ejk10@Tg00fHk50=Tg00g4k50<Tg00g`j4FTg00h;k309Tg00h^j2uTg00iJk208Tg00jMk307Tg00jnj1jTg00kLj3sTg00kok505Tg00lTk30GTg00mIk404Tg00n7k50HTg00nYk10ITg00o2j2dTg00oRk303Tg00>`j4lTP0j6aTg0106k30PTg010Vk100Tg0114k20QTg011Uk30RTg005hj2~Tg008Uj4nTg00?:j7tTg00:Fj8eTg012>k30`Tg012gk20_Tg013Sk30]Tg0143j4]Tg014Qk30[Tg0154k60ZTg015Xj7}Tg016<k30\Tg009bk60XTg00A]R0f0R2g00B;R33Sp=9f1R4=S02p=B1232p=1%@2#@p=Jf2R51D42'6p=L%52#5p=^%52#5#5#5p=K1654/22p=P1?42=S03p=71254/02p=M1:32p=[1~02p=UP5g00?^R6g00@=R7P7g00@]R8P0P4g016_P2Cng00A=R9Ftp=3f3R:P6P7P7P8P5P4P2Gep=A1z02p=<1v02p=ZB0`042p==g017F-0_2p=Yg00BYR;@0]42p=WP0P5P4P2C]p=CP0f4R<P:P0P5P4P2C]C]p=fP0P0P<P:P5C]P4P2C]p=E1y02p=GB0[042p=;P4P6P7P7P8P2J0Zp=>f5R=P6P7P7P8P<P6P7P7P8P:P5F}P4P2Gep=4f6R>P6P7P7P8P=P<P:P6P7P7P8P5P4P2GeGep=RP5P6P7P7P8P0P4g00CEP2CnP9Ftp=NP5P6P7P7P8P4P2F}p=QB0\042p=OP5P6P7P7P8P0P4g00DQP2CnP9Ftp=HP4P6P7P7P8P2J0Xp=\P>P=P<P:P5P4P2CFCFp=Tp,1cR6p,2HcS01+0cg00ClS02#5R9#8R?&0;6R@'2S03%59RA#5RB#5RC#8S04,2@RD'0S051?@?RE#9S06'0P1Q05Q06Q02#8S071g@?RF'2S08%8BRG,2FS09'0S0:1X@F/DF/B@S0;Q05p,2ΣRH0026RI$0bRJ,r0RK#pRL#1RMQ02#@S0<#5S0=#JS0>#8S0?,_?S0@,:LS0A'0S0B&0LIRN#1S0CQ0<#@RO#5#@S0D#8RP,_?RQ,2NS0E'0S0F%@AS0G#5S0H#8RR,_?RS,?NS0I#9S0J%8ARA?LLFRT&0CTRU'2S0K%5CS0L#5S0M#^#KRC#5#^S0N#5S0O#^S0P#8RV,DT,:US0Q'0S0R1?USS0S#9S0T12UQS0U1:NUS0V1XUNRW%8CRC'?S0W#9S0X1?WGS0Y#9S0Z1?WAS0[#9S0\APALNS0]'0S0^'0S0_'0S0`'0S0a'0S0b'0S0c'0S0d'0S0e'0S0f'0S0g'0S0h'0S0i'0RXP2Q05Q06p,3HRW20A6IP1&0?IRY#1RZg0182,2YS0j'0S0kg018oR[,7YS0l&0>6R\g019iR]&0:IRI'rR^#pR_'6R`/2YS0m1D`\,:YS0nQ0Cg01:d,2N'0S0o17N[S0pQ0]1i0JS0q%12S0r1:2_'0S0s&06]R[%m29k]Ig01;_-01]Ra3S'0X}0Rb={0JS0tP]p-0RcP2g01<ZRdQ07/22S0u&0a2/D2&0^2$0Y,B67M\'0RePePdn01101000400101021010200Z01]={]IS0vQ0>#5#K#K#K#K#KS0w#5Re#5#K#8Rf,2`S0x'0S0y'0S0z'0S0{'0S0|'0S0}'0S0~'0S10'0S11'0S12PXP2Q0kQ12P1Q0lQ11PXP2Q0lQ11P1Q0mQ10PXP2Q0mQ10P1Q0nQ0~PXP2Q0nQ0~P1Q0oQ0}PXP2Q0oQ0}P1Q0pQ0|PXP2Q0pQ0|P1Q0]Q0{PXP2Q0]Q0{P1Q0qQ0zPXP2Q0qQ0zP1Q0tQ0yPXP2Q0tQ0yP1Q0vQ0xPXP2Q0vQ0xPJP_%qKRKPM20WH6,r0RH#qRg%pH#1RH%q^R^%1_Rh1INVRiQ0C%1VRj1?NVS13#1[[Rk%@9S14#@S15#J#8Rl,c?Rm%[?S16%1l1_?lRn#[[[Ro%1?RpAb?l4VdWPRl%1n\d^PpRn1I@?Rq%1@Rr%1E\p[RE20V@?Rs%1F\p\rRr1IYVRt1?YV#1\j\ZRZ&0U;Ru%|;R;%U4Rv&0T0Rw&0S0Rx1z03RyQ02,y0Rz53xS17&0O7R7Q17CA20Nx8R8P2P5g00E8R{g00EXR|'x20M25=S{|dB0K034H0JR|b<b=b>X00S18Q0r%14S19[^00S1:P2P_f7R{O2b1b3b4b5b6b7b8b;b:b9S1;%|0R}P11i021o04[S1<1o021i04R~[1o05\~20F02P4n2001000000120000000W]Q1<^]}P2PJf:S1<O2bDP0PbQ0sXU0PbP2O1P1Q191:4_'0%m49k]I=S[a%15S0s1:5_'0P2%1:S1=1::_'0%m<9k]I=S[aP4WZWxP4P2O2n2001000000120000000WDXU0PJP=J0EI0D12L_Q01-0B6Q0L#8R6/2\RJQ0O#8Ra,2\R['0RI17\6R]'0P1PIP]%8eS0O,2_ReP2P1PJP[Pe\]P2P6P\P_Q1;PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPtPZPuP;PvPwPx%<6Rb=3xzR}P7P}CAP8P|b<b=b>X0012621264[^00P2P\f<S1;O2b1b3b4b5b6b7b8b;b:b9DwAP6_`PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPtPZg01=6R`#VS0L#VS01#V#VR}#VS1>#ZS1?1v0`R`5`0Q0w#@#8,h0Q1?5`0%Z}S0w1h06=`0`'='='=#Y/WuP;%U:S1@%U<S1A7C=P=&0@0R}P4P}P=P}P5%U=S1BDfDEPwPx%@OS1C#GR~93xbP7Px1;~z%<f53xP7PxPx%GBS1D93xyS1E1>x{S1FP7PxPxQ0=#5#G93xyS0=f8S1G,>xS1HP7PxPx%<?Rb%GO53xS1If9S1J,>xS1KP7Q0O#<S1L93xzE4E4E4FRP8P|b<b=b>X00XE0XL0XN0XO0X2cXKcXMc126<AP=4f%1</0{%1>S1MQ1J'012?=S1Nf;S1O'0Q0O,2=[[[[[^00^E0^L0^N0^O0^2c^Kc^McP2PDQ0jQ0P#5#^#K#K#8S0P,2NS1PP\PYPNP@P_f=S1QfES1RfZfjfoO=b1b3b4b5b6b7b8b;b:b9bDXy]XZ[X^JP4P2O2n2001000000121000000XDIP4P2O2n2001000000121000000bDPeQ0:Q0;Q08Q09P@P?Q07PqPEPuP;P}PwANxybP8P|b<b=b>Q16P2b1bVRePqPEPuP;PvPwPxA3xbzS1S1>x:S1T5QxS1UP7Q07#<S1V,;b=3xzCAP8P|b<b=b>X00X2cAM?24S1WQ07=P?4[^00^2cP2PDP@f^RIO3b1bVI0=P@P?PGPePqPEPuP;PvPwPxQ1TQ04#<93xzS1X5QxS1YP7%<GS1Z,;b93xzCAP8P|b<b=b>X00X2cQ04,22,04S1[16?G,24[^00^2cP2Q03P@PIO3b1bVI0<CFPqPEPsPrPuP;%U5S1\?C4}S1]Pw%G9R9:090z/O9=HxzP8P|b<b=b>X00XE01X24/D4/B2^00^E0P2PFP@O2b1S1^bVb|CFQ0:Q0;'0PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPtPZ1h0A=`0`Q1?Q01#Z'='=#Y,u`/WuP;Q1@?C=}P5P}P4Q1AP=P}P=Q1B?C=}DEDEPwPxPxQ0G#GS0G93xyS01Q1FP7PxPxQ15#G93xyS15Q1HP7PxPxQ1D93xbS1_Q1KP7PxQ0G%<ARI1Oz9';S1`5NxP7Q1`93xyCAE4E4E4P8P|b<b=b>X00XE0XL0XN0XO0X2cXKcXMcQ1=/0=S1a%1=/0{S1bQ1J9M?<S1cALA:<S1d,:>ALA<=#1[[[[^00^E0^L0^N0^O0^2c^Kc^McP2PDQ0jQ1PPYPNP@PFPLfRS1efbfgp,5HgrowS1fO<b1b3b4b5b6b7b8b;b:b9-08TQ0RQ1C#J#J#J#J#J#J#J#8Re,DTRT/gVRJPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPtPZPuP;P}Pw%<VS1C=Hxy,\xP8P|b<b=b>%9Vg00F8S1g[P2b1b3b4b5b6b7b8b;b:b9807VQ0TeQ0T16JV1DQeR[/gVR]/6VPQPJP]PVPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPr1IUSR]%1U%1SS1hQ0S#1[[RJPtPZ1c?RR\Q16%1R%[S[[RfAb?R4VdXPpRRQ1h\d^PpR6PuP;P}PwQ1C93xyP8P|b<b=b>PjP2b1b3b4b5b6b7b8b?b@bAb;b:b9PTP[PVPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrP]PJPtPZP\PfPRP6PuP;P}PwQ1C9NxyP8P|b<b=b>%[VP2b1b3b4b5b6b7b8b?b@bAb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPr1c?PRTQ16%1P%[Q[[RjAb?P4VdXPpRP%1Q\d^PpROP]PJPtPZP\PfPRP6Q1>#VS1>#V#ZS1iQ1>#ZS1>Q1?'='=,=`#Y,u`/WuP;Q1@?C{}S1jP5P}P4%U{P<P}P{P}DES1kP{Q1BP{%U>S1lDfDEPwPxPxQ1`%@B#GS1m53xQ1KP7PxPxQ1<,>xS1nQ1Z93x95QxQ1O,>xS1OP7PxQ1L93x~S1LP7PxA3xz~S1oP7PxPxQ01Q1;,>xS01P7PxPxQ15Q1Q,>xP7PxPxQ1_f>S1Q,>xP7Q1`%<eR~'OQ0D#j9s0bS0D/O~53xE4E4E4FRE4E4P8P|b<b=b>X00XE0XL0XN0XO0XS0XW0X2cXKcXMcXRcX[cX\cALA24S1p?M>{Q1J125G'0Q1<'0Q0O,2{Q1G,2:%1{S1qQ1Q'0Q1J#1S1rf@S1s'0Q1GfBR~5M?Q1G9LA{S1t/De/2[[[[[[[[^00^E0^L0^N0^O0^S0^W0^2c^Kc^Mc^Rc^[c^\cP2PDQ0jQ1PQ0;Q08Q0QPUP_PYPNP@PFPLQ1sfAS1uP~fCS1vfYfifnODb1b3b4b5b6b7b8b?b@bAbBbCb;b:b9I05DwP0Q00Q00g01=U60G0PQH04I0HQ0UeQ0U172SS00%92S1w$0IR[P117541d5:S1x[Re1d4517:5RB[S1y1d:<\BB03542S1zP4n2001000000120000000UXX0XT0Pe\[^X0^T0P2P5PSPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6Q1s/ISQ1s#1Q1h1?~S#1[[PuP;P}PwQ0H#j9s0bS0H=Hxy,\xP8P|b<b=b>%9SQ1g[P2b1b3b4b5b6b7b8b?b@bAbBbCbFb;b:b9P4O41dS5g01>:P0162SR~,B<XQ017<C17<G17<A'0'0P21B>~P0164SRB172C172G172A'0'0XU017BC17BGS1{17BAS1|'0P1PeQ1yQ1x17<:[Q1zP2n2001000000120000000V[XX0XT0S1zQ1y\[^X0^T0S1yP2165SS1xPCPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;P}Pw%<CS1}=Hxy,\xP8P|b<b=b>%9CQ1g[P2b1b3b4b5b6b7b8b?b@bAbBbCb;b:b9P016:SR[162C'BXQ0Q0M#8Re,65PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;PvPwQ0H,;zRB%<e,;zQ1}';5HxP8P|b<b=b>X00162e/6C,B~^00P2Q1uO1S1ub1b3b4b5b6b7b8b?b@bAbBbCb;b:b9ClO4bDQ1{Q1|Q1zQ1yP2Q1xPGPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;P}PwQ1Z=Hxy,\xP8P|b<b=b>%9GQ1g[P2b1b3b4b5b6b7b8b?b@bAbBbCb;b:b9P0162G,B[XQ0Q0N#8Re,65PKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;PvPw%<e,;zQ1Z';9HxBP8P|b<b=b>X00162e/6G,B~^00Q1ub1b3b4b5b6b7b8b?b@bAbBbCb;b:b9ClO4bDQ1zQ1yP2Q1xPAPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;P}PwAHxIy,\xP8P|b<b=b>%9AQ1g[P2b1b3b4b5b6b7b8b?b@bAbBbCb;b:b9P0162A,B[XQ0165aPKPMPgPHP^PhPiPkPmPoPlPnPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PuP;PvPw%<a,;z/;I9HxBP8P|b<b=b>X00162a/6A,B~^00Q1ub1b3b4b5b6b7b8b?b@bAbBbCb;b:b9ClO4bDFTP{P2EaWDX~0P4P2O2n2001000000121100000bYbDWYXU0Q00174C174G174A'0'0[^U0P0Q0SQ0I'X/?SQ1wXQ0P0P3Q0I,X2/7SXQ0P0P31X32/7SXQ01x03Q13fHEaQ0SP5Ea1?WSS13B0PUNSEaQ13#9P4PWP2O2Q0XQ0ZQ0\'0S00'0P1Q0XQ00PXP2Q0XQ00P1Q0ZQ0\PXP2Q0ZQ0\Q1eQ0JQ0:Q0iQ08Q09PKPMPgPHP^PhPiPkPmPoPlPn1IWGR1%1WS0i%1GQ0Y#1[[R31INSR~Q0CQ1hQ0I#1[[RaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP61IWARBQ0i%1AQ0[#1[[R[1IWCReQ0i%1CQ0W#1[[RC1IWSRWQ0iQ1hQ13#1[[RSPuP;PvPwPxPxQ1V=3xzS1VQ1T5Qx1>x<S0iP7Q1VE4P8P|b<b=b>X00X2cXKcQ0u/04/05Q07/24[^00^2c^KcP2Q0;Q09PFfSS09O4b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxPxQ1TQ1Z93xzS1Z5QxQ0iP7Q1ZE4P8P|b<b=b>X00X2cXKc122G,04/05124G[^00^2c^KcP2Q0;Q08PFQ09O4b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9CFQ0;Q0hPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSQ1^b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q05Q0gQ03PDPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxQ1UP7Q1SCAP8P|b<b=b>X00X2cQ1W12?4[^00^2cP2PDP@p+01ARGO3b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxQ1YP7Q1XCAP8P|b<b=b>X00X2cQ1[Q04,24[^00^2cP2Q03P@PGO3b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9CFQ0BQ0fPMQ0APKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSQ18Q1:P2PLQ1vO2b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZQ0?,c?Q16Q0?#1Q0@#[[[Q0?=b?4VdXPpQ0@#1\d^PpP\PfPRP6PBP[PePCPWPSQ1iQ1>/=`'=#Y/WuP;Q1jP{P}P4Q1kP{Q1BP5Q1lDfDEPwPxPxQ0G,Oz,;IRpQ1m53xQ1KP7PxQ1LP7PxQ1oP7Px1;IzRdQ1D53xP7PxQ1EQ1n5QxP7PxPxQ15Q1OP7PxPxQ1IQ01P7PxQ1D=NxpP7Q0>#j9s0b9NxzCAE4E4FRFRE4P8P|b<b=b>X00XE0XL0XN0XO0XS0XW0X2cXKcXMcXRcALA2:?M>{Q0O,2>125{APA:=Q1MQ1;'0Q1rQ1Q'0Q1s9M?{Q1JQ1<9LA{':Q1GQ0@':[[[[[[[[^00^E0^L0^N0^O0^S0^W0^2c^Kc^Mc^RcP2PDQ0jQ1PQ0QPUP_PYPFPNP@PLfTfVfWfefmf}p+01CQ1fOCb1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJbzb{b;b:b9CFQ0FQ0eQ0CQ0EPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxPxQ17Q1TP7Q17E4P8P|b<b=b>X00X2cQ0r/04Q19[^00^2cP2Q1PPNfkR_O3b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPTPjPPPOPsPrP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxPxQ1TQ0P#<93xzP7Q0D93xzR{E4P8P|b<b=b>X00X2cQ0P,22,04124QS0P[^00^2cP2Q0CPNP_O3b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9CFQ0JQ0dPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;Q1\?C5}P5P}P4P}DEPwPxPxQ1EP7PxQ0H93xyP7Q17FRP7PxAHxzyRyP7PxPxQ1EQ0iP7PyE4FRP8P|b<b=b>X00XE0X2cQ19Q1hQ0s[[%94Q1=/0<%9:[[[^00^E0^2cP2Q1PPNQ0IQ1;fDP_O6b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0RQ0cQ0KQ0QPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;Q1\Q1@7C4S0cPwPxPxQ1`Q0<#GR?53xRb1>x=RpP7PbE4P8P|b<b=b>X00XE0XL0X2cQ1p?M5:ALA45Rb/2:[^00^E0^L0^2cP2Q0QPUPFPLQ1eO5b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;Q0cPwPxPxPp1O9?,;IQ1C'O9NxzR?P7P?E4P8P|b<b=b>X00XE0XL0X2c1DbV,:2,0:ALA5:/DV,:4[^00^E0^L0^2cP2Q0KPFPLPUQ1eO5b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9CFQ0TQ0bPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSQ02$00-0Q0Q0w60R0/=`#Y/WuP;Q1@Q1A7C<P<P}P4Q1\9C}<DEPwPxPyP7PxQ1E1>x>5QxP7PxPxQ0=Q1FP7PxPxQ1IQ1HP7PyE4E4FRP8P|b<b=b>X00XE0XL0XN0X2cXKcXMcRyQ1wQ1aQ1bQ1c%9<[[[[^00^E0^L0^N0^2c^Kc^McRVP2PDQ0jQ1PPYPNP@Q0SfQP_f{R:PGO;b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0UQ0aPKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;PvPwPxP{P7P{CAP8P|b<b=b>X00122QQ0P[^00P2PUfPO2b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0VQ0`PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSQ1?Q0L#Z/=`'=#Y/WuP;Q1@Q1l7C>P5Q1B?C>}P4Q1AP>P}P>P}DEDEPwPxPxQ0GQ14#5#G'O,;IRI=3x9Q1HP7PxPxQ17Q1KP7PxPxQ0=Q1nP7PxPxQ1_Q1OP7PxANxzIP7ANxz9CAE4E4E4E4P8P|b<b=b>X00XE0XL0XN0XO0XS0X2cXKcXMcXRcQ1d?M4>Q19Q1G'0Q1qQ1<'0Q1NQ1;'0Q1t,:<1:=>[[[[[^00^E0^L0^N0^O0^S0^2c^Kc^Mc^RcP2PDQ0jQ1PQ0QPYPFPLP@PUPNQ1eP_P:PGQ1fO?b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0XQ0_PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZPePCP\PfPRP6PBP[PWPSPyPVP2PDQ0jQ1PPYPNP@Q0WfJP_P:PGO;b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0ZQ0^PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPyPVP2PDQ0jQ1PPYPNP@Q0YfFP_P:PGO;b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9Q0\Q0]PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZPBP[P\PfPRP6PePCPWPSPyPVP2PDQ0jQ1PPYPNP@Q0[Q1RP_P:PGO;b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9PKPMPgPHP^PhPiPkPmPoPlPnP1P3P~PaPqPEPsPrPTPjPPPOP]PJPtPZP\PfPRP6PBP[PePCPWPSPuP;Q1]PwPxA3xd9RdP7PdCAP8P|b<b=b>X00XE0APA24APA45[^00^E0P2PNPLfcO3b1b3b4b5b6b7b8b?b@bAbBbCbFbGbHbIbJb;b:b9CFFTFTFTFTFTFTbtWaW`P4P2O2n2001000010121000000WDW_P4P2O2n2001000010121000000bTbcbfbgbdbkbbbhbePXeWnWmP4P2O2n2001000010121000000WDWwP4P2O2n2001000010121000000WDWvP4P2O2n2001000010121000000WDWuP4P2O2n2001000010121000000WDWsP4P2O2n2001000010121000000WDWrP4P2O2n2001000010121000000WDWqP4P2O2n2001000010121000000WDWpP4P2O2n2011000010121000000WDWoP4P2O2n2011000010121000000WDWlP4P2O2n2011000010121000000bDWjWiP4P2O2n2001000010121000000bDo"). Qed.

Lemma cs_eager : rt_eager (recp Σ c i) = rt_eager Σ + (new - mfa).
Proof using Hc Hfull Hgrow.
ltac2:(KReplay.run1 (kr_t_RT_drain_cslow ()) ["CSlow"] "h01bh12Hah24__x1h34__x2h44__x3h51zh67__arithh74__ffh87__sat12h97__sat13h:7__sat14h;8__varmaph<5__with=4cstrh>5cstr0p;1p;3p;2p;4p;7p;6g01>Tj1ETg01?Qj3lTg00M5j2@Tg00Pgj19Tg00J;j1BTg00J`j1<Tg00Mlj1?Tg00Nej28Tg00OEj17Tg00K>j1JTg003>j2HTg002aj2=Tg002Dj2FTg00Qaj1DTg01@Oj2\Tg00\Fj2ZTg01@lj2YTg01B0j3XTg01Bnj2VTg00[aj1ATg00Oej13Tg00]=j2STg000nj26Tg00PJj2RTg00]ej3QTg00^Ij2MTg004hj1LTg005Hj1KTg005hj2>Tg0143j4ITg006Fj1NTg006dj1OTg0082j24Tg00h;j3PTg016<j3GTg008Uj4TTg00?:j7UTg00:jj2kTg00;Lj2jTg00;fj2iTg001jj3;Tg00<Rj3fTg00=1j4eTg01Cnj2CTg01DKj2^Tg01Dkj4]Tg00S\j1[Tg00UXj1_Tg01EFj4`Tg01F9j4aTg01G5j3bTg01H:j1cTg01H\j4dTg00HXj65Tg01I^j4WTg00LXj2gTg004Lj2hTf2R0f1R1f0R2'g'=p=0g00A]R3?;12p=1g00B;R4/h2p=2g00E8R5g00EXR6f3R7P0P1P2E5p=:P3p,2ΣR8#ER9p,1cR:p,1iR;5l8R</@:#9R=1@8:R>#9R?30g00ClR@#BRA#B#<RB%?>RC,83RD#7RE%J:RF%<ARG'HRH'='FRI#DRJ=09?RK,12X53P3P5P31\::RLP5P31Z8:RM,Y:RNg01;_RO9X>;,V:RPP?n0100000020000RQP?n0100000020000A092?/1KX53P5P3P2PQP?n0100000020000=09?/1KX05P5P3P2PPP?n0100000020000=09?/1KX05P5P3P2PJP?n0100000020000=09?/1KX05%AD%2E183MRE#A%7E#2%3A#3#3#3#<RE,SG164G%2E1RGERD,64[[%2GRQg01<ZRRAQGE1UW1%2D\R^1Q1MFG%2F%2H\Q[g00BYRQ#L%KQP31>30P11>37CI%N3%O3R7g00?^g00@=RQPQg00@]RQP3143@143A%3@,435P35G3R@g00DQP@CTg00A=FU1k7QP2P01j561i20=;56dAf341Ceb7b;b<X23X33X43A0210R1/11^23^33^43P2P?PJP9O3b6b8b9b:b>b=1C?IRJA;5J6RJ16?IR6[PJ\61^?Ip,5HgrowC]C:P5P3%[>P?g019i%_>P;POC`PCCaRC#9RO%?C,83#7/=H,FBRB'C%DBPOn0100000020000=09?/1KeA09P?/1KePNp,5Hfull9b:MC:PL%c:C:P=P8P:P;P:CdE5%E<P8P:P;p,2HcCWE5o"). Qed.

(* [comment removed for export] *)
Definition cs_eff : SyscallEffect :=
  mkEffect (Z_to_bv 64 (fa SB c + mfa)) [] [(Z_to_bv 64 (fa SB c + mfa), Z_to_bv 64 (new - mfa))].

(* [comment removed for export] *)
Definition cs_svc (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m1 : mem) (jr junk : list byte) (shj : list byte) (mm0 md0 stj : word)
         (ws chs : list word) (rand : word) (exh : byte) (pad : list byte) (nal nfr q0 q1 q2 q3 : Z),
    ms = MSsvc (rmap_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp1 - 128)) - 48)) gp (Z_to_bv 64 tpA)
                         t0' t1' t2' a6' (fa SB c + mfa) (new - mfa) (Z_to_bv 64 str_freearray) (Z_to_bv 64 (mc / 2))
                         (Z_to_bv 64 (P + 16 + 4 * (mc - mc / 2))) (Z_to_bv 64 (nf + mc / 2)) (Z_to_bv 64 2305843009213693952)
                         (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3' t4' t5' t6') F
               (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m1 (seg_rom asegs)
    /\ munch (W_CD T SB c usp) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ efs_A_cells m1 (Z_to_bv 64 (bv_unsigned sp1 - 128)) (Z_to_bv 64 rta_retE) (Z_to_bv 64 R) (Z_to_bv 64 nf)
         (Z_to_bv 64 c) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 INST) R (fa SB c + mfa) (new - mfa) new lo
    /\ rw_cells asegs m1 (bv_unsigned sp1 - 128)
         [CB 16 jr; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 (Z_to_bv 64 AB); C8 (Z_to_bv 64 c);
          C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 (cacheT T)); C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 drainhalf_retB)]
    /\ ri_lock m1 R 1152921504606846976 /\ ri_core m1 R nf mfa au (r_muser r)
    /\ ri_tail m1 R rand exh pad nal nfr q0 q1 q2 q3 /\ 0 <= nfr < 2 ^ 64 /\ 0 <= q0 < 2 ^ 64
    /\ fl_arr m1 SB c ws /\ 4 * Z.of_nat (length ws) = mfa /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r)
    /\ u32arr asegs m1 (P + 16) chs /\ length chs = 16%nat /\ firstn (length (ca Σ c)) chs = map (cpw c) (ca Σ c)
    /\ inst_cells SB m1 /\ thread_cells TCX T m1 /\ rw_cells asegs m1 (T + 2872) [C8 mm0; C8 md0]
    /\ rw_cells asegs m1 (shad (fa SB c + mfa)) [CB (Z.to_nat ((new - mfa) / 8)) shj] /\ ps_cells m1
    /\ pc_cells m1 P (mc - mc / 2) mc (ClassSize c) /\ rw_cells asegs m1 (cstat_alloc T) [C8 stj]
    /\ rw_cells asegs m1 (usp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m1 (usp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)]
    /\ rw_cells asegs m1 i_spacebeg [C8 (Z_to_bv 64 SB)].

(* [comment removed for export] *)
Theorem cs_A : evt asegs cs_svc cd_ms.
Proof using HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hfull Hgrow.
  pose proof (cd_geo Σ HG) as (HT & HSB & TSEP & G1 & G2 & G3 & G4). unfold SHB in G1. unfold kHighShadowEnd in G4.
  pose proof (cd_slot Σ c i st HG Hc Hi) as (P1 & P2 & P3).
  pose proof cs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14).
  pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & _). unfold kFaCap, kUMap, kUserCap in W1, W2, W5, W6.
  pose proof (dg_consts L m (proj1 HA)) as (IC & MMG & TC & PS & STS & UB).
  pose proof IC as (IC1 & IC2).
  apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  destruct IC1 as (SBC & _). cbn [cells_size csize Nat.add Z.of_nat] in SBC.
  pose proof (cd_pc Σ m c i HA Hc Hinit) as (chs & PC & CHS & Hchs & Hfch). rewrite Hfull in PC.
  pose proof HT as (T1 & T2 & T3 & T4 & T5). unfold img_hull_lo, img_hull_hi in T5.
  destruct (fl_c8_of_stk m (cstat_alloc T) ltac:(apply (dk_stk_within m _ _ _ _ STS); unfold cstat_alloc; lia)) as (stj & STJ).
  destruct (fl_two_c8 m (T + 2872) ltac:(apply (dk_stk_within m _ _ _ _ STS); lia)) as (mm0 & md0 & MM).
  pose proof (cd_reg Σ m c i HA Hc) as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hfw) & STU & SHU & STSH).
  apply ri_tail_norm in RT.
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dk_auser Σ HG c Hc) as AU.
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  assert (HTS : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) by (destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold kHighShadowEnd, SHB in *; lia).
  assert (HTX : (TCX + 0xa0 <= T \/ T + 4096 <= TCX) /\ (TCX + 0xa0 <= SB \/ SB + 2 ^ 37 + 4096 <= TCX) /\ 0 < TCX /\ TCX + 0xa0 <= l_ACEIL L)
    by (destruct TSEP as (_ & X1 & X2 & _ & _ & X3 & X4 & _); repeat split; assumption).
  assert (HSH : SHB <= shad (fa SB c + mfa) /\ shad (fa SB c + mfa) + (new - mfa) / 8 <= shad (rb SB c + 2 ^ 32)
                /\ shad (rb SB c) <= shad (fa SB c + mfa) /\ 0 <= (new - mfa) / 8 /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB).
  { pose proof (fk_shad_le2 (fa SB c + mfa) (new - mfa) ltac:(unfold fa, rb in *; lia) ltac:(lia)) as X1.
    pose proof (fk_shad_mono (fa SB c + mfa + (new - mfa)) (rb SB c + 2 ^ 32) ltac:(unfold fa, rb, kFaCap in *; lia)) as X2.
    pose proof (fk_shad_mono (rb SB c) (fa SB c + mfa) ltac:(unfold fa, rb in *; lia)) as X3.
    pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as X4.
    assert (X5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
    pose proof (Z.div_pos (fa SB c + mfa) 8 ltac:(unfold fa, rb in *; lia) ltac:(lia)).
    split; [unfold shad; lia|]. split; [lia|]. split; [lia|]. split; [apply Z.div_pos; lia | lia]. }
  destruct (stk_CB m (shad (fa SB c + mfa)) ((new - mfa) / 8) ltac:(apply (dk_stk_within m _ _ _ _ STSH); unfold SHB in *; lia) ltac:(lia)) as (shj & SHJ).
  unfold cd_msD.
  eapply evt_cut; [apply (cdealloc_drain_A_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                             F fc m (l_ACEIL L) T c AB mc (ClassSize c) lo)|].
  1: exact Hc. 1: exact PC. 1: lia. 1: lia. 1: exact HT. 1: exact ST. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: clear - P1 P3 G3 G2 Hc; lia. 1: exact MI.
  intros ms1 (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk & -> & MU1 & WM1 & MI1 & PC1 & FR1 & FR2 & ST1).
  assert (Esp1 : bv_unsigned sp1 = usp - 112) by (apply unsigned_lit; lia).
  assert (DJ1 : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= usp - 112 \/ usp <= a) -> disjoint_from [(P, P + 4); (usp - 112, usp)] a n).
  { intros a n Hn X1 X2. cbn [disjoint_from]. first [ clear - Hn X1 X2; repeat split; lia | split; [lia|]; split; [lia | exact I] ]. }
  pose proof (rw_cells_transport asegs _ m m1 _ _ (proj1 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as IC11.
  pose proof (rw_cells_transport asegs _ m m1 _ _ (proj2 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_premapped, g_instance, pc_addr in *; lia)) as IC21.
  assert (MMG1 : mm_gcells m1).
  { destruct MMG as (X1 & X2 & X3 & X4 & X5).
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X1 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X2 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X3 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport asegs _ m m1 _ _ X4 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    exact (rw_cells_transport asegs _ m m1 _ _ X5 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia)). }
  pose proof (rw_cells_transport asegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC1.
  eapply evt_mono; [apply (rta_A_spec (Z_to_bv 64 drainhalf_retB) sp1 gp (Z_to_bv 64 tpA) t0a t1a t2a (Z_to_bv 64 P) (Z_to_bv 64 (cacheT T))
                             a6a a7a (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) s5 s6 s7 s8 s9 s10 s11 t3a t4a t5a t6a F fc m1
                             (l_ACEIL L) SB c R (usp - 104) (cstats T) (P + 16) (mc - mc / 2) (mc / 2) nf mfa au (r_muser r) lo)|].
  1: exact HSB. 1: exact Hc. 1: reflexivity. 1: lia. 1: lia. 1: exact Hgrow. 1: lia. 1: exact N6. 1: exact N9. 1: lia. 1: lia.
  1: exact (conj IC11 IC21). 1: exact MMG1. 1: exact LK1. 1: exact RC1.
  1: rewrite Esp1; exact ST1. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia. 1: rewrite Esp1; lia.
  1: rewrite Esp1; lia. 1: exact MI1.
  intros ms2 (t0b & t1b & t2b & a6b & t3b & t4b & t5b & t6b & m2 & jr & -> & MU2 & WM2 & MI2 & EFS & FR3 & LK2).
  rewrite Esp1 in MU2.
  assert (MU01 : munch [(P, P + 4); (R, R + 8); (usp - 688, usp)] m m2).
  { apply (munch_trans _ m m1 m2); eapply munch_weaken; [|exact MU1| |exact MU2].
    - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia.
    - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }
  assert (WM01 : wmono asegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
  assert (DJ : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= R \/ R + 8 <= a) -> (a + n <= usp - 688 \/ usp <= a) ->
            disjoint_from [(P, P + 4); (R, R + 8); (usp - 688, usp)] a n).
  { intros a n Hn X1 X2 X3. cbn [disjoint_from]. first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  zhide.  
  assert (HRL : lo <= usp - 688 /\ l_ACEIL L <= lo) by lia.
  unfold cs_svc.
  exists t0b, t1b, t2b, a6b, t3b, t4b, t5b, t6b, m2, jr, junk, shj, mm0, md0, stj, ws, chs, rand, exh, pad,
    (bv_unsigned (Z_to_bv 64 nal)), (bv_unsigned (Z_to_bv 64 nfr)), (bv_unsigned (Z_to_bv 64 q0)), (bv_unsigned (Z_to_bv 64 q1)),
    (bv_unsigned (Z_to_bv 64 q2)), (bv_unsigned (Z_to_bv 64 q3)).
  split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU01]; unfold sub_fp, W_CD; cbn [outside]; intros x Hx; clear - Hx HLO2; repeat split; lia|].
  split; [exact WM01|]. split; [exact MI2|]. split; [exact EFS|]. split; [exact FR3|]. split; [exact LK2|].
  split; [exact (rw_cells_transport asegs _ m m2 _ _ RC MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m m2 _ _ RT MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (bv64_range nfr)|]. split; [exact (bv64_range q0)|].
  split; [exact (u32arr_transport asegs _ m m2 _ _ FL MU01 WM01 ltac:(apply DJ; [lia | unfold pc_addr, fa, rb in *; lia | unfold fa, rb, rinfo, RIS_of in *; lia | unfold fa, rb in *; lia]))|].
  split; [exact Hws|]. split; [exact Hfw|].
  split; [exact (u32arr_transport asegs _ m m2 _ _ CHS MU01 WM01 ltac:(apply DJ; rewrite ?Hchs; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact Hchs|]. split; [exact Hfch|].
  split; [split; [exact (rw_cells_transport asegs _ m m2 _ _ (proj1 IC) MU01 WM01 ltac:(apply DJ; cbn; unfold i_spacebeg, g_instance, pc_addr, rinfo, RIS_of in *; lia))
                 | exact (rw_cells_transport asegs _ m m2 _ _ (proj2 IC) MU01 WM01 ltac:(apply DJ; cbn; unfold i_premapped, g_instance, pc_addr, rinfo, RIS_of in *; lia))]|].
  split.
  { destruct TC as ((X1 & X2 & X3 & X4) & X5). split; [split; [|split; [|split]]|].
    - exact (rw_cells_transport asegs _ m m2 _ _ X1 MU01 WM01 ltac:(apply DJ; cbn; unfold g_tsd_key_inited, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport asegs _ m m2 _ _ X2 MU01 WM01 ltac:(apply DJ; cbn; unfold g_tsd_key, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport asegs _ m m2 _ _ X3 MU01 WM01 ltac:(apply DJ; cbn; unfold pth_tsd, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport asegs _ m m2 _ _ X4 MU01 WM01 ltac:(apply DJ; cbn; unfold g_pthread_tsd_main, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport asegs _ m m2 _ _ X5 MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)). }
  split; [exact (rw_cells_transport asegs _ m m2 _ _ MM MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m m2 _ _ SHJ MU01 WM01 ltac:(apply DJ; cbn; rewrite ?Z2Nat.id by lia; unfold pc_addr, rinfo, RIS_of, SHB in *; lia))|].
  split; [exact (PCP_framed m m2 _ PS MU01 WM01 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi, pc_addr, rinfo, RIS_of, SEGTOP_A in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m1 m2 _ _ PC1 MU2 WM2 ltac:(cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m m2 _ _ STJ MU01 WM01 ltac:(apply DJ; cbn; unfold cstat_alloc, pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(cbn; unfold rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport asegs _ m1 m2 _ _ FR2 MU2 WM2 ltac:(cbn; unfold rinfo, RIS_of in *; lia))|].
  exact (rw_cells_transport asegs _ m m2 _ _ SBC MU01 WM01 ltac:(apply DJ; cbn; unfold i_spacebeg, g_instance, pc_addr, rinfo, RIS_of in *; lia)).
Qed.

End CSlow.
