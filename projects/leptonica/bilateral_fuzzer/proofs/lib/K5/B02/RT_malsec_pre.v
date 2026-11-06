(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Exec RzCPS MState ITree.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require BackingAlgebra.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface D_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_sec_defs R_fs_defs R_mmapordie R_secalloc R_comballoc2 R_asan_defs R_allocate1 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_maltail RT_malcore_stmt RT_malcore_m RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_tail RT_malsec_rev.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_malsec_pre () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool;orb_false_rK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega5Tauto4kind02I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem3Run;zeros_coverC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init5Logic4True01C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K52AS8AsanAcctHfind_segment1_none_aboveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7ro_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8seg_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3MemAmem_inv_seg_belowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc69OSSVerify5KrLib2K53B02=RT_malsec_pre=ro_addr_aboveC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib3Mem:mem_inv_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@mem_inv_ov_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem4UTOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS7set_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3HIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC46Stdlib4Bool4Bool=orb_false_iffC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib2K52AS8AsanAcct3mkHC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_mapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53B028RT_state4smszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7l_ACEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9art_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53B028RT_state>startup_grantsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53B028RT_state5l_PRBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_FSBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=RT_malsec_rev>rv_grant_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_posC69OSSVerify5KrLib2K53B028RT_state2prC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4r_stC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK69OSSVerify5KrLib2K53B028RT_state4ckst02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4l_SBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_ubegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_PABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3l_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_TCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DTVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_DNBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5l_SSBC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B028RT_state3secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4s_mbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_quarC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6s_ubegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3s_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8grant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7rt_mapsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib2K53B028RT_state6secmapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53B028RT_state7l_maps0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_revC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C46Stdlib5Lists4List6in_mapC46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib2K53B02=RT_malsec_rev:rv_sec_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo0:geo_of_ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit6fk_mapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_glue_defs3ru8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_fkit8fk_aceilC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B026RT_sep=art_avoid_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<consts_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9reg_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pclass_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<pchunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<schunk_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9sec_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans:quar_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans9dep_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans4dsjlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans<shadow_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep5av_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans8fs_avoidC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2K53B026Layout?K_LOW_SHADOW_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout@K_HIGH_SHADOW_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep4CS_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state4ckst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B028RT_state5secst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans7ia_litsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo06geo_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep8geo_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6p_abegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs2rbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo07g_grantC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo05g_prbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib5Lists4List<In_nth_errorK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib2K53B028RT_state8kUserCapC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53B028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=RT_malsec_rev5W_revC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=RT_malsec_rev6rv_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_rangesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre7cl_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo07g_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027RT_geo0:g_frame_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9layout_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7regs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6sec_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5fs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fs_cls_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3fs1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53B029R_fs_defs2NFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natI35stdpp4base5NoDup00C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53B028RT_state5fs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9fss_flagsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029R_fs_defs5nbusyC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List6filterC69OSSVerify5KrLib2K53B028RT_state8fss_hintC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC69OSSVerify5KrLib2K53B029R_fs_defs:frame_addrC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr09I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C69OSSVerify5KrLib2K53B02=RT_malsec_rev8rv_fshadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:RT_maltail9shad_add8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef3nthK46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC69OSSVerify5KrLib2K53B028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=CLIENT_STATICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9RT_STATICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7CREDIT0C1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C69OSSVerify5KrLib2K53B02@RT_malsec_front22fAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?RT_malsec_state4sgΣC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ARTM_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02@RT_malsec_front22fKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?RT_malsec_state3shwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre4bpreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS8revealedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?RT_malsec_front:front_postC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2K53Lib5RzCPS5nretAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass7rz_sizeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_asan_defs7needed2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass<from_primaryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC69OSSVerify5KrLib2K53B02:R_secalloc@secalloc_A1_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs6sa_mszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_mmapordie8mod_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_secalloc8sa_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_mmapordie9mod_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_prim_defs9mm_gcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs8sec_pageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs:name_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02@RT_malsec_front27smsz_saC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs9roundup4kC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib2K53B028RT_state5l_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7rtA_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep8W_clientC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep@art_avoid_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_trans=ART_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep5ART_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre?nretA_mem_zerosC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre;zeros_munchC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre;zeros_wmonoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre8mp_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=RT_malsec_rev=rev_munch_hypC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_vis<reveal_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_vis<reveal_wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=RT_malsec_rev9rev_avoidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep6ART_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7live_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7quar_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state9budget_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs8depot_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs3d_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<R_depot_defs5d_totC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state7dep_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state8rt_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02>RT_malsec_tailAmap_range_visibleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02>RT_malsec_tail=nret_revealedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7vis_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:RT_maltail8af_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:RT_maltail9trc_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4nretC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc69OSSVerify5KrLib2K53B02=RT_malsec_pre=zeros_mem_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre>reveal_mem_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=RT_malsec_pre:cl_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<RT_malcore_m=aclient_splitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsI46Stdlib7Sorting;Permutation;Permutation00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC69OSSVerify5KrLib2K53B028RT_state8rt_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep8artm_sysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep>lazy_in_maps_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep9confined0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep;shadow_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep7ART_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_vis>vis_rep_revealC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_frame9stk_wmonoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:RT_maltail<af_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=R_unwind_defs8wr_traceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib2K53Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List>ForallOrdPairs00C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC69OSSVerify5KrLib2K53B026RT_rep;maps_zboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib;NodesA_madv<noaccess_posC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffI69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib2K53B028RT_state7VMLIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_rep8iv_apartC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K53B02<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C69OSSVerify5KrLib2K53B02<R_comballoc2>comballoc_retSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_secalloc7sa_retAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs8sec_nameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;R_mmapordie>sec_mmap_ecallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs5GSTATC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:R_sec_defs3SECC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep7live_ivC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep8frame_ivC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026RT_sep8fshad_ivC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state4vposC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_state6E0_MAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib2K53B02;R_glue_defs:i_sec_pageC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nretA_mem_zeros : forall (ms : machine_state) (P len : word),
  ms_mem (nretA ms (mkEffect P [] [(P, len)])) = apply_zeros (ms_mem ms) [(P, len)].
Proof. intros ms P len. reflexivity. Qed.

Lemma zeros_munch : forall (m : mem) P len, 0 <= P -> 0 <= len -> P + len < 2 ^ 64 ->
  munch [(P, P + len)] m (apply_zeros m [(Z_to_bv 64 P, Z_to_bv 64 len)]).
Proof.
  intros m P len H1 H2 H3 x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. unfold apply_zeros, zeros_cover. cbn [existsb fst snd].
  rewrite !unsigned_lit by lia. rewrite orb_false_r.
  replace ((P <=? bv_unsigned x) && (bv_unsigned x <? P + len)) with false by (symmetry; apply andb_false_iff; lia). reflexivity.
Qed.

Lemma zeros_wmono : forall (m : mem) zs, wmono asegs m (apply_zeros m zs).
Proof.
  intros m zs x Hx. unfold apply_zeros. destruct zs as [|z zs]; [exact Hx|]. unfold wview in *.
  destruct (zeros_cover (z :: zs) x); [discriminate | exact Hx].
Qed.

Lemma ro_addr_above : forall a : word, SEGTOP_A <= bv_unsigned a -> ro_addr asegs a = false.
Proof. intros a H. unfold ro_addr. rewrite (find_segment1_none_above asegs SEGTOP_A _ asegs_below H). reflexivity. Qed.

Lemma zeros_mem_inv : forall (m : mem) P len, mem_inv asegs m -> SEGTOP_A <= P -> P + len <= 2 ^ 47 -> 0 <= len ->
  mem_inv asegs (apply_zeros m [(Z_to_bv 64 P, Z_to_bv 64 len)]).
Proof.
  intros m P len MI H1 H2 H3. apply mem_inv_intro; [intros a Ha; exact (mem_inv_seg_below asegs m a MI Ha)|].
  intros a b Hb. unfold apply_zeros, zeros_cover in Hb. cbn [existsb fst snd] in Hb. rewrite orb_false_r in Hb.
  rewrite !unsigned_lit in Hb by (unfold SEGTOP_A in *; lia).
  destruct ((P <=? bv_unsigned a) && (bv_unsigned a <? P + len)) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [apply ro_addr_above; lia | unfold UTOP; lia].
  - split; [exact (mem_inv_ro asegs m a b MI Hb) | exact (mem_inv_ov_below asegs m a b MI Hb)].
Qed.

Section Reveal.
Variables (A A' : list (Z * Z)) (mo : Model) (ms0 ms : machine_state).
Hypothesis HR : revealed A A' mo ms0 ms.
Hypothesis HH0 : forall a, HID A mo a = true -> ms_mem ms0 a = None /\ SEGTOP_A <= bv_unsigned a.
Hypothesis HH1 : forall a, HID A' mo a = true -> ms_mem ms a = None.

Lemma reveal_mem_inv : mem_inv asegs (ms_mem ms0) -> mem_inv asegs (ms_mem ms).
Proof using HR HH0 HH1.
  intros MI. destruct HR as (_ & Hv & _).
  apply mem_inv_intro; [intros a Ha; exact (mem_inv_seg_below asegs _ a MI Ha)|].
  intros a b Hb. destruct (HID A mo a) eqn:E1.
  - destruct (HID A' mo a) eqn:E2; [rewrite (HH1 a E2) in Hb; discriminate|].
    destruct (HH0 a E1) as (_ & Ht). unfold HID in E2. apply orb_false_iff in E2 as [_ E3]. apply Z.leb_gt in E3.
    split; [exact (ro_addr_above a Ht) | unfold UTOP; lia].
  - rewrite (Hv a E1) in Hb. split; [exact (mem_inv_ro asegs _ a b MI Hb) | exact (mem_inv_ov_below asegs _ a b MI Hb)].
Qed.
End Reveal.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Map.
Variables (Σ : rtsA) (m : mem) (P n : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x8000000.
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).

(* [comment removed for export] *)
Lemma mp_avoid : art_avoid [(P, P + msz)] Σ.
Proof using HA HG Hn.
  pose proof (rv_map Σ m P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  assert (R_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from CS_W a k -> disjoint_from [(P, P + msz)] a k)
    by (intros a k H1 H2 _; cbn [disjoint_from]; split; [lia | exact I]).
  assert (R_grant : forall b gn a k, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
            b <= a -> a + k <= b + gn -> disjoint_from [(P, P + msz)] a k).
  { intros b gn a k Hin _ _ H1 H2. pose proof (rv_grant_apart Σ m P n HA HG b gn Hin) as X. unfold apart in X.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_shad : forall lo hi a k, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + k <= shad hi ->
            (forall f k', In (f, k') (frames Σ) -> hi <= f \/ f + fs_size k' <= lo) -> disjoint_from [(P, P + msz)] a k).
  { intros lo hi a k H1 H2 H3 H4 H5 H6 _. cbn [disjoint_from]. split; [|exact I].
    assert (shad hi <= 2 ^ 44 + SHB) by (unfold shad; assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
    assert (SHB <= shad lo) by (unfold shad; pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)); lia).
    unfold SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia. }
  assert (R_prb : forall a k, l_PRB L <= a -> a + k <= l_PRB L + 0x2000011000 ->
            (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
               a + k <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros a k H1 H2 _. pose proof (rv_grant_apart Σ m P n HA HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as X.
    unfold apart in X. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_secmap : forall k0 s0 a k, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + k <= s_mb s0 + smsz (s_n s0) ->
            (s_quar s0 = false -> a + k <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros k0 s0 a k Hk H1 H2 _. destruct HG as (_ & Hap).
    pose proof (proj1 (Forall_forall _ _) Hap (secmap s0) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s0)); exact (nth_error_In _ _ Hk))) as Y.
    pose proof (rv_sec_app Σ m HA k0 s0 Hk) as (_ & Z1 & Z2). pose proof (fk_map Σ (geo_of_ART Σ m HA) k0 s0 Hk) as (_ & _ & Z3 & _).
    pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (_ & Z4).
    unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by lia. unfold apart in Y.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_fsb : forall a k, l_FSB L <= a -> a + k <= l_FSB L + 0xb09000 ->
            (forall f k', In (f, k') (frames Σ) -> a + k <= f \/ f + fs_size k' - 8 <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros a k H1 H2 _. pose proof (rv_grant_apart Σ m P n HA HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as X.
    unfold apart in X. cbn [disjoint_from]. split; [lia | exact I]. }
  destruct (art_avoid_gen Σ m [(P, P + msz)] HA R_img R_grant (fun lo hi a k H1 H2 H3 H4 H5 H6 H7 _ => R_shad lo hi a k H1 H2 H3 H4 H5 H6 H7)
              R_prb R_secmap) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof (av_fs Σ m [(P, P + msz)] HA R_img R_grant R_shad R_fsb) as A10.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [exact A7|]. split; [exact A10|]. split; [exact A8 | exact A9].
Qed.
End Map.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Client.
Variables (Σ : rtsA) (m : mem) (P n sp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x8000000.
Hypothesis Hsp : l_ACEIL (lay Σ) <= sp.
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).

(* [comment removed for export] *)
Lemma cl_live : forall p k x, In (p, k) (live Σ) -> p <= x < p + k ->
  (x < K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= x) /\ (x < P \/ P + msz <= x).
Proof using HA HG Hn.
  intros p k x Hin Hx. pose proof (geo_of_ART Σ m HA) as HGo.
  destruct (geo_live Σ m HA p k Hin) as [(c & i & Hc & Hi & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y5)].
  - pose proof (g_grant Σ HGo (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
    pose proof (g_prb Σ HGo) as (P1 & P2 & P3).
    pose proof (rv_grant_apart Σ m P n HA HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap.
    unfold rb, kUserCap, apart in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct (In_nth_error _ _ Hs) as (k0 & Hk0). pose proof (rv_sec_app Σ m HA k0 s Hk0) as (X & _ & _).
    destruct HG as (_ & Hap).
    pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact Hs)) as Y.
    pose proof (fk_map Σ HGo k0 s Hk0) as (_ & Z1 & Z3 & _). pose proof (fk_aceil Σ HGo) as (_ & Z4).
    unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by (pose proof (rv_sec_app Σ m HA k0 s Hk0); lia).
    unfold apart, s_ubeg in *. rewrite <- Hsn in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cl_outside : forall x, aclient (live Σ) (frames Σ) sp x -> (x < P \/ P + msz <= x) /\ outside (W_rev Σ P n) x.
Proof using HA HG Hn Hsp.
ltac2:(KReplay.run1 (kr_t_RT_malsec_pre ()) ["Client"] "p'0h01Hh14__x1h24__x2h37__sat10h46__sat9h57__arithh64__ffh78__varmaph85__with94__x3h:4__x4h;4__p1h<6__sat6h=6__sat7h>6__sat8h?3Hlhh@7__sat11hA4__x5hB7__sat12hC7__sat13hD7__sat14hE7__sat15hF1khG2_HhH7__sat16hI4__x6hJ1ahK2hihL1pi001phM3_H0hN4__x7hO1fhP2lohQ1zi011zhR1EhS2HahT3HinhU4__p2hV4__x8hW1bhX2H0hY2Y1hZ2Y2h[3_H1h\1nh]2Aph^2G2h_2G4h`2HFha3Hf8hb3Hfxhc2Y3hd3_H2he7__sat17hf1ehg2fkhh7fv_listhi8hyp_listhj3lmphk1xi021xhl1yhm3APPhn1Dho2Eqhp2G1hq2G3hr3HGohs3Hfaht2Hkhu3Hk8hv2Hphw3Hpxhx2Hxhy2Hyhz2M1h{2M2h|2M3h}2M4h~2M5i032SHi042X1i052X2i064cstri071qp%0p%1p&0p&1p;1p;4p;3p;7p;2p;:p;6p;5p;9p;<p;8g02H\k11wTg01Rdk11vTg02V8k416Tg020Ak30vTg02IUk11uTg01E?k71STg003_j12Tg00<@j1ATg01F?j2FTg01F_k10tTg00;cR0j20Tg01GXk11fTg01HPk11^Tg00?:j21Tg00CaR1j2BTg00I1j1;Tg00<^j2oTg00iTR2j2lTg00?VR3j24Tg02W4k30wTg0234k20uTg00D]k20VTg00EEk30TTg01KIj2`Tg007ek10DTg00Eik10LTg00GEk11eTg00Gck11bTg00HNk20iTg00J]k11PTg00LGk21LTg009]k20cTg00Lik21ETg00MUk31?Tg00N4k41>Tg02X3m:1;Tg02Y3k60lTg00>Aj2sTg02Z5k10HTg02[7k207Tg02\3j2rTg02]1j2pTg00P=j1bTg00P\k20nTg00RZk10yTg00S8k20ZTg00=;j2GTg004Dk10XTg00S[k30WTg0195k402Tg02^6j2xTg00@1k101Tg006eR4k20;Tg01Maj35Tg00A0j37Tg008Ej3OTg02_4k50sTg01S_j16Tg02M?S00k20:Tg02`5k50rTg01Olk10qTg01N8k10oTg01]3k11tTg01]mk11sTg01^ek11rTg01__k11oTg01`Yk11nTg01aSk11kTg01bMk31iTg024Sk30CTg01L^k11hTg02NYk50STg01gFk31dTg01Pfm91cTg01O2k41aTg0240k31`Tg01Qnj1@Tg02a0k51_Tg02ank11]Tg02blk11ZTg02chk11YTg02dck11XTg02e]k11WTg02fUk20KTg02gSk11RTg02hKk11QTg02iCk11OTg02j;j1DTg02j[j1yTg02kSk10@Tg01i?k31NTg02l3k21MTg02lHk20fTg02lhk20eTg02mbk10dTg02n`k11KTg02o[k21JTg030;k31HTg030Vk11GTg031Sk11FTg01U>R5j2>Tg01i`k31CTg01mik61BTg032Nk20ITg032nk31ATg033Rk30aTg034Rk11<Tg035<k20JTg00j1k10_Tg035fk30\Tg036Pk11ITg0378k40^Tg037^k70gTg038Mk40]Tg002Ik60RTg038gk219Tg039Gk118Tg039lk31TTg03:Um<1UTg01VGj2YTg01JJk317Tg03;Wk41VTg01Vdk20ATg01WUk414Tg01T[k313Tg01U[k51[Tg00FIk21\Tg00Fgk40>Tg00WJk408Tg00X5k709Tg00Kck712Tg00IVk311Tg00Yak80BTg00XYk70[Tg00QEk30jTg00Qnk20mTg01L:k610Tg007Ek40kTg03<Wk61gTg00OBk70~Tg00UZk30}Tg00U=k31jTg03=4k40|Tg00J9k61lTg03=Pk21mTg03>:k30{Tg03>dk31pTg03?Nm:1qTg03@?m<0zTg00ZER6f0R7'Gp=?%27#2p=Rg00[cR8?776p=~g02C:S01/17p=m%;7#2#2#2p>04%27#2#2#2#2#2#2#Ap=q%27#2#2#2p=v%;7#;p=H%27#2#2#Ap=zf2R9f1R:'1/47p=\1F9:=786/47p>0Ff5R;f4R<'Gf3R=/19'B1s:7'4p=8109:/17p=Ig02B8S02,G7p>001167p=321\87p=tP8P9P:P7H0>p=E20i87p=JP9g00\hR>g00]GR?P?g00]gR@P8P:g00^gRAP7H08g00^GRBK09p=cP9P>P?P?P@P8P:g00\ARCP7H08PBK09p=<P9P>P?P?P@P:P7K12p=a20Z87p=TB118:7p=KP=P>P?P?P@P9P:P7L0Bp=Ug00ZcRDg00a6RE777p>0P1G=911:7'Bp=h11:7,B9p=gP<P>P?P?P@P=P9P>P?P?P@P8P:PAP7H08PBK09K0[p=n11=91G:7'4p=91B:7,B9p=i20n87p=kB0j8:7p=dB0j8:7g00bRRF+0mp=ug00`JRG?O:7p=]P8P8P<P=P9H0>P:P7H0>p=QP:P>P?P?P@P7J10p>0=P9P>P?P?P@P:P7K0[p>0YP;P>P?P?P@P<P>P?P?P@P8P=PCP9H08PBK09P:P7L0Bp=Lf6RCP>P?P?P@P;P<P=P>P?P?P@P9P:P7L0BL0Bp=VP8P<P=P8P9P:P7H0>H0>p>0x%;7#;#;#;p>03%27#2#2#2#2#2#2#2p>0OP8P:PAP7H08p>0EP<P>P?P?P@P=P>P?P?P@P9PBK09P:P7L0Bp>0<P8P8P:P7H0kp=:11=91G:7'4,4<p=N20:87p=w%27#;p=X%;7#2p=Sg011`S03,G7p=[P<P8P=P9P:P7J1gp>05A78:7p==1G:7,49p=^P8P;P<P=P9P:P7K0~p=}1G9:/B7p>0N1G:7,49,4=p>0U1B9:/47p>0MP8g02AYRAP:P7H0kp=C1s:7,49p>0pg00b3RH97A7p=|A7A:7p=ZA7A9:/B7p=j1F=9=786%6:/F7=786'4p=_1F:7=786p=PA78961F:7=786'4p>0hB0}8A7p=MB1j8A=B0a9:7578p=fP8P=20e9:$0dP6H0|=787p=e14:7,49p>0?119:/47,4=p>1DP8P:g02UQP7H08p>0QP:P>P?P?P@P7PBK09p>0`P:P>P?P?P@P7J1lp>0b%6:/F7=786p>1=%27#Ap>1@21m87p={B0{8:7p=WB1p8:7p>06P8P6P:P0P5P2g03@lR>g03AIS04g03AfRBP7N:1qp>1:P8P6P9P0P5P2P>Q04PBg03BGS05P:P7N<0zp>0G20m7Fp>15p,2ΣRF$1wRB&1vFR>p,2spR2P7H16p,1mS06p,2HAS0760vF&1uFS08PFQ06p,1PR5p,1nS09Q07p,2HGS0:p,2HnS0;K1S%?5S0<g00;>R0#2S0=#2S0>#2S0?#2S0@#RS0A#2#RS0B#2#RRI#ARJ,F5RK#~S0CQ09$0tS0D,05RL&1fFRM$1^S0E'1S0FQ02,1L%m5'BS0GQ03/15S0HQ0?#;S0I#;$04#qQ0DQ0DQ0D&04I#v#qQ0EQ0=#ARNQ0=#;S0J#;S0K#HS0L#ARO'oS0M%2IRI#2#RS0N#vS0O#zS0P'l'13\80FJ3\S0Q'4S0R'4S0S'4S0T'4S0U'4P3Q0<Q0UP<P5PLP<Q09:0wF5RPP<E8P7Q0<Q0UP3Q0CQ0Tf8RQP5PLPQPPPQE8P7Q0CQ0TP3Q0FQ0Sf<RRP5PLPRPPPRE8P7Q0FQ0SP3Q0GQ0Rf@RSP5PLPSPPPSE8P7Q0GQ0RP3Q0HQ0QfDRTP5PLPTPPPTE8P7Q0HQ0QfES0V-0uFQ0K#RS0W#ART,oNRUg02E4S0XQ0E3IS0YQ0EQ0M'1S0Z'4P3Q0YQ0ZfIS0[P5PLQ0[PPQ0[E8P7Q0YQ0Z&007%m7'BRVPPP:%A0RWP:PFQ06P5Q09Q07Q0:Q0;P:PW20VNORX%?NRY%3OQ0M#?[[RZ%3NR[g00_nR\B0TNO:UWSROQ0M#3\\^S[R]20VNTR^%3T%?U[\YRYB0TNT:V\XS[RT%3U\\^S[R[1`5JR\%35%3JS0\%3K[[RK&0DGR_&0LGRG%t9S0]%t=S0^7E:S0_&1e8R`&1b8Ra20i80RbQ0=#JRc5caS0`%;0S0a#JS0b=<abRd5aaS0c&1P?R?%TW,KbRe=<ac=aadCU21La@R@P7P920cDES0d21E79$0PdB1?86:H1>REb6b7b8X18X28X98P7P:P9P7ChAI:W9?g=:[^18^28^98P7Q01Q02f7RDPCO4b5b<b=b>b4b3N:1;PXPZPOP]P^PYPTP[P\PKP_PG%t:S0eP`PaA<abbPaPbPeDnP@PEb6b7b8X18P7P7P7107WC9^18P7PDO1b5b<b=b>b4b3J0lWyXl81sP:\V^l8P1P2fMRVPVg03C6ReC9&0HV207BV1r>V1p>V'B3ifNRdP5PLPdPPPdE8fLS0fP2PdPdPeC9fORfP5PLPfCh1sPfPXPZPOP]P^PYPTP[P\PKp-0Rg%bHRh#bRi#bS0g#bS0h#kS0i%kiS0j%khS0k20n8HS0l'dS0m'd'u/]_RHPG&0y8RjP9%t;S0nP:%t<S0o?E=jDQP`PaPaQ0b,KcS0pQ0J#JRkP?Pa20Z86Rl=cacS0qP?PaQ0a#2S0r#JRm=<ab20=aDRn60YaP?PaPaPkPmP?20=aQQ0p=<abS0s5aaELFVELP@PEb6b7b8X18X28X98X:8XA8X;gWU10:9S0t/1=%?9S0uA\C9D11CDS0vf:Rm10;C;g<[[[[^18^28^98^:8^A8^;g^UgP7fURo/G51GoeReP2Q0EQ0DP5PofGS0wPfPCp,3HspRpO;b5b<b=b>b4b3P9PfPXPZPOP]P^PYPTP[P\PKPHPGQ0]?E<jS0xP:Q0^P<Q0oI0xP`PaPa%TNS0yQ0W$0X60W8S0zQ0a#;S0{#;S0|#;#H$03$03S0}#;$0O#qS0~#TS10'KQ0>#JS11P?PaPaQ0{#JS12-0ElP?PaA<akb20=aC60YaP?PaQ11=<akP?&03I$03$03$03$0O#qS13#TS14=<ab9aanFVI0<ELP@PEb6b7b8X18X28X98X:8X;gXUgQ0~=IU:%?<S15A\<9C11<;f9RnQ13;g<[[[[^18^28^98^:8^;g^UgP7&00oPeP5P2Q0EPoPmPfPCPpO:b5b<b=b>b4b3&00f%mf'BeO2H02W0P7O1&0Hd207Bd1r>d1p>d'B3iP1&0Hf207Bf1r>f1p>f3ifPRdP5PLPdPPPdE8P7&0HdP3g03D5RpfQR2'xg03E7Re/x2$01fRRIP5PLPIPPPIE8S16P7fSRk,xpQ00P820;88RH1::7S17;5pRqP:fVS18Q18P7DNXK8#wXP81xeo$01Q18P5PLQ18PPQ18E8S19[P7PqP:fXRqPqP7DNXK8#wQ00P81:97S1:=5HpP9fYRrPrP7DNXK81xer$01fZRsP5PLPsPPPsE8S1;[P71:<7S1<=5HpP<f[RtPtP7DNP31:;:S1==5HpP;f\S1>Q1>P:C9f]Ru,xe$01f^S1?P5PLQ1?PPQ1?E8S1@[P71:D=S1A=5HpPQf_RpPpP<C9f`Rv,xe$01P1%20#R#X#H#X#H#S#S#S#zRe%20#R#S#H#R#H$04#H#zRw':Rx1:mCRy57H%;0#R#X#H$04#X#H#S#S#zRz%;0#R#S#X$04#X#H#S#S#zR{':R|%;0#R#H#X#H#X#v#X#X#zR},:{S1B&0DHS1C5OHS1D5OHS1E95HyfbRy#[P9f;S1F/:DS1G97HxPHP4P8P8P8P7P7n2001100000120101101XfHS1HPx1:RQS1IP7I051=wQPHP4P8P8P8P7P:n2001100000120101101XfHS1JPxf=Rx/:nS1KP:I051=exf>S1L,=ePeP7fgS1MQ1MPRC91=wxfiS1N#[S1O[]?XP8PeffR4P4Q1FC91=wRPwPeQ1NQ1NP7C9fjS1P#[]?XK8PefhR~P~PwC9PXPZPOP]P^PYPTP[P\PKP_PGQ0eP`PaPa20=a=S1QPaPb%TwDnP?%;0#R#H#X#H#S#v#qS1R#T9cabS1SCUP@PEb6b7b8X18X;gA^:7wQ1R,G:S1T[^18^;gP7foS1U,1eQ1UPCO3b5b<b=b>b4b3Q1OeW?PxP7P:E}W0W?f?ReP7PCE}W0P7O1b0P7O1b0WRP7O1Q1GQ1E55HP1Q1I97H|Q1IQ1D55HfdS1I#[P7Q1K97H|PHQ1HP|Q1L/:mRwP7I051={mPHQ1JP|Q1F,:eR|P:I051=ze1=zSPzP7Q1NQ1NQ1LC91={efkS1G#[S1E[]?XP8PzP~P~PxC9Q1L,={P{PzQ1GQ1GP7C9flS1O#[]?XK8PzQ1PQ1PP{C9PXPZPOP]P^PYPTP[P\PKP_PGQ0eP`PaPaQ1QPaPb%T{DnP?Q1SCUP@PEb6b7b8X18X;gA^:7{Q1T[^18^;gP7fqS1V,1zQ1VPCO3b5b<b=b>b4b3Q1EeW?PeP7P:E}W0W?fARzP7PQE}W0P7O1b0P7O1b0WRP7O1Q1KQ1D55HP1Q1B=7HwQ1C95Hw%[4P7Q1B=7H|PHQ1HQ1B1:SRP7I051=}RPHQ1JQ1B1:zxP:I051={zfB,={P{P7Q1GQ1GPSC91=}zfmS1B#[Rw[]?XP8P{Q1PQ1PPeC91=}SP}P{Q1BQ1BP7C9fnS1P#[]?XK8P{Q1OQ1OP}C9PXPZPOP]P^PYPTP[P\PKP_PGQ0eP`PaPaQ1QPaPb%T}DnP?Q1SCUP@PEb6b7b8X18X;gA^:7}Q1T[^18^;gP7fsS1T,1{Q1TPCO3b5b<b=b>b4b3PweW?PzP7P:E}W0W?fCP7PmE}W0P7O1b0P7O1b0WRP7O1Q1C95H|g00aVS1J%[~P7n010000000W0P7O1n200100000021100010000W0P7O1n200100000021100011000W0P7O1n200100000021100011000faR|#[PyP5PLPyCh1sPyPXPZPOP]P^PYPTP[P\PKQ0g#kS0gQ0jQ0l'dS1H'u/]_PGPjP9Q0^?E=jP:PjDQP`PaPaQ0J#2S0J#JRz-0EbP?PaPaPzPcP?PaQ0qP?Q0`20=a;5aaCUELI0<P@PEb6b7b8X18X28X98X;g1G7911=9%?=B0N=<C[[[^18^28^98^;gP711L~Q03P5P~PCPIPyO7b5b<b=b>b4b3Q0VPyPXPZPOP]P^PYPTP[P\PKP_PGQ0eP`PaQ1SP?Q0}#2#H#S#v#qS0}#TS1S9cabQ1Q5aaCUP@PEb6b7b8X18X;gQ1R,G7Q0}>0N:9[^18^;gP7%m~P~PCO3b5b<b=b>b4b3&00y%my'BRgeO2H02b0WGW?WTP:P7O2n2001000000121000000W0XK8P:P7O2n2001000000121102000W0XP8P:P7O2n2001000000121102000W0P:P7O2n2001000000121000000W0P7O1207Bd1r>d1p>d3iP1207B21r>21p>2'BQ16P7207BIQ00P8Q17=5HBRzP:PoPo10:7RwDNX\8#wXL8fTR{P5PLP{PPP{E8R}P7PzfWS17,1:RzQ17PwH0UX\8#wQ00P8Q1:=5HBP9PqPq1097DNX\8PqP5PLPqPPPqE8P7Q1<=5HBP<PsPs10<7DNP3Q1==5HBP;PtPt10;:C9Q1>P5PLQ1>PPQ1>E8P7Q1A=5HBPQQ1?Q1?10Q<C9PnP;PpP:P7I0s&00p%mpPpP5PLPpCh40MP3&00v%mv'BPvP5PLPvChP|P5PLP|PPP|E8P7fcRBP5PLPBChS1AQ1IP5PLQ1IChQ1I,sPP7Q0wQ1IP:O2H02WZXYgP:P7O2n2001000000120000000bJWwWTP:P7O2n2001000000120000000W0XF8P:P7O2n2001000000120102000W0XL8P:P7O2n2001000000121102000W0P7O11r>I1p>I'BP11r>k1p>kP}P71r>{Q00P820;8AR}1C:7;5>S0wPzQ17%67Rz,0:S1=Q0?#AR1'lRgH0UXFA-0:AXO8Q19P7Q0wP:PrPrPgDNXFA-0:AQ00PA1C97=5}>S1<P9PsPs109zS1:/l1DNXFAQ1;P71C<7=5}>S16P<Q1>Q1>10<zS1R/l1DNP31C;:=5}>S1QP;PuPu%6:,0;S0V/l1C9Q1@P71CD==5}>S1KPQPvPv%6<,0QS1D/l1C9PFPpPnP;P:I0rS1E&0qMRzQ0>#;S1W#2$0OS1X#zRg'0S1Y%6;S1Z,0nQ0W#2#X#R#S#v#qRw,0zReQ1Z#?3\7\nS1ZP3Q1Y/1mS0W%6CS1[,0mQ1[#?7\eS1[Q1A@0pPBS1AP7Q1Y/1RS1\%6nS1],0xQ1]#?7\eS1]P3Q1L%6mS1^;IeS1LQ1^#?S1^Q1MP5PLQ1MPPQ1ME8S1_P7%6R=ISeS1`%6x#?S1aPFP~PzPw&0oMQ0O$04#S#v#q':1:zwR~57H&1tMQ0P':S1b&1sM/:JS1c&1rMQ0N#AS0N':S1d&1oM/:JS1e&1nMQ0O#A':&1kMQ0P':Q1C5OH5OHS1C9OH~S0P5OHS0O5OHRx5OHRR5OH95H~Q1b=7H~A5H~RQ1c=7H~A5H~xQ1d=7H~Q0O95H~Q1e=7H~Q0P95H~A7H~~Q1C95H~20cH~41i40C40C40C40C40C&1hM95H~eS1CI0SB1dMzwS0PP3%?zS1e1FzJS0O#~S1dQ0E,1eS1cQ02,1e%mz'BS1bQ0N,1eQ03;gzS03'4S0N'4R~'4S1fQ1OP5PLQ1OPPQ1OE8P7Q1eQ1fP3Q1dP~fpRHP5PLPHPPPHE8P7Q1dP3Q1cQ0NftS1OP5PLQ1OPPQ1OE8P7Q1cQ0NP3Q1bQ03fxS1gP5PLQ1gPPQ1gE8P7Q1bQ03PFQ06P5Q09Q07Q0:PzPwQ1CN91cS1hP5Q0DPzPwH1aS1if|RHP5PLPHCh1sPHPXPZPOP]P^PYPTP[P\PKQ0h#bRx#bRR#bS0h#kS1j%kRS1kQ0jQ0k'dS0k'd'uS0jQ1j%kxS1lQ0gQ0l'd'dS0g'uS0l/]_']PGQ0n?ECjP9%tCS1m9EjCP:Q0o9Ej=DQP`PaQ0pQ0{#2S0{#JRx5<a%TwS1n,KxS1o=<acS1p5aaP?PaQ12Q0?#JS0?'KS1qQ1o5<aS1rP?Pa%TgS1s,KxS1tQ125<aS1uP?PaQ0qP?PaPaQ12=<abS1vPaPbQ1q%T1S1w61`8DnS1qP?Q0`Q0s5aaS0sCUFVFVP@PEb6b7b8X18X28X98X:8XA8XI8Q0t/1;10;w;g:10<;S0`10CwS1x'110DgS1y/1;Q15PDP<P<10DQ/l1C9S1z1G;CS1{10CDS1|;g;[[[[[^18^28^98^:8^A8^I8P7PzQ18#6S1}PsQ0DP5p+01CS1~PCQ0[PVPHP2O;b5b<b=b>b4b3PpPHPXPZPOP]P^PYPTP[P\PKQ0lQ0j/]_']PGQ0n?EDjP9%tDS0l9EjDP:Q1mPDPjP=Q0oDQDQP`PaQ1pQ0b=<ax5aaP?PaQ1rP?PaQ1uP?PaQ1W#J9calS1WP?PaQ1qP?Q0cCUFVFVP@PEb6b7b8X18X28X98X:8XA8XI8XN8Q1x/1:?g9CQ0`10Dw'110QgS0`/1;%?QS0cQ1zQ1{?gD;[[[[[^18^28^98^:8^A8^I8^N8P7PzP5Q1}PsQ01Q02Q1~PQQ0[PVPHP2O<b5b<b=b>b4b3O2H02b]WdW_P:P7O2n2001000000121000000W0W[P:P7O2n2001000000121000000X0~WMP:P7O2n2001000000121000000W0WGP:P7O2n2001000000121000000b0WcWZP:P7O2n2001000000121000000W0WYP:P7O2n2001000000121000000bJWbWTP:P7O2n2001000000121000000W0XFAP:P7O2n2001000000121102000W0XO8P:P7O2n2001000000121102000W0P7O11p>{Q00P8Q0w%@:S02Q17Q17Q1=#@S1=DNXFA-0:AXO8Q19P7Q0wQ02PrPrQ1=DNXFA-0:AQ00PAQ1<%@9PsPsQ1:#@DNXFAQ1;P7Q16%@<Q1>Q1>Q1R#@DNP3Q1Q%@;PuPuQ0V#@C9Q1@P7Q1K%@QPvPvQ1D#@C9Q1EQ1ZP3Q0WQ1[Q1AP7Q1\Q1]P3Q1LQ1^Q1_P7Q1`Q1aQ1hQ1iPFQ1NPzPwQ1CI0SQ0PP3Q1eQ1fQ1BP5PLQ1BPPQ1BE8P7Q1eQ1fP3Q1dP~Q1VP5PLQ1VPPQ1VE8P7Q1dP3Q1cQ0NfuS1BP5PLQ1BPPQ1BE8P7Q1cQ0NP3Q1bQ03fyS1NP5PLQ1NPPQ1NE8P7Q1bQ03PFfzS1iP{PdQ0fI1_%|d1Zdi9jdR9jdhQ1Y%6dS0f=I{e7\{40MP3%|21Z2h1Z2i9j2R3iQ1Y%62S1h=Ioe7\oQ18P1PIP1C_P7%|k1Zkh1Zki9jkR3iQ1Y%6{S18=Iqe7\qp+01@S1YQ08P3&1]MS08&1ZFS1_&1YFS1^&1XFS1L'4S1A'4S1[Q17#6S0W/P1:0Ft1P7Q08Q1[P3Q1_Q1A1Fp1S1Z%6tRM<0h1P7Q1_Q1AP3Q1^Q1L1FB1S1E%6pS1D<0h1P7Q1^Q1LP3&1WF-0K6S1@&1RF-0KWS0VQ0r#A&1QF+0K&1OF-0KN'4S1Q%M7R6#|1Z6i9j6R9j6h%37Rp%M:Re#DR2#y7^7P:PzP2P7Cf&0@7S1RPFPePWCe40?XL8#w40MXg}Re>1N}>R221M}>20f}>#DQ0@#A%|71Z7h1Z7i9j7R3iS0@20eF:S16$0d$1K#D21J69Xg}>1H}>-0f}#D'=[^FAQ0@Q16$1GQ0{#A,oNg03F5&1FF'l'>'1[^FA'4H1DS0@'4S0{'4S16'4S1;Q1M%6BS1:/F1S1<#~80F1P7Q1@Q1;P3Q0VQ16Q1GP1Q1MP1C_P7Q0VQ16P3Q1QQ0{Q1UP1Q1GP1C_P7Q1QQ0{P3P2Q0@Q1TP1Q1UP1C_P7Q0@A5}7>PeP:O1[^k}R6\2P2\6B1C}e>P:fvfr'CR}Q1PJ1BPeP}O1P3fwR}Q1T'C#MRe#|1Zeh1Zei9jeR3iQ1gQ1O'CRe#MR>#DR6#y9^p7PePzP6P7CfQ1RPFP>PWCe40?XL8#wQ1gP1Q1OP1C_P7Q1NQ1B'C#MR>#|1Z>h1Z>i9j>R3if{R>/C}R}#MRR#DRi#y9^p7P}PzPiP7CfQ1RPFPRPWCe40?XL8#wQ00P8Q1g,CHRR#MRi#DR}#y9^p7PRPzP}P7CfQ1RPFPiPWCe40?XL8PHP1Q1gP1C_P7f~RiQ1i'CR}#MRR#DRh#y9^p7P}PzPhP7CfQ1RPFPRPWCe40?P3%3:S1RQ1Y/C>R>#MRR#DRh#y7^:P>PzPhP:Cf&0@:PFPRPWCe'4p+01ARRP1PHP1C_P7%3=p+01BRhf}'C#M#D#y7^=Q1~/CiR>Pz%M>R>#DP<Cf&0@<PFP>PWCe'4P3p+01DQ1Y'CR>Pz%M>R>#DP;Cf&0@;PFP>PWCep+01EP1PRP1C_P7p+01FRR/ChRhPz%Mh#DPDCf&0@QPFp+01GS1YQ1~'C#MPWCePFp+01nPzPwQ1CI0SQ0PP3Q1eQ1fp+01JRhP1PRP1C_P7Q1eQ1fP3Q1dP~p+01NP1PhP1C_P7Q1d%~7$01RhP31P9:20I9=S0P[S1C20I:91P=9R>[S1~20I=<\>B1A9:7S1iP:n2001000000120000000UXW8XJ8Q1C\h^W8^J8P7PzPJ1`zJ%3zQ0\Q0O#3[[PXPZPOP]P^PYPTP[P\PKP_PGPjP`%TJ00Ql-0`a-0baP@PEb6b7b8%~JQ1J[P7b5b<b=b>b4b3b@P9O420IJzQ00P81>7J,=zS00XQ8p+01TR>P1p+01PP1C_P7Q00p+01WS0\/P1p+01SS0O01=1S1gP8Q0O#DR}fH60azS1N1P71S1BXO8P81>:J107gS1O%D>R>Q0J$1@S0J,oNS1T'>S1P'0Q0[Q0A#AR61oN>Re'>S0A'>S1U'0/P1XQ8P3Q1CQ1~Q0P1P<=[Q1iP7n2001000000120000000VhXW8XJ8S1iQ1~\h^W8^J8S1~P71>9J/0gQ1P'0Q1U'0S1UP1PXPZPOP]P^PYPTP[P\PKP_PGPjP`Q1w00Ql-0`a-0baP@PEb6b7b8%~1Q1J[P7b5b<b=b>b4b3S1JP81>=J/0gp+01U#DRhQ1T'>'0fJS1T1oNhS1P,>6S0P'>'01>71S1C'=XQ8Q0B#AS0B/>9Q1X#AS1X'0Q0I#AS0I,oN,>>'0Q0[/>1/>e'0S0[&1<8R>00;>R>$0DS1G&0L>S1=Q1TQ1P&0D85O8S1P5O89O8h9O8=&0L8S1TQ05P7P:20J80R0%{J'W%{g+06Q0=-0J8S0=%{NRJQ0J$0_60\8'W+06Q0a-0J8Rh%{6S0aQ0>-0J8R>'W'W+06S0>Q0B#{/W0Q1X#{+06Q0=Q0I$0_:0\8J'W+06%{1RJ,Wh/W>+06/WJR>g00ncS0=Q0d21:W:S0Ig03G1-0;8&1I8+0;$0LRhP8Q04Q0>:0GW7B0GW7>H0^bj$0PdK0gbhbiQ1UQ0[/>1'=eH0]O4b0PzP7J0RQ1N/P1eQ0\PSJ0RP81oN},>6Q1BXQ8Q1iQ1~P7Q0AP1Q1JP8Q0PQ1C'=XQ81>1eReQ1GQ1=Q1PQ1TQ05P7P:Q0a/W0RN1WJ0/WJRJQ0=Q0dQ0IPhP8Q04B0GW7NB0GW7JH0^bj$0PdK0gbhbiQ0A1>e1'=eH0]O4b02196}Q0O$18%3}PXPZPOP]P^PYPTP[P\PKP_PGQ0eP`PaA<albReP?PeCUP@PEb6b7b8X18Q1R\p^18P7p+01Z#DPCO2b5b<b=b>b4b3c06:1T6}J0RQ1geH02WoZ078P:P7O2n2001000000121102000b^b0XM~W^P:P7O2n2001000000121000000W0WGP:P7O2n2001000000121000000b0WMWsP:P7O2n2001000000121000000W0WvP:P7O2n2001000000121000000W0XL8P:P7O2n2001000000121102000W0WGP:P7O2n2001000000121000000b0WdX`2P:P7O2n2001000000121000000W0W[P:P7O2n2011000000121000000W0WMP:P7O2n2011000000121000000W0WGP:P7O2n2011000000121000000W`W[P:P7O2n2001000000121000000W0WMP:P7O2n2001000000121000000W0WGP:P7O2n2001000000121000000b0WGWtP:P7O2n2001000000121000000b0Q0f/P1:0F{1P31Po1Q1h/P1PiP5PLPiPPPiE8P7Q17/P1Q18/P1PFQ06P5Q09Q07Q0:Q0;Pr%6oRoPXPZPOP]P^PYPTP[1`u1RF%3u%31RiQ1Z#3[[R3P\PK1`M1R2%3M%6uR6/F1#3\i[R}P_PGQ0]?E:jRpP`PaPaQ1s,KbPcP?A<abcRJELP@PEb6b7b8X18X28Q1O/1:11:9[^18^28P7P|PzP{O3b5b4b3b@bBbCbDbEPXPZPOP]P^PYPTP[PFP3P\PKP2P}P_PGQ0_P`Pa1KbcRWQ0bQ1n'K5<aRNP?PNCUP@PEb6b7b8X18X28X98109w9I7:Q0t10=w'1[^18^28^98P7PzP6P|PdO4b5b4b3b@bBbCbDbEPXPZPOP]P^PYPTP[PFP3P\PKP2P}P_PGQ0eP`PaPa20ElbP?PeI0<P@PEb6b7b8X18%?7Q1R[^18P7P6PfO2b5b4b3b@bBbCbDbEN<1U%@r1Yo1617PPsQ1}P9P:H1VQ1},0s#@%@sQ1}/Y1'0'=PtP1Q0W00A1RoQ0W#3%6rR6/Y1R}#3\i[R2PXPZPOP]P^PYPTP[1`v1R3%3v1Fy1#3\i[RFP\PKQ1?#6Rd/`1RN%3d%6vRv/F1#3\i[RdQ0iQ1H'dRh$15/]_PGQ0xP<Q0o9Ej<P:PjP<Q0^P<PjDQDQP`PaQ0r#;#JR09calRSP?PaAcalxP?PaPaQ1s,K0R0PbP?PaQ0?9calR>P?PeCUELFVP@PEb6b7b8X18X28X98X:8Q0uQ15AI<g9Q15%3<[[[[^18^28^98^:8P7PvPzP5Q1IPVPIQ17Q1YO8b5b4b3b@bBbCbDbEbHPoP2PXPZPOP]P^PYPTP[P3PFP\PKPNPdP_PGPjP`Q1w9calP@PEb6b7b8%?1P7b5Rdb4b3b@bBbCbDbEbHH141Yt1#3%6qRN00A1RF%3N%6s/Y1#3\i[RsPXPZPOP]P^PYPTP[1`|1R3%3|Q1E#3\i[R2P\PK20AB1%3BfeRB/Y1#3\i[1`v1Ro%3v%6yRI/F1#3\i[RVP_PGPpP`PaPaPlPcP?1Kcb9<abELP@PEb6b7b8X18X28Q1R109:,1:[^18^28P71Y41Q0XPmO3b5b4b3b@bBbCbDbEbHbeb0Q0X%@t'1RtePtQ1>/0NRNP1PUPFPsPXPZPOP]P^PYPTP[P3P2P\PKQ1D/`1RtQ1D#3%6|R|/F1#3\i[RpPdb4b3b@bBbCbDbEbHPFPsP^PYPTP[PXPZPOP]P3P2P\PKPtPpQ1k/uh/]_PGQ0^P9Q0n9Ej;P:Q0oP;PjP;PjDQDQP`PaPaQ1oQ11P?PaQ0qP?PaQ1o9<aWP?PaPaQ1tPbP?PaPaQ11Q0yQ0L$0X60W8P?PaQ1WP?Q1wQ0z61389<aWCUELELFVELP@PEb6b7b8X18X28X98X:8XA8AI<w9Q0uQ1x9I9=Q1y/1=Q0M,1CQ0cQ1|1>1U'1[[[[[[^18^28^98^:8^A8P7PzP5Q0EP|PBfFPkP{PqQ1Vp+01HO;b5b4b3b@bBbCbDbEbHI1[1YN1/1U20A61Rq%361YM1#3\i[RMP^PYPTP[PXPZPOP]1`y1R6%3yQ1I/F1#3\i[RyP\PKQ1I/0vRv00A1%3v104IRv/Y1#3\i[1`|1%3|Q1<#3\i[P_PGQ0eP`PaPaPbQ0zP?Q10,KbQ145<aELP@PEb6b7b8X18117UQ0~Q135I:[^18P7Q1MQ1:'0/Y1PmO2b5b4b3b@bBbCbDbEbHbeb0%@NQ01'1RNePNPRP5PLPRChRL1sPRPqPMPXPZPOP]P^PYPTP[P6PyP\PKPoPVQ0h#b#bRN#kQ0g'u%bN#kQ1lQ0k'd'u/]_']PGQ0nQ0l7EQP9PjP:PjPQ%tQRNP=Q1m?E<jDQDQP`PaPaQ0?Q14P?PaPaQ10Q12P?PaPaQ0K#JRU-0ElP?PaPSP?PaQ1s,KUQ0r#2#J5<aP?PaQ0pQ1S5<aQ14=<ac5aaP?PaQ0qP?PaPaQ1vPaPbQ0?DnP?Q0sCUFVFVI0<ELELP@PEb6b7b8X18X28X98X:8XA8XI8XN8XV8Q13,1<Q0~/1<%?DRU%?mAIngmQ1|Q0}'1Q13;gCPmPDPDQ1FC9AInmQ:0NQn[\U[[[[[[^18^28^98^:8^A8^I8^N8^V8P7PIP4Pz%@vRv%@4RUQ0DP5p+01ORgPnPmPfP{PrPHp+01IRHPuO@b5b4b3b@bBbCbDbEbHPLePP%@uP}PRP=PqPMPXPZPOP]P^PYPTP[P6PyP\PKPoPVQ1jQ0m'u/]_PGQ0n?EQjP9Q0l9EjQP:PjPQQ1mP=AEj<NDQDQP`PaPaQ12Q0b,KbRb+0QP?PaPSP?PaQ0|#J9calP?PaPaP0PxP?PaP>P?PaPaPJPaPcQ12DnP?PaPJPaPcPbDnFVELFVI0<P@PEb6b7b8X18X28X98X:8XA8XI8XN8XV81079,==%?C%?nQ0`/1nQ0cP;PCPCPQC9Q0v10CQ7^D[[[[[[^18^28^98^:8^A8^I8^N8^V8P7PIP4PzP5Pv1YI1PgPUQ1FPfP{PrPHPuO>b5b4b3b@bBbCbDbEbHJ0lH02b0c03bRbnWuWaP:P7O2n2001000000121000000baWMW_P:P7O2n2001000000121000000W0WqP:P7O2n2001000000121000000X0~WGP:P7O2n2001000000121000000W0WpP:P7O2n2001000000121000000b0b]WcWZP:P7O2n2001000000121000000W0WYP:P7O2n2001000000121000000bJWbWTP:P7O2n2001000000121000000W0XFAP:P7O2n2001000000121102000W0XO8P:P7O2n2001000000121102000W0P7O1n200100000021100011000WXP7O1n200100000021100011000WXP7O1n200100000021100011000WXP7O1n200100000021100011000bmY05Y04P:P7O2n2001000000121000000b0WGW~P:P7O2n2001000000121000000W0W}P:P7O2n2001000000121000000W0W|P:P7O2n2001000000121000000W0W{P:P7O2n2001000000121000000W0WzP:P7O2n2001000000121000000b0brWxXk8o"). Qed.
End Client.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BPre.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo P : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis Hn : 64512 < n <= 0x8000000.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv asegs mX.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis Htrl : (1 <= length tr <= 9)%nat.
Hypothesis TRC : trc_cells B tr mX tb.
Hypothesis AFC : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0.
Hypothesis HG : sgrant_ok Σ P (smsz n).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation msz := (smsz n).
#[local] Notation SZ := (needed2 n).

Definition bpre (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (mA : mem),
    ms = nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -192)) - 96)) gp (Z_to_bv 64 tpA)
                       t0' t1' t2' a6' (sa_msz SZ) (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 8)
                       (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                     F (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom asegs))
              (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])
    /\ ART_A Σ mA /\ mem_inv asegs mA /\ wmono asegs mX mA
    /\ (forall a : word, aclient (live Σ) (frames Σ) (B + -16) (bv_unsigned a) -> mA a = mX a)
    /\ vis_rep (lay Σ) (shw P n :: rtA_allow Σ) mA
    /\ rw_cells asegs mA (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 8);
                                      C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x4618c)]
    /\ sa_frame mA (Z_to_bv 64 (B + -192)) (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 SZ)
         (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
    /\ mod_frame mA (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -192)) - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
         (Z_to_bv 64 (sa_msz SZ))
    /\ stk asegs mA lo (bv_unsigned (Z_to_bv 64 (B + -192)) - 144)
    /\ mm_gcells mA /\ sec_page mA /\ name_cells mA
    /\ af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mA j0 /\ trc_cells B tr mA tb.

Lemma bp_pre : forall ms, fA Σ PMc mX B gp F fc n lo P ms -> bpre ms.
Proof using Hn HA MI LOW LOR SPT Htrl TRC AFC HG.
  intros ms (ms0 & mo & (HM & _) & (ms1 & (m1 & MU1 & WM1 & FR1 & HA1) & E0) & HRev & HH0 & HH1).
  destruct HA1 as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1e & E1 & MU2 & WM2 & MI2 & SAF & MODF & ST2 & MM2 & PG2 & NM2).
  pose proof (rv_map Σ mX P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof (smsz_sa n Hn) as (Z1 & Z2 & Z3).
  assert (RS : 0 <= B + -192 < 2 ^ 64) by (unfold l_ACEIL, USTACK_TOP in *; lia).
  rewrite unsigned_lit in MU2 by exact RS.
  assert (Hsp1 : rtA_sp0 Σ - STACK_WIN <= B + -608) by (unfold l_ACEIL, rtA_sp0 in *; lia).
  assert (MUC : munch (W_client Σ (B + -608)) mX m1e).
  { apply (munch_trans _ mX m1 m1e).
    - eapply (munch_weaken _ _ mX m1); [|exact MU1]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I].
    - eapply (munch_weaken _ _ m1 m1e); [|exact MU2]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I]. }
  pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WMe.
  pose proof (ART_transport _ Σ mX m1e HA MUC WMe (art_avoid_client Σ mX (B + -608) HA Hsp1)) as ART1.
  assert (E0m : ms_mem ms0 = apply_zeros m1e [(Z_to_bv 64 P, Z_to_bv 64 msz)]) by (rewrite E0, nretA_mem_zeros, E1; reflexivity).
  pose proof (zeros_munch m1e P msz ltac:(lia) ltac:(lia) ltac:(lia)) as MU3. rewrite <- E0m in MU3.
  pose proof (zeros_wmono m1e [(Z_to_bv 64 P, Z_to_bv 64 msz)]) as WM3. rewrite <- E0m in WM3.
  pose proof (ART_transport _ Σ m1e (ms_mem ms0) ART1 MU3 WM3 (mp_avoid Σ m1e P n ART1 HG Hn)) as ART0.
  pose proof (reveal_munch (rtA_allow Σ) [shw P n] mo ms0 ms HRev HH0 HH1 (W_rev Σ P n) (rev_munch_hyp Σ (ms_mem ms0) P n ART0 HG Hn)) as MU4.
  pose proof (reveal_wmono (rtA_allow Σ) [shw P n] mo ms0 ms HRev HH0) as WM4.
  pose proof (ART_transport _ Σ (ms_mem ms0) (ms_mem ms) ART0 MU4 WM4 (rev_avoid Σ (ms_mem ms0) P n ART0 HG Hn)) as ARTA.
  pose proof (ART_wf Σ mX HA) as (HL & _).
  assert (E5 : ms = nretA (set_mem ms1 (ms_mem ms)) (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 msz)]))
    by (apply (nret_revealed (rtA_allow Σ) (shw P n :: rtA_allow Σ) mo ms0 ms1 ms P msz ltac:(lia) ltac:(lia) ltac:(lia) E0 HRev);
        intros a Ha; exact (map_range_visible Σ P n mo a HL HM HG Ha)).
  assert (TR : forall a cs, rw_cells asegs m1e a cs -> (a + Z.of_nat (cells_size cs) <= P \/ P + msz <= a) ->
            (a + Z.of_nat (cells_size cs) <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) -> rw_cells asegs (ms_mem ms) a cs).
  { intros a cs X D1 D2. apply (rw_cells_transport asegs _ (ms_mem ms0) _ _ _ (rw_cells_transport asegs _ m1e _ _ _ X MU3 WM3
      ltac:(cbn [disjoint_from]; split; [lia | exact I])) MU4 WM4). exact (rv_app Σ (ms_mem ms0) P n ART0 HG Hn _ _ D2). }
  pose proof (fk_aceil Σ (geo_of_ART Σ mX HA)) as (X1 & X2).
  assert (SP : K_HIGH_SHADOW_hi <= B + -608 /\ P + msz <= B + -608) by (unfold K_HIGH_SHADOW_hi, SHB in *; lia).
  assert (M5' : 0x66f000 <= P) by exact M5.
  exists t0', t1', t2', a6', t3', t4', t5', t6', (ms_mem ms). split.
  { rewrite E5 at 1. rewrite E1, <- Z2. reflexivity. }
  split; [exact ARTA|].
  split; [apply (reveal_mem_inv (rtA_allow Σ) (shw P n :: rtA_allow Σ) mo ms0 ms HRev HH0 HH1); rewrite E0m;
          apply zeros_mem_inv; [exact MI2 | exact M5 | lia | lia]|].
  split; [exact (wmono_trans asegs _ _ _ WMe (wmono_trans asegs _ _ _ WM3 WM4))|].
  split.
  { intros a Ha. destruct (cl_outside Σ mX P n (B + -16) HA HG Hn ltac:(lia) _ Ha) as (Y1 & Y2).
    rewrite (MU4 a Y2). rewrite (MU3 a ltac:(cbn [outside]; split; [lia | exact I])).
    destruct (aclient_split Σ mX (B + -16) _ HA Ha) as [Y|Y].
    - rewrite (MU2 a ltac:(cbn [outside]; split; [lia | exact I])). apply MU1. cbn [outside]. split; [lia | exact I].
    - rewrite (MU2 a ltac:(cbn [outside]; split; [lia | exact I])). apply MU1. cbn [outside]. split; [lia | exact I]. }
  split.
  { pose proof HM as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & SL & _)).
    exact (vis_rep_reveal (rtA_allow Σ) [shw P n] mo ms0 ms HRev (lay Σ) SL (ART_vis Σ (ms_mem ms0) ART0)). }
  split.
  { apply TR; [|cs_size; lia | cs_size; lia]. apply (rw_cells_transport asegs _ m1 m1e _ _ FR1 MU2 WM2). cs_size.
    cbn [disjoint_from]. split; [lia | exact I]. }
  split; [destruct SAF as (j & SAF); exists j; apply TR; [exact SAF | rewrite unsigned_lit by exact RS; cs_size; lia
                                                          | rewrite unsigned_lit by exact RS; cs_size; lia]|].
  split; [destruct MODF as (j & MODF); exists j; apply TR; [exact MODF | rewrite (unsigned_lit (B + -192)) by exact RS;
             rewrite unsigned_lit by lia; cs_size; lia | rewrite (unsigned_lit (B + -192)) by exact RS; rewrite unsigned_lit by lia; cs_size; lia]|].
  split; [exact (stk_wmono _ _ _ _ (stk_wmono _ _ _ _ ST2 WM3) WM4)|].
  split.
  { unfold mm_gcells in *. destruct MM2 as (G1 & G2 & G3 & G4 & G5).
    split; [apply TR; [exact G1 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G2 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G3 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G4 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    apply TR; [exact G5 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]. }
  split; [unfold sec_page in *; apply TR; [exact PG2 | cs_size; unfold i_sec_page, INST, g_instance, SEGTOP_A in *; lia
                                           | cs_size; unfold i_sec_page, INST, g_instance, K_LOW_SHADOW_lo; lia]|].
  split; [unfold name_cells in *; destruct NM2 as (N1 & N2); split; [apply TR; [exact N1 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]
                                                                   | apply TR; [exact N2 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]]|].
  assert (D4 : forall a k, K_HIGH_SHADOW_hi <= a -> disjoint_from (W_rev Σ P n) a k)
    by (intros a k H; exact (rv_app Σ (ms_mem ms0) P n ART0 HG Hn _ _ (or_intror H))).
  split.
  { pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ mX m1 j0 AFC MU1 WM1
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF1.
    pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m1 m1e j0 AF1 MU2 WM2
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF2.
    pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m1e (ms_mem ms0) j0 AF2 MU3 WM3
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF3.
    exact (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ (ms_mem ms0) (ms_mem ms) j0 AF3 MU4 WM4
             (D4 (B + -144) 128 ltac:(lia))). }
  destruct TRC as (T1 & T2 & T3). split; [|split; [|exact T3]].
  - pose proof (rw_cells_transport asegs _ mX _ _ _ T1 MU1 WM1 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X.
    pose proof (rw_cells_transport asegs _ m1 _ _ _ X MU2 WM2 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X'.
    pose proof (rw_cells_transport asegs _ m1e _ _ _ X' MU3 WM3 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X''.
    exact (rw_cells_transport asegs _ (ms_mem ms0) _ _ _ X'' MU4 WM4 (D4 B _ ltac:(lia))).
  - pose proof (u64arr_transport asegs _ mX _ _ _ T2 MU1 WM1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X.
    pose proof (u64arr_transport asegs _ m1 _ _ _ X MU2 WM2 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X'.
    pose proof (u64arr_transport asegs _ m1e _ _ _ X' MU3 WM3 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X''.
    exact (u64arr_transport asegs _ (ms_mem ms0) _ _ _ X'' MU4 WM4 (D4 (B + 16) _ ltac:(lia))).
Qed.
End BPre.
