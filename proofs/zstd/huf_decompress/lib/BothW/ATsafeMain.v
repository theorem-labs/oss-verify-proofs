(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra MainExport MainFactsBoth BothEntry.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Stdio Harness Adapter Driver ProgA
  AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal AsanOK RSimProg BothHandoff Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ATsafeMain () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z6of_natc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5NMAXZI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4NMAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8allow_ofC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8aallowedc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5Ahandc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain9win_pagesK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth8asan_visC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv9RESERVE34c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain6NMAX_ZC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl@K_PTRARR_RESERVEC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4UWINC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4FWINC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:length_appI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z4succK47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z7inj_addC47Corelib4Init9Datatypes3appK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K5ARocqVerifyHarness?AgentSubmission4Spec5ProgA6AAlloc01I5ARocqVerifyHarness?AgentSubmission4Spec6Driver7IOStyle00C5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore8TS_ebindC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore4preTC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore3TSMC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAlloc9shad_div8K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl8K_REGIONC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_OFFC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff?placement_factsC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_space_beg0C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7PRIM_SZC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6PTR_SZC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<K_SPACE_SIZEC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_ptr_array0C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff@space_beg0_factsC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z7mod_mulI47Corelib4Init5Logic2ex00c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain9cls_pagesC47Corelib5Lists7ListDef3seqC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore;range_pagesC46Stdlib5Lists4List;in_flat_mapC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2ex01C46Stdlib5Lists4List9in_or_appC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAlloc;shad_boundsc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain8shad_clsC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore@range_pages_specc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain6A0_clsC5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAlloc5shad8c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain2A0c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain3HSBc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain3HPAc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain:shlen_valsc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5SB_alc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5PA_alC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCoreBrange_pages_lengthC46Stdlib5Lists4List:length_seqC57Corelib7BinNums6PosDef3Pos3mulC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClassesCPreOrder_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMainBflat_map_length_leC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_mult_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain9CLS_PAGESC47Corelib7Program6Basics4implC56Stdlib6ZArith6BinInt1Z;le_preorderC5ARocqVerifyHarness?AgentSubmission2AS:MainExport6ivz_wfC5ARocqVerifyHarness?AgentSubmission2AS:MainExport9ivz_bytesC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore6aunionC5ARocqVerifyHarness?AgentSubmission2AS:MainExport<aallowed_finI46Stdlib5Lists4List5NoDup00C5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore4abudC56Stdlib6ZArith6BinInt1Z;div_le_monoC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore:abud_unionC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore9abud_monoC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth;asan_abytesc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain@win_pages_lengthc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain2K0I5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7amodelL00C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry<amL_allow_wfC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry:amL_abytesc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain;A0_abud_genC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission2AS9BothEntry6amodel00C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry;am_allow_wfC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry9am_abytesC56Stdlib6ZArith6BinInt1Z7div_posC5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAllocApage_base_of_selfC46Stdlib5Lists4List:in_map_iffC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC46Stdlib5Lists4List8map_consC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps7JJ_acctc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4HRESC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps7JJ_permC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps9JJ_creditC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps9JJ_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps5JJ_ioC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps5JJ_soc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain8ABASE_SHC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps8U_mallocC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps6U_freeC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps7U_annotI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore5postMC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3AStc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain1Jc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain6J_acctC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore8TSM_munrC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<new_handlerAI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00I47Corelib4Init9Datatypes9Empty_set00C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg9s_emit_okC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4a_soC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA8a_set_soC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA3ioAC5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_emitC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg3TSJc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4J_ioc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4J_soC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA7amallocC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA5afreeC5ARocqVerifyHarness?AgentSubmission4Spec7Harness8fuzz_oneC5ARocqVerifyHarness?AgentSubmission4Spec7Adapter:target_runC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4runAC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg=target_run_okc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain6J_permc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain8J_creditc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain2Jmc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain2Jfc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5JemitC5ARocqVerifyHarness?AgentSubmission4Spec6Driver9MAX_INPUTC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg8RUN_COSTC5ARocqVerifyHarness?AgentSubmission4Spec8RSimProg7RUN_OPSC5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_diagC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg9s_diag_okI5ARocqVerifyHarness?AgentSubmission4Spec6Driver8diag_msg00C5ARocqVerifyHarness?AgentSubmission4Spec6Driver7io_exitC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProgDstdout_exit_flush_okC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA;alloc_initAC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg7TSJ_retC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA<alloc_countAC5ARocqVerifyHarness?AgentSubmission4Spec6Driver:main_modelC5ARocqVerifyHarness?AgentSubmission4Spec6Driver:exit_modelC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA:progA_mainC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg<main_exit_okc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5Jdiagc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain5Jinitc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain6Jcountc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4Jrunc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain7JioexitC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeProg9MAIN_COSTC5ARocqVerifyHarness?AgentSubmission4Spec8RSimProg8MAIN_OPSC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9AI_init_LC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7resv_ofC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7atop_ofC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_initC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX2MXC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK2AIC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF5fp_okC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_atopC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_ptr_arrayC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nextC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission5BothW8ATsafeEv3QOKC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA6alw_leC5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAlloc2GAC5ARocqVerifyHarness?AgentSubmission5BothW9ATsafeOps5pcredC5ARocqVerifyHarness?AgentSubmission5BothW8ATsafeEv8chunk_okI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5ainitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv:all_chunksC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff@all_chunks_ainitC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA;alw_le_reflC5ARocqVerifyHarness?AgentSubmission5BothW;ATsafeAlloc6GA_nilc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain9A0_abud_LC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7LIMIT34I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA8init_fdsc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4VMAXc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4WMAXC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4NOPSI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00C4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC5ARocqVerifyHarness?AgentSubmission4Spec4Prog6argv_ZC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA:progA_treeC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore2EQI5ARocqVerifyHarness?AgentSubmission3Lib5ITree5itree00C47Corelib4Init9Datatypes3sndc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain8J_init_Lc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain=progA_main_okC5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA7acct_okC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore2TSK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeCore9TS_tsafeAI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA3alwI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry>amodel_amodelLc5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain=progA_tsafe_LC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5LIMITC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv@LIMIT34_le_LIMITC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8LIMIT_eqC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff6a_usp0c5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain;progA_tsafeI5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_facts".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition VMAX : Z := MAIN_COST.
Definition WMAX : Z := NOPS.

(* [comment removed for export] *)
Definition cls_pages (SB : Z) (c : Z) : list word :=
  range_pages (shad (SB + c * K_REGION) - 4096) (UWIN / 8 + 8192)
  ++ range_pages (shad (SB + c * K_REGION + K_FREEARR_OFF)) (FWIN / 8)
  ++ map (fun i => Z_to_bv 64 (shad (SB + c * K_REGION) + 32768 * Z.of_nat i)) (seq 0 (Z.to_nat 14337)).
Definition CLS_PAGES : Z := 19975.   (* [comment removed for export] *)

Definition win_pages (V : nat -> Z) : list word :=
  flat_map (fun c => cls_pages (a_space_beg0 V) (Z.of_nat c)) (seq 1 31)
  ++ range_pages (shad (a_ptr_array0 V)) (shlen K_PTRARR_RESERVE).

(* [comment removed for export] *)
Definition K0 : Z := 600959 + 31 * CLS_PAGES + (2^8 + 2).
Definition NMAXZ : Z := K0 + pcred VMAX WMAX.
Definition NMAX : nat := Z.to_nat NMAXZ.

Lemma NMAX_Z : Z.of_nat NMAX = NMAXZ.
Proof using Type. unfold NMAX. apply Z2Nat.id. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition Ahand (V : nat -> Z) : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of ASHOFF V asan_vis) p.

Definition A0 (V : nat -> Z) : alw := aunion (Ahand V) (win_pages V).

Theorem A0_init : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.
Proof using Type. intros V p Hal Ha. left. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma HRES : Z.of_nat NMAX * 4096 <= RESERVE34.
Proof using Type. rewrite NMAX_Z. vm_compute. discriminate. Qed.

Lemma shlen_vals : shlen K_PTRARR_RESERVE = 2^20 /\ UWIN / 8 + 8192 = 18882560 /\ FWIN / 8 = 4194304.
Proof using Type. repeat split; reflexivity. Qed.

Lemma flat_map_length_le : forall {A B} (f : A -> list B) (l : list A) (b : Z),
  (forall x, In x l -> Z.of_nat (length (f x)) <= b) -> Z.of_nat (length (flat_map f l)) <= Z.of_nat (length l) * b.
Proof using Type.
  intros A B f l b H. induction l as [|x l IH]; cbn [flat_map length]; [lia|]. rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ.
  specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). pose proof (H x (or_introl eq_refl)). lia.
Qed.

Lemma shad_cls : forall SB c, SB mod 4096 = 0 -> shad (SB + c * K_REGION) = shad SB + c * 536870912
  /\ shad (SB + c * K_REGION + K_FREEARR_OFF) = shad SB + c * 536870912 + 469762048
  /\ shad (SB + c * K_REGION + UWIN) = shad SB + c * 536870912 + UWIN / 8
  /\ shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN) = shad SB + c * 536870912 + 469762048 + FWIN / 8.
Proof using rc.
  intros SB c HSB. rewrite !(shad_div8 0%nat). unfold K_REGION, K_FREEARR_OFF, UWIN, FWIN.
  pose proof (Z.div_mod SB 4096 ltac:(lia)). repeat split; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
Qed.

Section V.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  (* [comment removed for export] *)
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  Lemma HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_space_beg0, K_SPACE_SIZE, PRIM_SZ, a_usp0 in *. lia. Qed.

  Lemma HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_ptr_array0, K_PTRARR_RESERVE, PTR_SZ, a_usp0 in *. lia. Qed.

  Lemma SB_al : SB mod 4096 = 0.
Proof. pose proof (space_beg0_facts V HP) as (H1 & _). apply (Z.mod_divide _ 65536) in H1; [|lia]. destruct H1 as [q Hq]. rewrite Hq.
         replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. Qed.

  Lemma PA_al : PA mod 4096 = 0.
Proof. pose proof (space_beg0_facts V HP) as (_ & _ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma A0_cls : forall c p, 1 <= c <= 31 -> In p (cls_pages SB c) -> A0 V p.
Proof using rc.
    intros c p Hc Hp. right. unfold win_pages. apply in_or_app. left. apply in_flat_map. exists (Z.to_nat c).
    split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. exact Hp.
  Qed.

  (* [comment removed for export] *)
  Lemma ABASE_SH : forall z',
    ((exists c, 1 <= c <= 31 /\
        (shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN)
         \/ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN)))
     \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 V (page_base_of z').
Proof using rc HP HAT.
    intros z' Hz. pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as (E1 & E2 & E3).
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    destruct Hz as [(c & Hc & Hz)|Hz].
    - pose proof (shad_cls SB c SB_al) as (C1 & C2 & C3 & C4).
      assert (Hc29 : 0 <= c * 536870912 <= 31 * 536870912) by nia.
      apply (A0_cls c); [exact Hc|]. unfold cls_pages. apply in_or_app.
      destruct Hz as [Hz|Hz]; [left| right; apply in_or_app; left]; apply range_pages_spec; lia.
    - right. unfold win_pages. apply in_or_app. right. apply range_pages_spec; [lia|].
      rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al) in Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma win_pages_length : Z.of_nat (length (win_pages V)) <= 31 * CLS_PAGES + (2^8 + 2).
Proof using rc HP HAT.
    pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as (E1 & E2 & E3).
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    unfold win_pages. rewrite length_app, Nat2Z.inj_add.
    pose proof (range_pages_length (shad PA) (shlen K_PTRARR_RESERVE) ltac:(lia) ltac:(rewrite E1; lia)) as LP. rewrite E1 in LP |- *. change (2^20 / 4096) with (2^8) in LP.
    assert (LC : Z.of_nat (length (flat_map (fun c => cls_pages SB (Z.of_nat c)) (seq 1 31))) <= 31 * 19975).
    { replace 31 with (Z.of_nat (length (seq 1 31))) at 1 by (rewrite length_seq; reflexivity).
      apply flat_map_length_le. intros x Hx. apply in_seq in Hx.
      pose proof (shad_cls SB (Z.of_nat x) SB_al) as (C1 & C2 & C3 & C4).
      assert (Hc29 : 0 <= Z.of_nat x * 536870912 <= 31 * 536870912) by nia.
      unfold cls_pages. rewrite !length_app, length_map, length_seq, !Nat2Z.inj_add. rewrite ?Z2Nat.id by lia.
      pose proof (range_pages_length (shad (SB + Z.of_nat x * K_REGION) - 4096) (UWIN / 8 + 8192) ltac:(lia) ltac:(lia)) as L1.
      pose proof (range_pages_length (shad (SB + Z.of_nat x * K_REGION + K_FREEARR_OFF)) (FWIN / 8) ltac:(lia) ltac:(lia)) as L2.
      rewrite E2 in L1 |- *. rewrite E3 in L2 |- *. change (18882560 / 4096) with 4610 in L1. change (4194304 / 4096) with 1024 in L2. lia. }
    unfold CLS_PAGES. lia.
  Qed.

  Lemma A0_abud_gen : ivz_wf (allow_of ASHOFF V asan_vis) -> ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes -> abud (A0 V) K0.
Proof.
    intros HWF AB. unfold A0, K0.
    apply (abud_mono _ (600959 + Z.of_nat (length (win_pages V)))); [apply abud_union| pose proof win_pages_length; lia].
    destruct (aallowed_fin (allow_of ASHOFF V asan_vis) HWF) as (L & ND & HLL & HIN).
    exists L. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
    unfold asan_abytes in AB. change BothEntry.ASHOFF with ASHOFF in AB.
    pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB) as AB'. change (2460838912 / 4096) with 600790 in AB'. lia.
  Qed.

  Lemma A0_abud_L : forall lim sp fs mo, amodelL lim V sp fs mo -> abud (A0 V) K0.
Proof using rc HP HAT. intros lim sp fs mo HM. apply A0_abud_gen; [exact (amL_allow_wf _ _ _ _ _ HM)| exact (amL_abytes _ _ _ _ _ HM)]. Qed.

  Lemma A0_abud : forall sp fs mo, amodel V sp fs mo -> abud (A0 V) K0.
Proof using rc HP HAT. intros sp fs mo HM. apply A0_abud_gen; [exact (am_allow_wf _ _ _ _ HM)| exact (am_abytes _ _ _ _ HM)]. Qed.
End V.

(* [comment removed for export] *)
Theorem A0_lat : forall V (p : word) (c k : Z), 0 <= a_space_beg0 V -> a_space_beg0 V mod 4096 = 0 ->
  bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
  (bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c - 4096
   \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c + 32768 * k)) -> A0 V p.
Proof using rc.
  intros V p c k S0 SAL Hal Hc Hp. pose proof shlen_vals as (E1 & E2 & E3).
  pose proof (shad_cls (a_space_beg0 V) c SAL) as (C1 & C2 & C3 & C4).
  assert (SH1 : 2147450880 <= shad (a_space_beg0 V)).
  { rewrite (shad_div8 0%nat). pose proof (Z.div_pos (a_space_beg0 V) 8 S0 ltac:(lia)). lia. }
  assert (Hc29 : 536870912 <= c * 536870912 <= 31 * 536870912) by nia.
  apply (A0_cls V c); [lia|]. unfold cls_pages. apply in_or_app. destruct Hp as [Hp|[Hk Hp]].
  - left. rewrite <- (page_base_of_self 0%nat p Hal). apply range_pages_spec; lia.
  - right. apply in_or_app. right. apply in_map_iff. exists (Z.to_nat k). split; [| apply in_seq; lia].
    rewrite Z2Nat.id by lia. rewrite C1. replace (shad (a_space_beg0 V) + c * 536870912 + 32768 * k) with (bv_unsigned p) by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Variable sp : word.                          (* [comment removed for export] *)
  Hypothesis HSP : atop_of sp = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  (* [comment removed for export] *)
  Definition J : list (AsanCtrl.aptr * Z) -> Z -> Z -> preT (St:=APS) := JJ NMAX SB PA (A0 V).

  Lemma J_acct : forall Y v w RNG A s mo, J Y v w RNG A s mo -> acct_ok NMAX RNG A mo.
Proof using Type. exact (JJ_acct NMAX SB PA (A0 V) HRES). Qed.
  Lemma J_perm : forall Y Y' v w RNG A s mo, Permutation Y Y' -> J Y v w RNG A s mo -> J Y' v w RNG A s mo.
Proof using Type. exact (JJ_perm NMAX SB PA (A0 V)). Qed.
  Lemma J_credit : forall Y v w v' w' RNG A s mo, 0 <= v' <= v -> 0 <= w' <= w -> J Y v w RNG A s mo -> J Y v' w' RNG A s mo.
Proof using Type. exact (JJ_credit NMAX SB PA (A0 V)). Qed.
  Lemma J_nonneg : forall Y v w RNG A s mo, J Y v w RNG A s mo -> 0 <= v /\ 0 <= w.
Proof using Type. exact (JJ_nonneg NMAX SB PA (A0 V)). Qed.
  Lemma J_io : forall n Y v w RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> J Y v w RNG A s mo -> J Y v w RNG A s mo'.
Proof using HP HAT. exact (JJ_io NMAX SB PA (A0 V) (HSB V HP HAT) (HPA V HP HAT)). Qed.
  Lemma J_so : forall Y v w RNG A s mo x, J Y v w RNG A s mo -> J Y v w RNG A (aset_so x s) mo.
Proof using Type. exact (JJ_so NMAX SB PA (A0 V)). Qed.

  Local Notation TSM := (TSM NMAX (St:=APS)).

  Lemma Jm : forall Y v w n, 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
    TSM (fun RNG A s mo => J Y v w RNG A s mo /\ n <= v /\ 1 <= w) (amalloc_M n)
        (fun r RNG A s mo => exists q, r = Some q /\ J ((q, n) :: Y) (v - n) (w - 1) RNG A s mo /\ n < 2^63).
Proof using HP HAT. exact (U_malloc NMAX SB PA (A0 V) HRES (ABASE_SH V HP HAT)). Qed.
  Lemma Jf : forall Y v w p n, TSM (J ((p, n) :: Y) v w) (afree_M p) (fun _ => J Y v w).
Proof using HP HAT. exact (U_free NMAX SB PA (A0 V) HRES (ABASE_SH V HP HAT)). Qed.
  Lemma Ja : forall Y v w q cap old new, In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
    TSM (J Y v w) (aannot_M q cap old new) (fun _ => J Y v w).
Proof using HP HAT. exact (U_annot NMAX SB PA (A0 V) HRES (ABASE_SH V HP HAT)). Qed.

  Ltac jx := first [ exact J_acct | exact J_perm | exact J_credit | exact J_nonneg | exact J_io | exact J_so | exact Jm | exact Jf ].

  Lemma Jnh : forall Y v w (Q : postM (St:=APS) Empty_set), TSM (J Y v w) (new_handlerA AAllocAsan) Q.
Proof using Type. intros Y v w Q. unfold new_handlerA. apply TSM_munr. apply J_acct. Qed.

  Lemma Jemit : forall Y v w z, TSJ NMAX J Y v w (io_emit (ioA AAllocAsan) z).
Proof using HP HAT. intros Y v w z. cbn [io_emit ioA io_S]. eapply s_emit_ok; jx. Qed.

  (* [comment removed for export] *)

  Lemma Jrun : forall X cfg payload v w, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v -> RUN_OPS <= w ->
    TSM (J X v w) (runA AAllocAsan cfg payload) (fun _ => J X (v - RUN_COST) (w - RUN_OPS)).
Proof using HP HAT.
    intros X cfg payload v w HX Hp Hv Hw. unfold runA, fuzz_oneA. cbn [amalloc afree AAllocAsan].
    eapply target_run_ok; try jx; first [apply Jnh| apply Jemit| exact HX| exact Hp| exact Hv| exact Hw].
  Qed.

  Lemma Jdiag : forall Y v w d, TSJ NMAX J Y v w (io_diag (ioA AAllocAsan) d).
Proof using HP HAT. intros. cbn [io_diag ioA io_S]. eapply s_diag_ok; jx. Qed.
  Lemma Jioexit : forall Y v w, TSJ NMAX J Y v w (io_exit (ioA AAllocAsan)).
Proof using HP HAT. intros. cbn [io_exit ioA io_S]. eapply stdout_exit_flush_ok; jx. Qed.
  Lemma Jinit : forall Y v w bm, TSJ NMAX J Y v w (alloc_initA AAllocAsan bm).
Proof using Type. intros. unfold alloc_initA, target_alloc_init. eapply TSJ_ret; jx. Qed.
  Lemma Jcount : forall Y v w, TSJ NMAX J Y v w (alloc_countA AAllocAsan).
Proof using Type. intros. unfold alloc_countA, target_alloc_count. eapply TSJ_ret; jx. Qed.

  (* [comment removed for export] *)
  Lemma progA_main_ok : forall rs argv v w (Q : postM (St:=APS) Empty_set), MAIN_COST <= v -> MAIN_OPS <= w ->
    TSM (J [] v w) (progA_main AAllocAsan rs argv) Q.
Proof using HP HAT.
    intros rs argv v w Q Hv Hw. unfold progA_main. cbn [amalloc afree aptr_addr AAllocAsan].
    eapply main_exit_ok; try jx; first [apply Jdiag| apply Jinit| apply Jcount| apply Jrun| apply Jioexit| exact Hv| exact Hw].
  Qed.

  (* [comment removed for export] *)
  Lemma J_init_L : forall lim fs mo, LIMIT34 <= lim -> amodelL lim V sp fs mo ->
    J [] VMAX WMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V) (aps_init SB PA (resv_of V) (atop_of sp)) (MX mo []).
Proof using HP HAT HSP.
    intros lim fs mo HL HM. destruct (AI_init_L lim V sp fs mo HL HM HP) as (HAI & _).
    unfold J, JJ. split; [exact HAI|]. split; [exact HSP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold VMAX, MAIN_COST, READ_COST, RUN_COST, FUZZ_COST, PRODUCER_SIZE, BUFF_MAX, MAX_INPUT; lia|].
    split; [unfold WMAX; cbn [aps_m aps_init a_next ainit Z.of_N]; unfold NOPS; lia|].
    exists [], K0. split; [unfold QOK; cbn [aps_m aps_init]; rewrite all_chunks_ainit; constructor|].
    split; [apply alw_le_refl|]. split; [apply GA_nil|]. split; [eapply A0_abud_L; [exact HP| exact HAT| exact HM]|].
    split; [unfold K0, CLS_PAGES; lia|]. rewrite NMAX_Z. unfold NMAXZ. lia.
  Qed.

  Theorem progA_tsafe_L : forall lim rs inp mo, LIMIT34 <= lim -> amodelL lim V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof using rc HP HAT HSP.
    intros lim rs inp mo HL HM.
    apply (TS_tsafeA NMAX _ _ _ _ (EQ (fun (_ : unit) _ _ _ => True))).
    unfold progA_tree. eapply TS_ebind.
    - exact (progA_main_ok rs (argv_Z (in_argv inp)) VMAX WMAX (fun _ _ _ _ _ => True) ltac:(unfold VMAX; lia) ltac:(unfold WMAX, NOPS, MAIN_OPS, READ_OPS, RUN_OPS, FUZZ_OPS; lia) _ _ _ _ (J_init_L _ _ _ HL HM)).
    - intros [[] s] RNG' A' mo' _ _.
  Qed.

  (* [comment removed for export] *)
  Theorem progA_tsafe : forall rs inp mo, amodel V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof using rc HP HAT HSP.
    intros rs inp mo HM. apply (progA_tsafe_L target_alloc_limit); [| apply amodel_amodelL; exact HM].
    rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
  Qed.
End Main.

(* [comment removed for export] *)
Corollary progA_tsafe_open : forall rs V sp inp mo,
  Forall (pfact_ok V) asan_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> amodel V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof using Type. intros rs V sp inp mo HP HAT HSP HM. exact (progA_tsafe V HP HAT sp HSP rs inp mo HM). Qed.

(* [comment removed for export] *)
Corollary progA_tsafe_open_L : forall lim rs V sp inp mo, LIMIT34 <= lim ->
  Forall (pfact_ok V) asan_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> amodelL lim V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof using Type. intros lim rs V sp inp mo HL HP HAT HSP HM. exact (progA_tsafe_L V HP HAT sp HSP lim rs inp mo HL HM). Qed.
End CANSEC1.
