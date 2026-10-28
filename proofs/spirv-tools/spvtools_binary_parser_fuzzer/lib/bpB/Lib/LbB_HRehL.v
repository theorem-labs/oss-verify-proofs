(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpD LbB_HEmpI LbB_HEmpR LbB_HRehK LbB_HRehD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_HRehL () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waK47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem>wr_at_store_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond05C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203I5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr00I47Corelib4Init9Datatypes3nat00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchI47Corelib4Init5Logic3and00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts8agree_onK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel3entC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes8list_indC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel4addrC47Corelib4Init5Logic3notI47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01I47Corelib4Init5Peano2le00K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_KitBword_to_le_bytes_1K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ARocqVerifyHarness?AgentSubmission8LibIface3memI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval24C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpR@bseq_next_factsEC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bseq_nextC56Stdlib6ZArith6BinInt1Z4landC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HFind;BSEQ_boundAC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4BSEQC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK8last_anyC4ELinuxProcessSemantics5Riscv7Prelude5bvmapi6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4LSTA00K4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC4ARocqVerifyHarness?AgentSubmission8PropExec4getrI47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes3appI46Stdlib7Sorting;Permutation;Permutation00I5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel4binv00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK7last_inC46Stdlib5Lists4List9app_nil_rC46Stdlib7Sorting;Permutation>Permutation_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK9ent_factsC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel8hh_rangeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK9lnk_chainC46Stdlib5Lists4List:removelastC46Stdlib5Lists4ListCapp_removelast_lastC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK3lnkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK3hdaC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK7lnk_appC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS9syms_sameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS?syms_same_soundK47Corelib4Init5Logic2ex01I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C46Stdlib5Lists4List4lastC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel2hhC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5chainC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel4hkeyC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK2d0I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z6inj_lec6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL6R_LOOPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehD6R_EXITc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL5keptLc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL2WLc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL8n_factsLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL3srLI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK?chain_last_nextC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK?chain_head_nextC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List9last_lastC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI3gzAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK46Stdlib9micromega=RingMicromega5Psatz07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel9step_samek6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4LSTA01C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z9mod_smallK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_ltuK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_remuC56Stdlib6ZArith6BinInt1Z6ltb_geC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK:perm_nodupC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK<nodup_app_neC47Corelib4Init5Logic:not_eq_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK;nodes_apartC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL?outside_map_invK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotK46Stdlib9micromega5Tauto8GFormula01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL>agree_of_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpI7dsh_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel:step_emptyC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission7LibHash9HRepFacts;cellw_agreeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK9lnk_agreeC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_HKitBcellw8_of_rw_cellsK46Stdlib9micromega:ZMicromega;ZArithProof03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6sub_fpC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame<munch_weakenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;munch_transC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;wmono_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge>msteps_mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own;wr_at_wmonoC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond03C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL=sc_storeok_wrC56Stdlib6ZArith6BinInt1Z7eqb_neqK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6insideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?munch_mem_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells6cbytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK<splice_factsC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpS7gz_subEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HEmpD:wr_at_subEI47Corelib5Lists7ListDef6Forall00C46Stdlib7Sorting;PermutationAPermutation_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6kn_fixK46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC4ELinuxProcessSemantics5Riscv3Sem5alu64K46Stdlib9micromega=RingMicromega5Psatz04C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC4ELinuxProcessSemantics5Riscv3Sem7mul_divI46Stdlib5Lists4List5NoDup00K46Stdlib9micromega5Tauto8GFormula07C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvDrw_cells_mem_denot_wC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4K4ELinuxProcessSemantics5Riscv5Instr5aluop07c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL3KNLK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5mulop08I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOK4ELinuxProcessSemantics5Riscv5Instr5mulop01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL<HTLbAHRehL_0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL9loop_exitc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL9loop_stepC4ARocqVerifyHarness?AgentSubmission6CatSim<msteps_transc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4REGFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4REGXC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_alC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit5gz_atc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL<kshadow0_regC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehK?ents_nil_of_bc0C4ARocqVerifyHarness?AgentSubmission8PropExec<Z_land_rangeC46Stdlib7Sorting;Permutation@Permutation_reflC5ARocqVerifyHarness?AgentSubmission7LibHash<HRehashModel:binv_startc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL6relinkC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_neC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3le8I5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4R_MSc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL3srMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL5keptMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL3KNMK4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_HRehL4KNM0".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition R_LOOP : Z := 0xfaee4.

Definition srL : list expr := srs sr_id [(10%bv, EVar 35); (14%bv, EVar 36); (15%bv, EVar 32); (8%bv, EVar 33); (9%bv, EVar 34);
   (2%bv, EVar 37); (18%bv, EVar 38); (19%bv, EVar 39); (20%bv, ELit SHBASE); (21%bv, EVar 40)].
Definition KNL : list kentry :=
  [KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 28); KRange (EVar 35) 1 (2 ^ 47); KRange (EVar 41) 1 (2 ^ 47);
   KRange (EVar 42) 0 (2 ^ 32)].

Definition keptL : list reg := [2; 3; 4; 5; 6; 8; 9; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma sc_storeok_wr : forall E M (sa : saddr) (A N a : Z) (k : nat),
  wr_at asegs M A N -> adenot E sa = Z_to_bv 64 a -> A <= a -> a + Z.of_nat k <= A + N -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  sc_denot asegs M E (SCStoreOk sa k).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HRehL ()) [] "h06__sat6h14__x1h24__x2h32Hah47__arithh54__ffh66__sat5h78__varmaph85__with94cstrh:4__x3h;4__x4h<1bh=1Ah>1Eh?1Hh@2H1hA2H2hB2H3hC2H4hD1MhE1NhF2WRhG1ahH1khI2sap;1p;4p;2p;3p;8p;9p;6p;7p-1p10000p4p710p8p1000Gp4p710R0g000dR1p4p710p8P0g001@R0p4p710p8g001^j13Tg002Cj1JTg002aj1CTg003Dj1MTg003fj4eTg004`j2GTg005Xj2<j1ZTg006>j38Tg006Xj21Tg0074j14Tg007Tj20Tg0081j1BTg008Oj2dTg008lj4HTg009lj2:Tg00:Ij2=Tg00:cj1FTg00;Hj2WTg00<0j2DTg00<Lj3VTg00=0j2UTg00=Qj1TTg00>1j1QTg00>Qj2>Tg00>oj1PTg00?Mj4;Tg00?kj1OTg00@Ij1NTg00A4j27Tg00AWj3@Tg00B:j36Tg00B]j4ATg00CHj2LTg00Cjj2KTg00DVj3RTg00E5j4STg00Egj8cTg00FDj1ITg00G;j1bTg00G]j2aTg00H@j1]Tg00Hel9\TP1j6[TP0j6YTg00Ihj2^Tg00Jdj4_Tg00Kdj7XTg00LHj8`Tg00LlR0f0R1'1p=2g00MJR2g00MjR3781p=?f1R4g00NJR5g00NiR6P6g00OIR7P1g00OiFXp=5g00PIR8P4g00PgP1CAp=9f3R9P5P6P6P7f2R5P4P1G`p=Eg00QNg00RER:#3R;#3R<#3R=#3#3#3R>#JR?#CR@%J=#C#M[g00Rjg00Scg00TBR=f5RAP9P5Cef7RB/GA1<?558@11A9f4RC%49'0f6RD/0A'1%2A%4A,0D%B;RA%B>R>'dRE'1P@1<?BRFP=f<RGP1PBCH#?X<@P8P@%Z?RHPHf9RI1:BI'0RJPBP@\8/=H%FD%4D#21WA>RH1D0ARK%2>1D0E[RL[RM%2ARNg00U9ROAVA>4UW3R>%2E\O^3NRNP4g00UU1U0A'=PKeO1RKPLg00V;RA#TRO%QARAP81>85P4%P8REC;RP%O8RQ%N8RRP8178:RS178;R;=@8S568g00VgP;CA'51LR7R7P1P51=231K15#?dAR804CSR3b5b7b8X18X281:41,01=884^18^28P1PGf>R2O2b4b0b6b0b9Gc%IJ=8@FRFePFP@f:RFf8RJ/:FRT'0#IP=f=RUP1PJCH#?X<@P=PGPFPIPTPBPD%FBRT%4B#2RBPHPMP>PNPKPLPOPAPPPQPR19;S,5R%b6R61a80A@8S;R0'9,5RCEP7P3b5b7b8X18X2811411:45RP#2[^18^28P1f?R@PUPIO3b4b0b6b0b9PTPBPHPMP>PNPKPLPOPAP8P81>8CP5PEC;P41>89C;PQPR%]:,78R:968S178<R<968;'9,5RP6A680:/9<,5RCEP7P3b5b7b8X18X28X:8X;810151049'110P9/1C[^18^28^:8^;8P1P2%4GP@PUPJO5b4b0b6b0b9M9\1<?JP1E[b?1GGFPCEYP=f;PG1^FDC_eWCWBWAW@W3WFWHXG8XE8X=8WIWDW>o"). Qed.

Lemma agree_of_munch : forall W m m' a k, munch W m m' -> (forall x, a <= x < a + k -> outside W x) ->
  0 <= a -> a + k <= 2 ^ 64 -> agree_on m m' a k.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HRehL ()) [] "h06__sat1h14__x1h24__x2h34__x3h42Hah57__arithh64__ffh76__sat0h88__varmaph95__with:2HOh;3Hakh<2Hih=2MUh>1Wh?1ah@1ihA1khB1mhC2m'hD1xhE1zp;1p;3p;2p;4p;6p;7p;8g00>1j1HTg001^j13Tg002Cj1BTg002aj1?Tg003Dj1dTg00WNj3YTg006Xj26Tg007Tj24Tg00<0j22Tg00XKj25Tg00Xfj2ETg0081j1CTg008Oj2cTg005Xj2bTg00;Hj2]Tg00<Lj3XTg00=0j2WTg00:Ij2FTg00=Qj1VTg00>Qj2DTg00?Mj4UTg00?kj1PTg00@Ij1OTg00G]j2ATg00A4j2>Tg00H@j1NTg00G;j1MTg00B:j3@Tg00CHj2LTg00Cjj2QTg006>j3RTg00DVj3KTg00E5j4STg00Yej2TTg00ZOj1;Tg00Znj27Tg00[Wj3:Tg00\@j2JTg00\lj3GTg00]Lj3aTg00]oj2\Tg001@j6ZTg00^ij4[Tg00B]j4ITg00Kdj7^Tg00_hj7_Tg00LHj8`Tg00LlR0f0R1'6p=0g00PIR2f1R3g00PgP1CIp=8P3g00NJR4g00NiR5P5g00OIR6P1g00OiF^p=1P2P3g00`LP1CIp=<f2R7P4P5P5P6P3P1F_p==f3R8P4P5P5P6P7P3P1G`p=9g00a3#Hg00RER4#3R9#3#3R:#3#3#3R;#BR<#?%B:#?#d[R:f4R=?Y8716811487,21'5f7R>/E3[^D2%0814=8%C9R?%C;R;'cR@'6%01f5RA,21'5PA14>3RB,b<RCP2PBf;RD/E1XE2P=PB1]?;RE120?RF%0;120@[RG[RH%0?RIg00U9RJAX?;3UW4R;%0@\J^4IRIP3g00UU1W0?'FPFeO1RFPGg00V;RJ#VRK%HJRLP21D27P31D28CURM%P2RN%O2RO1A20RP1>29R9'8,1O%N4,>2RQ,<9,1O5=ORR%M5R51>24R4A@249R9'8,1OA@24QRQ,<9,1O5=OC91LO6R6P1P7g00MJRSg00MjRT'F1Q17=RSTdAK203CSR0b6b8b9X12X22X32%031237'5RT1437RS,631438R3,2S'5[^12^22^32P1f:RSPAPDP=O4b5b0b7b0O21T<CPEPHP;PIPFPGg00anRG#;RF#;RI#;R;,72172I172GRG5:25:2g00bMRI'J%;;,72172F=:2G5:2/JI=GJK5GJPLPMPNPOPRP5PO1A2?=a2<R<,8Q,1OP5PO18P4,1OP518P9,1O1<9<,1O5=OC9C9C9P6P0b6b8b9X12X22X32163@%07148=R8#0128@'5[[\T^12^22^32P1PSPAPDP=f6RDP>O6b5b0b7b0,\BEZO2W<X@2P>PDPAP=C[eW;W4W:W=XA2X?2XC:WBW>o"). Qed.

Lemma outside_map_inv : forall (l : list (Z * (Z * Z))) x e,
  outside (map (fun e => (HRehashModel.addr Z e, HRehashModel.addr Z e + 8)) l) x -> In e l ->
  ~ (HRehashModel.addr Z e <= x < HRehashModel.addr Z e + 8).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HRehL ()) [] "h03Hinh12Hoh22IHh31eh41lh51Hh62H0h72e0h81xp;2p;1p;4p;3p;7p;5g00c9R0p4p711R1g00d6R2p4p710p8P1p100Egp4p710p8P1p100dRp4p710p8g00dmj29Tg00>1j1ETP0j1<Tg001^j16Tg0081j1CTg007Tj24Tg00eMj4;TP2j45Tg00Xfj22Tg00emj31Tg00=Qj1:Tg00\lj38Tg006>j37Tg000dj7DTg00fDj5BTg00ffj2?Tg006Xj2>Tg00<0j2=Tg00XKR2j2@Tg00gdj1ATg00PIR0f0R1'?p=3f3R3f2R4'>f1R5/=1'@#Ap=01900R6,90R7#ER8P7%<0R9P6P0P0%31R:g00RE#6#6#6#CR;,4:C;X39R:P1C5R</24A1745%33R=f4R>P>14=;C0R=[[X48P9P6P:%:7R?C5/25A175?g00h=P=P1n010000000W0W112<3A1735%3>R<f5R=P=14<;R=C0[[P9P6P:A8745C5/2>A8734917>P2P<f6R<P<P=C0P9P6P:P3C5/2<%3<R3f7R=P=143;R2C0P5P3f8R3P3P2C0P9P6P:P<C5f9R<'2g00hZA773<A17<=f:R=#3R2f;R?P?142;C0P>A77<=P7P=P9P6P:P=C5f='2A175?%34R2f?R@P@142;C0[[%35R2f>R@P@142;C0]2X37P9P6P:P<C5f<R<'2A17?=%3<R<P@P@14<;C0[[P>W2P?P1P3FDW5P1O1A17=3P3P4P1O2W0P1O1n200100000021000010000W1W6P5P1O2n2001000000121000000W0W1W2X48X77P4DBX37X80W4o"). Qed.

Ltac nrmR HX := rewrite ?w_remu by lia; rewrite ?HX; rewrite ?w_mul by lia; rewrite ?w_add by lia; rewrite ?v_addi_Z by lia.
Ltac sc_brR HX := cbn [sc_denot]; evs; cbn [edenot]; nrmR HX; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.
Ltac sc_djR HX := cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_off a_base]; nrmR HX;
  rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia.
Ltac sc_shdjR HX :=
  cbn [sc_denot]; unfold flat, elenZ;
  repeat (erewrite estart_sh; [| evs; cbn [edenot]; nrmR HX; reflexivity | lia]);
  unfold estart; cbn [a_base a_off]; evs; cbn [edenot]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [edenot];
  repeat match goal with
  | |- context [?a / 8] =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
  end;
  rewrite ?u64_of_Z by lia;
  unfold SHBASE; lia.
Ltac sc_flatR HX b := eapply (sc_flat _ _ _ _ b); [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn; lia | lia | cbn; lia].
Ltac sc_rdR HX C := eapply (sc_read_cellw _ _ _ _ _ _ _ _ C); [cbn; lia | evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | evs; first [reflexivity | f_equal; lia]].
Ltac kshadow_tacR HX :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 (ELit 0)) =>
      eapply kshadow0; [evs; cbn [edenot]; nrmR HX; reflexivity | lia | sh0_from_gz]
  end.
Ltac know_tacR HX := repeat (apply Forall_cons; [first [kshadow_tacR HX | kentry_tac] |]); apply Forall_nil.

Ltac rwc_newR HX Hlf WR :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m ?lg) ?A [?c] =>
    let rec go pre post :=
      lazymatch post with
      | SE ?a ?w ?v :: ?post' =>
          first [ eapply (rw_cells_mem_denot_w E m pre a w v post' A c);
                  [ exact Hlf
                  | repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia|]); apply Forall_nil
                  | unfold estart; evs; cbn [edenot a_off a_base]; nrmR HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia
                  | exact WR | reflexivity | exact I | evs; cbn [edenot cbytes]; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity ]
                | let pre' := eval cbn [app] in (pre ++ [SE a w v]) in go pre' post' ]
      end in
    go (@nil sentry) lg
  end.
Ltac sc_soR HX WR := eapply (sc_storeok_wr _ _ _ _ _ _ _ WR); [evs; cbn [edenot]; nrmR HX; first [reflexivity | f_equal; lia] | lia | cbn; lia | lia | cbn; lia].

Lemma kshadow0_reg : forall E M e (x : Z),
  edenot E e = Z_to_bv 64 (x / 8 + SHBASE) -> 0 <= x < 2 ^ 47 -> sh0 M x ->
  kentry_ok ASEGS E M (KWord (SA e 0) 1 (ELit 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HRehL ()) [] "h06__sat1h16__sat3h24__x1h37__arithh44__ffh56__sat0h66__sat2h78__varmaph85__with92Hah:6__sat4h;4__p1h<6__sat5h=1xh>1bh?6__sat6h@1zhA1EhB2HehC2HrhD2HshE2HxhF1MhG1ehH1lhI1mhJ1nhK1yp%0p&0p;1p;2p;3p;6p;4p;5p;<p;7p;8p;Bg001^j1GTg002Cj1KTg002aj1XTg00i4j2LTg0081j18Tg00ilj2ATg007TR0j22Tg005Xj2<Tg006>j39Tg008Oj2MTg00<0j23Tg00XKj21Tg00jIk208Tg00kAj2WTg00;Hj2TTg00<Lj3STg00=0j2wTg00:Ij2CTg00=Qj1YTg00>1j1_Tg00>Qj2pTg00?kj1oTg00@Ij1mTg00G]j2ETg00A4j2kTg00l2j6gTg00G;j1fTg00CHj2eTg00Cjj2dTg00DVj3cTg00E5j4bTg00>oj1aTg00lVk40<Tg00]Lj3VTg00m7k30;Tg00mZk20:Tg00n7k509Tg00ncj4UTg00ZOj1:Tg00o>R1k207Tg00oXj2^Tg0074R2j1]Tg010Qk303Tg003Dk102Tg004`k201Tg011Mj1zTg012Ej2\Tg013Mj2JTg006XR3j25Tg013oj4[Tg00Yej2PTg00H@j1OTg014Zj3ZTg015@j1uTg015^j4rTg016Al<NTg016fj6QTg00B:j3RTg00]oj2vTg001@j6@Tg017Oj1nTg018Gj1yTg019>j2HTg00\lj3{Tg01:2j1|Tg01:Sj3}Tg01;Mj2lTg01<Tj3~Tg01=Nk400Tg00B]j4`Tg00Kdj7jTg00_hk704Tg00LHj8iTg01>Ok405Tg01?@m<06Tg01?elBhTf0R4#G#Gp=6g00LlR5/54p=0%O4#Op=71354p=Dg00PIR6f1R7g00PgP4C`p==P7g00NJR8g00NiR9P9g00OIR:P4g00OiFjp=4f2R;P8P9P9P:P7P4K04p=;f3R<P8P9P9P:P;P7P4Gip=IP6P7g00`LP4C`p=>g01@KS00P;P7P4H05p=B1C64p=?g00ScR=P6P1P2P3g01Aif5R1f4R>P<P;P7P4M<Np=x1174,1;p=FP=P6P6P6P2P2P1P>P<P;P7P4N<06p=tP6P6P3P1P3P>P5P5P<P;P7P4M<Np=sP6P6P6P6P6P6P0P4P7P;P0P<P>P1f6R0f7R2f8R?f9R@MBhp=qg00QNg01BKg01C<g00RERA#GRB#6RC#G#6RD#KRE#XRF1L<7%8CRG,A4g01D4RH'2,<E39%07RI%8BRJ%7BRB#7RK#8RL'MRM,37'1208>;1A<GRN#0RO%6BRB#8RP,MJRQ,3NRNP<PG1W<GRR%0<%0GRS1A1GRT#0[[RU1TJLRV%DJRW%0L%DM[RX[RY%0JRZg00U9R[ASJL7UW9RL%0M\[^9ZR\P7g00UU1w5J'CPWeR]O1R^PXp-0R_g00V;R`#YRa%_`R`1p67Rb%o6Rc%m6Rd1E65Re1k6ARf'=,4dRgPdP8P9P9P:P<EgR85;d%f9R9PgCI1ed:R:P4P;g00MJRhg00MjRi'C1d4;=9hidAc657CbRib4b7b8X26W;%04Rh/17PI[^26^;_P413?MP?P0O3b3b0b5b0b6PRPUPVPYPLP\P^PXPaP`%a6R?Pc1E6GRI,>e,4dP:Pib4b7b8%DGP4b3b0b5b0b6R;H0<P<PGPQP;PRPU1TJPRU%0P%DQ[RR\WR;ASJP7V[X9ZRP%0Q\[^9ZRjPVPYPLP\P^PXP>P]O1RkPRPaP`PbPcPd1E6JRl%KK5V6,>f,4d9;d8P9%KB9V6lRB:0;6I,>f,4dCIP:Pib4b7b8X26X;_134M,1720:GQ,37[^26^;_P4f;RM#0PMP@O3b3b1b0b5b0b6b1b:I09CU11ONg00an#:RN%:N#:#:#:#:#:#:RO+07R@1^15R8%]NRK6032Rm%KCRC#XRn#_Ro$02Rp20128=B0N%z5Rq,L2,\N,JoRr39Rs'1P@%8AR@/5GRtPNP@%?@S01POPG%?GEx1W>GRO%0>1A0G#0\S[RSPUP;PPPjPVPYPLP\P^PXPkPRPaP`P?Pc1E6@Ru/=I,4dP:Pib4b7b8PtP4b3b1b0b5b0b6b1b:C[PmPsPF1A>GRt/2HRI,<ERv1PE4/25Rw#0%8DRx,MJRy,3w%0KRz12wK/5y'13FX>FP6PI1245Rw#013wy12wK/5y,1z3FX@6%OA#7#7#7#7#7#7#7#G#6#6#6#6#6#6#6#8RA,2t/25Rt#0Rw13tyR{12tKS02/5yS03,1zS04'1S05'1%0@R|12t@S06/5yS07'1R},1{R~,1wPwQ05PwP~1C_w9ZwwP{Q04P{P}1C_{9Z{{PzQ03P|Q07P4X=6R{1574#uXK6X=6R_1C65PKP@P{P{%]4#?X==PNP@Q01EtR=EsP6P6P3P{P3P_Q02Q06P{P{P{P6P6g01Do1274Cr#?XI6XJ6PtPt%?tPKP@P=M:qPyPy%?yM<NEQEQEQPOPSPUP;PPPjPVPYPLP\1TJxR=%0x%Dy[Rt\WRWASJx7V[X9ZRx%0y\[^9ZRZP^PtPkPXP2P]O1R]PRPaP`PbPcPd1>fB,4d9;dgRgP91E6A9R6fRf=R6eRB,=e,4dAV6lERl,>B,4d1=eu,4dAR6Bu/=l,4d5;d5;d5;dCIP:Pib4b7b8X26134Q,1hRh127ARA/25RQ#013Qy12Q@/5y,1|3F[^26P4f?/AGPMO2RMb3b<b1b0b5b0b6b1b:b<b?C[12I5RG#013Gy12GK/5y,1z3Fe1PEvPOPSPUP;PPPjPVPYPLP\P=PWPxPZP^PtPkPXP]PRPaP`PbPcPdPgP91=ef,4d1>fl,4d5;dCIP:Pib4b7b8X26%0A13Ay'1\h^26PMb3b<b1b0b5b0b6b1b:b<b?%0I13Iy'1eRM,vIE@1L21RhP<E@%n8,L2RA,PE%y8R8'2Rl#013ly12lK/5y,1z3FePmePFPv1H45=B2N1<E5,\NRm,Jo59pX>FPo1<C5%Yn5{nRn12TH,<E/H5=B2N1Jo459pXHoPF1<EGAB24N1JonRn59pX>FP6PI1<E4=B2N=9pnX@6P7PG%|IE@1Hv5A}I5ME@PmPOPSPUP;PPPjPVPYPLP\P^PXPkPRPaP`P?Pc1=ee,4d%6D#8RD,E6,>e,4d5;dP:Pib4b7b81555%DD'1P4b3b1b0b5b0b6b1b:,l5E@PhP<E@1HA8=B0N=9prePseCUCUbCQ00P0P11^>5?~NqH00eWDWEWBX=6WGWFWAo"). Qed.

Definition R_MS : Z := 0xfad9c.
Definition srM : list expr := srs sr_id [(8%bv, EVar 33); (9%bv, EVar 34); (2%bv, EVar 35); (18%bv, EVar 36); (19%bv, EVar 37); (20%bv, ELit SHBASE); (21%bv, EVar 38)].
Definition KNM : list kentry :=
  [KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 28); KRange (EVar 34) 7241728 (2 ^ 47); KRange (EVar 39) 1 (2 ^ 47);
   KRange (EVar 40) 0 (2 ^ 32); KWord (SA (EVar 38) 0) 1 (ELit 0)].
Definition KNM0 : list kentry :=
  [KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 28); KRange (EVar 34) 7241728 (2 ^ 47); KWord (SA (EVar 38) 0) 1 (ELit 0)].
Definition keptM : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section RehL.
  Context {HCEIL : HeapCeil}.
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (spz : Z) (F : bvmap 5 word) (fc : bv 32).
  Variables (obj bl bc p : Z) (ents : list (Z * (Z * Z))) (A0 : list (Z * Z)) (M0 ML : mem).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation ent := (Z * (Z * Z))%type.
  #[local] Notation addr := (HRehashModel.addr Z).
  #[local] Notation hkey := (HRehashModel.hkey Z).
  #[local] Notation hh := (HRehashModel.hh Z n).
  #[local] Notation sent := (obj + 16).
  #[local] Notation d0 := (LbB_HRehK.d0).
  #[local] Notation st R pc M := (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 pc) M (seg_rom asegs)).

  Hypothesis U0 : umapx MI_A 24 (nval24 ASEGS) A0 M0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis HP : 0 < p /\ p mod 16 = 0 /\ AIMG_TOP <= p /\ p + 8 * n <= aceil /\ aapp p (8 * n).
  Hypothesis HPN : forall e, In e ents -> apart p (8 * n) (addr e) 24.
  Hypothesis HPO : apart p (8 * n) obj 40.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis OAPP : aapp obj 40.
  Hypothesis NAPP : forall e, In e ents -> aapp (addr e) 24.
  Hypothesis SPR : 2 ^ 45 <= spz - 64 /\ spz <= 2 ^ 47.

  Definition WL : list (Z * Z) := (p, p + 8 * n) :: (obj + 16, obj + 24) :: map (fun e : ent => (addr e, addr e + 8)) ents.

  Record LREG (P S : list ent) (R : bvmap 5 word) : Prop := LRG {
    r_x2 : getr R 2%bv = Z_to_bv 64 (spz - 64); r_x3 : getr R 3%bv = gp; r_x4 : getr R 4%bv = tp;
    r_x5 : getr R 5%bv = Z_to_bv 64 1; r_x6 : getr R 6%bv = Z_to_bv 64 (2 ^ 60);
    r_x8 : getr R 8%bv = Z_to_bv 64 n; r_x9 : getr R 9%bv = Z_to_bv 64 obj;
    r_x10 : getr R 10%bv = Z_to_bv 64 (addr (last P d0)); r_x11 : getr R 11%bv = Z_to_bv 64 (hdaddr S);
    r_x14 : 2 <= bv_unsigned (getr R 14%bv); r_x15 : getr R 15%bv = Z_to_bv 64 (n - 1);
    r_x16 : getr R 16%bv = Z_to_bv 64 (hh (last P d0)); r_x17 : getr R 17%bv = Z_to_bv 64 p;
    r_x18 : getr R 18%bv = Z_to_bv 64 (obj + 8); r_x19 : getr R 19%bv = Z_to_bv 64 SHBASE;
    r_x20 : getr R 20%bv = Z_to_bv 64 (obj / 8 + SHBASE); r_x21 : getr R 21%bv = Z_to_bv 64 ((obj + 8) / 8 + SHBASE);
    r_x22 : getr R 22%bv = s6; r_x23 : getr R 23%bv = s7; r_x24 : getr R 24%bv = s8; r_x25 : getr R 25%bv = s9;
    r_x26 : getr R 26%bv = s10; r_x27 : getr R 27%bv = s11
  }.

  Record LMEM (P S : list ent) (Bf : Z -> Z) (M : mem) : Prop := LMM {
    l_perm : Permutation (P ++ S) ents;
    l_binv : binv Z n sent P Bf;
    l_P : P <> [];
    l_p1 : cell8 ASEGS M sent (hdaddr (P ++ S));
    l_chain : chain ASEGS M (P ++ S);
    l_hash : forall e, In e ents -> cell8 ASEGS M (addr e + 8) (hkey e);
    l_bkt : forall i, 0 <= i < n -> cell8 ASEGS M (p + 8 * i) (Bf i);
    l_adp : addressable M p (8 * n);
    l_adh : addressable M obj 40;
    l_adn : forall e, In e ents -> addressable M (addr e) 24;
    l_mu : munch WL ML M;
    l_wm : wmono asegs ML M;
    l_mi : mem_inv asegs M;
    l_wrp : wr_at asegs M p (8 * n);
    l_wrh : wr_at asegs M obj 40;
    l_wrn : forall e, In e ents -> wr_at asegs M (addr e) 24
  }.

  Lemma n_factsL : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ 0 <= bc.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_HRehL ()) ["RehL"] "h02Hah11Hh24__p1h37__sat14h47__sat16h57__sat18h64__x1h71Ah81Bh91Ch:2_Hh;7__arithh<4__ffh=7__sat12h>7__sat13h?7__sat15h@7__sat17hA8__varmaphB5__withC1ap;1p;>p;3p;2p;4p;7p;6p;8g00H@j10Tg001^j12Tg0081j13Tg01ESj1\Tg01FKl>VTg01GCj3LTg01HJj1ETg00emj3CTg00<0j26Tg00mZj2ATg008Oj2;Tg006Xj27Tg006>j38Tg00XKR0j24Tg009lj2WTg01IEj2UTg00gdj1TTg00hZj2QTg01Icj2KTg00;Hj2:Tg00<Lj39Tg01Jej2DTg01KVj2FTg00=0j2GTg00:Ij2=Tg00=Qj1HTg00>1j1BTg00>Qj2ITg00?kj1JTg00@Ij1@Tg00G]j2MTg00A4j2NTg00B]j4?Tg00Kdj7OTg00l2j6PTg00_hj7>Tg00G;j1RTg00LHj8STg00CHj2[Tg00Cjj2ZTg00DVj3YTg00E5j4XTg00ncj4<Tf0R1#2#2p=5g00LlR2/71p=1p,2bcR3g01L6g01@KR4g01M0g01Mjg00RER5#0R6#5R7#2#3g00PIR8%\4p,2A0p,2M0p,3objp,2blP3p,4entsp,2U0M>VR4p,5Hlast3L%E3R9g01Nd5C8R:1639R;%25R<#5R=#3/A9%3<R>%06#5#3R?';R@'7RAA8832A889>'4%36/79%35,W9,U9=882#T'4'QR9'4R6'4RB'4P0P:PB%13RC,4ARD,4;RE,4:RFP1P0P;P6PFP1P0PAP9PFP11K34%07#2#5#0#0#0#0#2#0#2#0#2#0#5#5#5#0#3,73R7,4CP:PEf:P;PDf6PAPCf2RC%0<#0R<#2#0#3RD,:>162>RE%1D1;>DR4,62[RF[%1>R0g00U9RGf1RH99>DUW0%14\G^00%0<#0#3R<,:>%1<1;><R4,62[RD\EA9><HVGX00%14\G^001:>?%1?162@[R4\EA9>?HVGX00%1@\G^00p,1pR0%2=#3R='D%10%1=1F0=#1[[PCg00UU1G2>'=PEeREO1P4f5PEO1PDf8PEO1PFp-0RFg00V;RE#H%BE1I8H%J8%@8REg00NJRDg00NiR4P4g00OIR>PEPDP4P4P>PEPDP4P4P>P81M82g00Pg1N85C?g00OiFOR5PEPDP4P4P>f3EPF>%R4P5GS1[E>P1PCg00MJR>g00MjRE'=1Z1C=8>EdAY82HCXb<bAbBX68W2%11/4H%1H[^68^2FP1P7P3f;O3b;b5b4b3b=b>b3b?b4b@b5C<C<C<b1X:9X9APHP1O2n2001000000121000000X16X8;PHP1O2n2001000000121000000X1BX7:PHP1O2n2001000000121000000bCo"). Qed.

  Definition L_STOPS : list Z := [0xfaee4; 0xfb048; 0xfb06c; 0xfb070; 0xfb074; 0xfb078; 0xfb07c; 0xfb080; 0xfb084; 0xfb088; 0xfb08c; 0xfb090; 0xfb094; 0xfb098; 0xfb09c; 0xfb0a0; 0xfb0a4; 0xfb0a8; 0xfb0ac; 0xfb0b0; 0xfb0b4; 0xfb0b8; 0xfb0bc; 0xfb0c0; 0xfb0c4; 0xfb0c8; 0xfb0cc; 0xfb0d0; 0xfb0d4; 0xfb0d8; 0xfb0dc; 0xfb0e0; 0xfb0e4; 0xfb0e8; 0xfb0ec; 0xfb0f0; 0xfb0f4; 0xfb0f8; 0xfb0fc; 0xfb100; 0xfb104; 0xfb108; 0xc0cbc; 0xc0fdc].
  Definition srLS : list expr := srs sr_id [(8%bv, EVar 35); (19%bv, ELit SHBASE); (5%bv, ELit 1); (6%bv, ELit (2 ^ 60)); (10%bv, EVar 36); (11%bv, EVar 37); (14%bv, EVar 38); (16%bv, EVar 39); (17%bv, EVar 32); (15%bv, EAlu ALU_ADD (EVar 35) (ELit (-1)))].
  Definition KNLS : list kentry := [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 35) 3 (2 ^ 25); KRange (EVar 36) 1 (2 ^ 47); KAlign (EVar 36) 16; KRange (EVar 37) 1 (2 ^ 47); KAlign (EVar 37) 16; KRange (EVar 38) 2 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 25); KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 41) 1 (2 ^ 47); KAlign (EVar 41) 8; KRange (EVar 42) 1 (2 ^ 47); KAlign (EVar 42) 16].
  Definition SCR_ksl := SCR [true; false] [EVar 40; EVar 42] [].
  Definition SCR_ksx := SCR [true; false] [EVar 40; ELit 0] [].
  Definition SCR_kel := SCR [true; true; false] [EVar 40; ELit 0; EVar 42] [].
  Definition SCR_kex := SCR [true; true; false] [EVar 40; ELit 0; ELit 0] [].
  Definition SCR_kpl := SCR [true; true; false] [EVar 40; EVar 41; EVar 42; EVar 41; EVar 43; EVar 41] [].
  Definition SCR_kpx := SCR [true; true; false] [EVar 40; EVar 41; ELit 0; EVar 41; EVar 43; EVar 41] [].
  Definition SCR_rsl := SCR [false; false] [EVar 40; EVar 42] [].
  Definition SCR_rsx := SCR [false; false] [EVar 40; ELit 0] [].
  Definition SCR_rel := SCR [false; true; false; false; false] [EVar 40; ELit 0; EVar 42] [].
  Definition SCR_rex := SCR [false; true; false; false; false] [EVar 40; ELit 0; ELit 0] [].
  Definition SCR_rpl := SCR [false; true; false; false; false] [EVar 40; EVar 41; EVar 42; EVar 41; EVar 43; EVar 41] [].
  Definition SCR_rpx := SCR [false; true; false; false; false] [EVar 40; EVar 41; ELit 0; EVar 41; EVar 43; EVar 41] [].

  Definition OSHR (A k : Z) : Prop := A + k <= ALOWSH_LO \/ AHI_LO <= A.

  Lemma w_srlR : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k < 64 ->
    alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a / 2 ^ k).
  Proof.
    intros a k Ha Hk. apply bv_eq. cbn [alu64 alu].
    rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small a), (Z.mod_small k), (Z.mod_small 63) by lia.
    replace (Z.land k 63) with k.
    2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
    rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= a / 2 ^ k <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; try lia; nia]).
    rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Lemma w_srl61R : forall a, 0 <= a < 2 ^ 61 -> alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 61) = Z_to_bv 64 0.
  Proof. intros a Ha. rewrite w_srlR by lia. rewrite Z.div_small by lia. reflexivity. Qed.

  Lemma nodeF : forall e, In e ents -> 0 < addr e /\ addr e + 24 <= 2 ^ 47 /\ addr e mod 16 = 0 /\ 0 <= hkey e < 2 ^ 32
    /\ apart (addr e) 24 obj 40 /\ apart p (8 * n) (addr e) 24 /\ OSHR (addr e) 24.
  Proof using All.
    intros e He. destruct (LbB_HRehK.ent_facts obj bl bc ents A0 M0 e U0 He) as (E0 & E1 & E2 & E3).
    split; [exact E0|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    split; [destruct e as [a [k v]]; destruct (@u_node _ _ _ _ _ _ _ _ _ _ _ _ _ U0 a k v He) as (_ & _ & _ & _ & _ & _ & _ & _ & Ao & _); exact Ao|].
    split; [exact (HPN e He)|]. unfold OSHR. apply aapp_not_shadowland. exact (NAPP e He).
  Qed.

  Lemma objF : 0 < obj /\ obj mod 8 = 0 /\ obj + 40 <= 2 ^ 47 /\ OSHR obj 40 /\ OSHR p (8 * n).
  Proof using All.
    split; [eapply u_obj_lo; exact U0|]. split; [eapply u_obj_al; exact U0|]. split; [eapply u_obj_hi; exact U0|].
    split; unfold OSHR; apply aapp_not_shadowland; [exact OAPP|]. pose proof HP as (_ & _ & _ & _ & Ha). exact Ha.
  Qed.

  Lemma pF : 0 < p /\ p mod 16 = 0 /\ p mod 8 = 0 /\ p + 8 * n <= 2 ^ 47.
  Proof using All.
    pose proof HP as (H0 & H1 & _ & H3 & _). pose proof aceil_facts as (Ha & _).
    split; [exact H0|]. split; [exact H1|]. split; [clear - H1; Z.div_mod_to_equations; lia | lia].
  Qed.

  Lemma nF : ents <> [] -> 3 <= n /\ n <= 2 ^ 25 /\ bc <> 0.
  Proof using All.
    intros Hne. destruct n_factsL as (N0 & N1 & N2 & N3).
    assert (Hbc : bc <> 0) by (intro E0; apply Hne; exact (LbB_HRehK.ents_nil_of_bc0 obj bl bc ents A0 M0 U0 E0)).
    assert (Hbs : In bc BSEQ) by (eapply u_bseq; exact U0).
    destruct (LbB_HEmpR.bseq_next_factsE bc Hbs Hlast) as (_ & _ & _ & [[B0 _]|[B3 _]]); [contradiction|].
    split; [exact B3|]. split; [lia | exact Hbc].
  Qed.

  Lemma sub_bkt : forall i y, 0 <= i < n -> outside WL y -> ~ (p + 8 * i <= y < p + 8 * i + 8).
  Proof. intros i y Hi Hy. unfold WL in Hy. cbn [outside] in Hy. destruct Hy as [Hy _]. lia. Qed.

  Lemma sub_sent : forall y, outside WL y -> ~ (obj + 16 <= y < obj + 16 + 8).
  Proof. intros y Hy. unfold WL in Hy. cbn [outside] in Hy. destruct Hy as (_ & Hy & _). lia. Qed.

  Lemma sub_node : forall e y, In e ents -> outside WL y -> ~ (addr e <= y < addr e + 8).
  Proof.
    intros e y He Hy. unfold WL in Hy. cbn [outside] in Hy. destruct Hy as (_ & _ & Hy).
    exact (outside_map_inv ents y e Hy He).
  Qed.

  Lemma hash_node : forall e z y, In e ents -> In z ents -> addr e + 8 <= y < addr e + 16 -> ~ (addr z <= y < addr z + 8).
  Proof using All.
    intros e z y He Hz Hy. destruct (Z.eq_dec (addr e) (addr z)) as [E|E]; [lia|].
    pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 e z U0 He Hz E) as A. unfold apart in A. lia.
  Qed.

  Lemma node_node : forall e z y, In e ents -> In z ents -> addr e <> addr z -> addr e <= y < addr e + 8 -> ~ (addr z <= y < addr z + 8).
  Proof using All.
    intros e z y He Hz E Hy. pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 e z U0 He Hz E) as A. unfold apart in A. lia.
  Qed.

  Lemma lmem_frame : forall P S Bf M P' S' Bf' M' W,
    LMEM P S Bf M -> munch W M M' -> wmono asegs M M' -> mem_inv asegs M' ->
    sub_fp W WL -> (forall e, In e ents -> forall y, addr e + 8 <= y < addr e + 16 -> outside W y) ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W ->
    Permutation (P' ++ S') ents -> binv Z n sent P' Bf' -> P' <> [] ->
    cell8 ASEGS M' sent (hdaddr (P' ++ S')) -> chain ASEGS M' (P' ++ S') ->
    (forall i, 0 <= i < n -> cell8 ASEGS M' (p + 8 * i) (Bf' i)) ->
    LMEM P' S' Bf' M'.
  Proof using All.
    intros P S Bf M P' S' Bf' M' W LM MU WM MI SUB HO FW PE BI PN C1 CH BK.
    destruct LM as [_ _ _ _ _ Lhash _ Ladp Ladh Ladn Lmu Lwm _ Lwrp Lwrh Lwrn].
    destruct pF as (Hp0 & _ & _ & Hp1). destruct objF as (Ho0 & _ & Ho1 & _). destruct n_factsL as (N0 & N1 & N2 & N3).
    constructor; try assumption.
    - intros e He. destruct (nodeF e He) as (E0 & E1 & _).
      apply (cellw_agree ASEGS M M' (addr e + 8) 8%N (hkey e) (Lhash e He)); [| cbn; lia | cbn; lia].
      apply (agree_of_munch W M M' (addr e + 8) 8 MU); [intros y Hy; apply (HO e He y); lia | lia | lia].
    - apply (addressable_transport W M M' p (8 * n) Ladp MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - apply (addressable_transport W M M' obj 40 Ladh MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - intros e He. destruct (nodeF e He) as (E0 & E1 & _).
      apply (addressable_transport W M M' (addr e) 24 (Ladn e He) MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - exact (munch_trans WL ML M M' Lmu (munch_weaken W WL M M' SUB MU)).
    - exact (wmono_trans asegs ML M M' Lwm WM).
    - exact (wr_at_wmono M M' p (8 * n) Lwrp WM).
    - exact (wr_at_wmono M M' obj 40 Lwrh WM).
    - intros e He. exact (wr_at_wmono M M' (addr e) 24 (Lwrn e He) WM).
  Qed.

  Lemma lreg_step : forall P S R P' S' R', LREG P S R -> (forall r, In r keptL -> getr R' r = getr R r) ->
    getr R' 10%bv = Z_to_bv 64 (addr (last P' d0)) -> getr R' 11%bv = Z_to_bv 64 (hdaddr S') ->
    getr R' 16%bv = Z_to_bv 64 (hh (last P' d0)) -> LREG P' S' R'.
  Proof.
    intros P S R P' S' R' LR K H10 H11 H16. destruct LR.
    constructor;
      first [ assumption
            | match goal with |- getr R' ?r = _ => rewrite (K r) by inb; assumption end
            | match goal with |- 2 <= bv_unsigned (getr R' ?r) => rewrite (K r) by inb; assumption end ].
  Qed.

  Definition STEPR (R : bvmap 5 word) (M : mem) (pc : Z) (Q : mem -> Prop) (a10 a11 a16 : Z) : Prop :=
    exists R' M', CatSim.msteps asegs (st R R_LOOP M) (st R' pc M') /\ (forall r, In r keptL -> getr R' r = getr R r)
      /\ getr R' 10%bv = Z_to_bv 64 a10 /\ getr R' 11%bv = Z_to_bv 64 a11 /\ getr R' 16%bv = Z_to_bv 64 a16
      /\ mem_inv asegs M' /\ Q M'.

  Definition valsL (R : bvmap 5 word) (a36 a37 a39 a40 a41 a42 a43 : Z) : list word :=
    [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 n; Z_to_bv 64 a36; Z_to_bv 64 a37; getr R 14%bv;
     Z_to_bv 64 a39; Z_to_bv 64 a40; Z_to_bv 64 a41; Z_to_bv 64 a42; Z_to_bv 64 a43].

  Ltac nrmL HX := rewrite ?w_remu by lia; rewrite ?HX; rewrite ?w_mul by lia; rewrite ?w_add by lia; rewrite ?v_addi_Z by lia;
    rewrite ?w_srl61R by lia.
  Ltac sc_brL HX := cbn [sc_denot]; evs; cbn [edenot]; nrmL HX; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.
  Ltac sc_arL HX :=
    cbn [sc_denot]; unfold flat, elenZ;
    repeat (erewrite estart_sh; [| evs; cbn [edenot]; nrmL HX; reflexivity | lia]);
    unfold estart; cbn [a_base a_off]; evs; cbn [edenot]; nrmL HX; rewrite ?u64_of_Z by lia; cbn [edenot];
    repeat match goal with
    | |- context [?a / 8] =>
        let t := fresh "t" in let Ht := fresh "Ht" in
        pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
    end;
    rewrite ?u64_of_Z by lia; unfold SHBASE.
  Ltac sc_soL HX W := eapply (sc_storeok_wr _ _ _ _ _ _ _ W);
    [evs; cbn [edenot]; nrmL HX; first [reflexivity | f_equal; lia] | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
    | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Ltac scL HX :=
    lazymatch goal with
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => sc_brL HX
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with C : cell8 _ _ _ _ |- _ => sc_rdR HX C end
    | |- sc_denot _ _ _ (SCStoreOk _ _) => match goal with W : wr_at _ _ _ _ |- _ => sc_soL HX W end
    | |- sc_denot _ _ _ (SCFlat _ _) => sc_arL HX; lia
    | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_SRL _ _) _) _ _ _) =>
        sc_arL HX; match goal with O : OSHR _ _ |- _ => unfold OSHR, ALOWSH_LO, AHI_LO in O; lia end
    | |- sc_denot _ _ _ (SCDisj _ _ (SA (EAlu ALU_SRL _ _) _) _) =>
        sc_arL HX; match goal with O : OSHR _ _ |- _ => unfold OSHR, ALOWSH_LO, AHI_LO in O; lia end
    | |- sc_denot _ _ _ (SCDisj _ _ _ _) => sc_arL HX; match goal with A : apart _ _ _ _ |- _ => unfold apart in A; lia end
    end.
  Ltac regsL G15 := apply regs_ok_srs; [apply regs_ok_seed|];
    repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs;
      first [reflexivity | assumption | (rewrite w_addm by lia; rewrite G15; f_equal; lia)]] |]); apply Forall_nil.
  Ltac knL HX := unfold know_ok;
    repeat (apply Forall_cons; [first [kshadow_tacR HX | (cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; split; lia)] |]);
    apply Forall_nil.
  Ltac runS R M vals scr HX G15 :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    let vs := eval unfold valsL in vals in
    pose (E := Eseed R vs);
    assert (HR : regs_ok E srLS R) by (regsL G15);
    assert (HK : know_ok asegs E M (kn_fix 30%nat L_STOPS scr R_LOOP srLS KNLS 60%N)) by (kn_eval; knL HX);
    xrun_at (PropExec.mkFP F fc) asegs R R_LOOP M (seg_rom asegs) HR HK 400%nat L_STOPS scr 60%N;
    [ split_scs; scL HX | ].
  Ltac finS HX Lmi :=
    lazymatch goal with
    | Hms : CatSim.msteps _ (@PropExec.mkst _ ?R _ ?M0 _) (@PropExec.mkst _ ?R' _ ?mm _) |- _ =>
    lazymatch goal with
    | HR : regs_ok ?E _ R, HR' : regs_ok ?E _ R', Hlf : log_flat ?E ?lg |- _ =>
        change mm with (mem_denot E M0 lg) in Hms;
        exists R', (mem_denot E M0 lg); split; [exact Hms|];
        split; [let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ keptL HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|];
        split; [let G := fresh "G" in rreg HR' 10%bv G; rewrite G; nrmL HX; first [reflexivity | f_equal; lia]|];
        split; [let G := fresh "G" in rreg HR' 11%bv G; rewrite G; nrmL HX; first [reflexivity | f_equal; lia]|];
        split; [let G := fresh "G" in rreg HR' 16%bv G; rewrite G; nrmL HX; first [reflexivity | f_equal; lia]|];
        split; [exact (msteps_mem_inv asegs _ _ Hms Lmi)|]
    end end.
  Ltac munchL HX :=
    apply munch_mem_denot; [match goal with H : log_flat _ _ |- _ => exact H end|];
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; nrmL HX; rewrite ?u64_of_Z by lia;
      cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); apply Forall_nil.
  Ltac rwcL HX W := apply cellw8_of_rw_cells; [match goal with H : log_flat _ _ |- _ => rwc_newR HX H W end | lia | lia].

  Lemma step_sl : forall P x S' Bf M R, LREG P (x :: S') R -> LMEM P (x :: S') Bf M -> hh x = hh (last P d0) ->
    STEPR R M (match S' with [] => R_EXIT | _ => R_LOOP end) (fun M' => M' = M) (addr x) (hdaddr S') (hh (last P d0)).
  Proof using All.
    intros P x S' Bf M R LR LM Hs. 
    pose proof LR as [G2 G3 G4 G5 G6 G8 G9 G10 G11 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27].
    pose proof LM as [Lperm Lbinv LP Lp1 Lch Lhash Lbkt Ladp Ladh Ladn Lmu Lwm Lmi Lwrp Lwrh Lwrn].
    assert (Inx : In x ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; left; reflexivity]).
    assert (Inl : In (last P d0) ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; apply LbB_HRehK.last_in; exact LP]).
    assert (Hne0 : ents <> []) by (intro E0; rewrite E0 in Inx; exact Inx).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & Hx3 & Axo & Apx & Ox).
    destruct (nodeF _ Inl) as (Hl0 & Hl1 & Hl2 & Hl3 & Alo & Apl & Ol).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    destruct pF as (Hp0 & Hp16 & Hp8 & Hp1).
    assert (Hxl : addr (last P d0) <> addr x) by
      (apply (LbB_HRehK.nodup_app_ne P (x :: S') (last P d0) x);
       [exact (LbB_HRehK.perm_nodup obj bl bc ents A0 M0 _ U0 Lperm) | apply LbB_HRehK.last_in; exact LP | left; reflexivity]).
    pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Inl Inx Hxl) as Alx.
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    pose proof (hh_range Z n ltac:(lia) (last P d0)) as Hhl.
    pose proof (Lhash x Inx) as Cxh.
    pose proof (LbB_HRehK.chain_head_next M P x S' Lch) as Cxn.
    pose proof (Lbkt (hh x) Hhx) as Cbk.
    pose proof (Lwrn x Inx) as Wx. pose proof (Lwrn _ Inl) as Wl.
    assert (Wx8 : wr_at asegs M (addr x) 8) by (apply (wr_at_subE M (addr x) 24 (addr x) 8 Wx); lia).
    assert (Wl8 : wr_at asegs M (addr (last P d0)) 8) by (apply (wr_at_subE M _ 24 _ 8 Wl); lia).
    pose proof (gzA M (addr x) 24 (Ladn x Inx) eq_refl) as Gx.
    pose proof (gzA M _ 24 (Ladn _ Inl) eq_refl) as Gl.
    pose proof (gzA M p (8 * n) Ladp ltac:(rewrite Z.mul_comm; apply Z_mod_mult)) as Gp.
    pose proof (gzA M obj 40 Ladh eq_refl) as Go.
    assert (H14 : 2 <= bv_unsigned (getr R 14%bv) < 2 ^ 64) by
      (split; [exact G14 | pose proof (bv_unsigned_in_range 64 (getr R 14%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia]).
    assert (G11x : getr R 11%bv = Z_to_bv 64 (addr x)) by (rewrite G11; destruct x; reflexivity).
    unfold STEPR.
    destruct S' as [|y S''].
    - cbn [hdaddr] in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p p 0) SCR_ksx HX G15.
        finS HX Lmi. reflexivity.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p p 0) SCR_rsx HX G15.
        finS HX Lmi. reflexivity.
    - assert (Iny : In y ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; right; left; reflexivity]).
      destruct (nodeF y Iny) as (Hy0 & Hy1 & Hy2 & _).
      assert (Hny : hdaddr (y :: S'') = addr y) by (destruct y; reflexivity).
      rewrite Hny in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p (addr y) 0) SCR_ksl HX G15.
        finS HX Lmi. reflexivity.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p (addr y) 0) SCR_rsl HX G15.
        finS HX Lmi. reflexivity.
  Qed.

  Lemma step_el : forall P x S' Bf M R, LREG P (x :: S') R -> LMEM P (x :: S') Bf M ->
    hh x <> hh (last P d0) -> Bf (hh x) = 0 ->
    STEPR R M (match S' with [] => R_EXIT | _ => R_LOOP end)
      (fun M' => munch [(p + 8 * hh x, p + 8 * hh x + 8)] M M' /\ wmono asegs M M'
                 /\ cell8 ASEGS M' (p + 8 * hh x) (addr (last P d0)))
      (addr x) (hdaddr S') (hh x).
  Proof using All.
    intros P x S' Bf M R LR LM Hd Hb0. 
    pose proof LR as [G2 G3 G4 G5 G6 G8 G9 G10 G11 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27].
    pose proof LM as [Lperm Lbinv LP Lp1 Lch Lhash Lbkt Ladp Ladh Ladn Lmu Lwm Lmi Lwrp Lwrh Lwrn].
    assert (Inx : In x ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; left; reflexivity]).
    assert (Inl : In (last P d0) ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; apply LbB_HRehK.last_in; exact LP]).
    assert (Hne0 : ents <> []) by (intro E0; rewrite E0 in Inx; exact Inx).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & Hx3 & Axo & Apx & Ox).
    destruct (nodeF _ Inl) as (Hl0 & Hl1 & Hl2 & Hl3 & Alo & Apl & Ol).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    destruct pF as (Hp0 & Hp16 & Hp8 & Hp1).
    assert (Hxl : addr (last P d0) <> addr x) by
      (apply (LbB_HRehK.nodup_app_ne P (x :: S') (last P d0) x);
       [exact (LbB_HRehK.perm_nodup obj bl bc ents A0 M0 _ U0 Lperm) | apply LbB_HRehK.last_in; exact LP | left; reflexivity]).
    pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Inl Inx Hxl) as Alx.
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    pose proof (hh_range Z n ltac:(lia) (last P d0)) as Hhl.
    pose proof (Lhash x Inx) as Cxh.
    pose proof (LbB_HRehK.chain_head_next M P x S' Lch) as Cxn.
    pose proof (Lbkt (hh x) Hhx) as Cbk.
    pose proof (Lwrn x Inx) as Wx. pose proof (Lwrn _ Inl) as Wl.
    assert (Wx8 : wr_at asegs M (addr x) 8) by (apply (wr_at_subE M (addr x) 24 (addr x) 8 Wx); lia).
    assert (Wl8 : wr_at asegs M (addr (last P d0)) 8) by (apply (wr_at_subE M _ 24 _ 8 Wl); lia).
    pose proof (gzA M (addr x) 24 (Ladn x Inx) eq_refl) as Gx.
    pose proof (gzA M _ 24 (Ladn _ Inl) eq_refl) as Gl.
    pose proof (gzA M p (8 * n) Ladp ltac:(rewrite Z.mul_comm; apply Z_mod_mult)) as Gp.
    pose proof (gzA M obj 40 Ladh eq_refl) as Go.
    assert (H14 : 2 <= bv_unsigned (getr R 14%bv) < 2 ^ 64) by
      (split; [exact G14 | pose proof (bv_unsigned_in_range 64 (getr R 14%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia]).
    assert (G11x : getr R 11%bv = Z_to_bv 64 (addr x)) by (rewrite G11; destruct x; reflexivity).
    unfold STEPR.
    assert (Wh8 : wr_at asegs M (p + 8 * hh x) 8) by (apply (wr_at_subE M p (8 * n) (p + 8 * hh x) 8 Lwrp); lia).
    destruct S' as [|y S''].
    - cbn [hdaddr] in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p p 0) SCR_kex HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|]. rwcL HX Wh8.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p p 0) SCR_rex HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|]. rwcL HX Wh8.
    - assert (Iny : In y ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; right; left; reflexivity]).
      destruct (nodeF y Iny) as (Hy0 & Hy1 & Hy2 & _).
      assert (Hny : hdaddr (y :: S'') = addr y) by (destruct y; reflexivity).
      rewrite Hny in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p (addr y) 0) SCR_kel HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|]. rwcL HX Wh8.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) p (addr y) 0) SCR_rel HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|]. rwcL HX Wh8.
  Qed.

  Lemma bkt_facts : forall P x S' Bf M, LMEM P (x :: S') Bf M -> In x ents ->
    (Bf (hh x) = obj + 16 \/ exists y, In y P /\ Bf (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x) ->
    1 <= Bf (hh x) /\ Bf (hh x) + 8 <= 2 ^ 47 /\ Bf (hh x) mod 8 = 0 /\ OSHR (Bf (hh x)) 8
    /\ apart (Bf (hh x)) 8 (addr (last P d0)) 8 /\ apart (Bf (hh x)) 8 (addr x) 8 /\ apart p (8 * n) (Bf (hh x)) 8
    /\ wr_at asegs M (Bf (hh x)) 8 /\ gz M (Bf (hh x)) 8
    /\ (forall a, In a ents -> addr a <> Bf (hh x) -> apart (addr a) 24 (Bf (hh x)) 8)
    /\ (Bf (hh x) <> obj + 16 -> apart (obj + 16) 8 (Bf (hh x)) 8)
    /\ (forall y, outside WL y -> ~ (Bf (hh x) <= y < Bf (hh x) + 8)).
  Proof using All.
    intros P x S' Bf M LM Inx Hbor.
    destruct LM as [Lperm _ LP _ _ _ _ Ladp Ladh Ladn _ _ _ Lwrp Lwrh Lwrn].
    assert (Inl : In (last P d0) ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; apply LbB_HRehK.last_in; exact LP]).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & _ & Axo & Apx & Ox).
    destruct (nodeF _ Inl) as (Hl0 & Hl1 & Hl2 & _ & Alo & Apl & Ol).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op). destruct n_factsL as (N0 & N1 & N2 & N3).
    destruct Hbor as [Hb|(y & Hy & Hb & Hyl & Hyx)]; rewrite Hb.
    - split; [lia|]. split; [lia|]. split; [clear - Ho8; Z.div_mod_to_equations; lia|].
      split; [unfold OSHR in Oo |- *; lia|].
      split; [unfold apart in Alo |- *; lia|]. split; [unfold apart in Axo |- *; lia|].
      split; [pose proof HPO as A; unfold apart in A |- *; lia|].
      split; [apply (wr_at_subE M obj 40 (obj + 16) 8 Lwrh); lia|].
      split; [apply (LbB_HEmpS.gz_subE M obj 40); [apply gzA; [exact Ladh | reflexivity] | lia | lia]|].
      split; [intros a Ha _; destruct (nodeF a Ha) as (_ & _ & _ & _ & Aao & _); unfold apart in Aao |- *; lia|].
      split; [intros E; exfalso; apply E; reflexivity|].
      intros z Hz. exact (sub_sent z Hz).
    - assert (Iny : In y ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; exact Hy]).
      destruct (nodeF y Iny) as (Hy0 & Hy1 & Hy2 & _ & Ayo & Apy & Oy).
      pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Iny Inl Hyl) as Ayl.
      pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Iny Inx Hyx) as Ayx.
      split; [lia|]. split; [lia|]. split; [clear - Hy2; Z.div_mod_to_equations; lia|].
      split; [unfold OSHR in Oy |- *; lia|].
      split; [unfold apart in Ayl |- *; lia|]. split; [unfold apart in Ayx |- *; lia|].
      split; [unfold apart in Apy |- *; lia|].
      split; [apply (wr_at_subE M (addr y) 24 (addr y) 8 (Lwrn y Iny)); lia|].
      split; [apply (LbB_HEmpS.gz_subE M (addr y) 24); [apply gzA; [exact (Ladn y Iny) | reflexivity] | lia | lia]|].
      split; [intros a Ha Hay; pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Ha Iny Hay) as A; unfold apart in A |- *; lia|].
      split; [intros _; unfold apart in Ayo |- *; lia|].
      intros z Hz. exact (sub_node y z Iny Hz).
  Qed.

  Lemma step_pl : forall P x S' Bf M R nt, LREG P (x :: S') R -> LMEM P (x :: S') Bf M ->
    hh x <> hh (last P d0) -> Bf (hh x) <> 0 ->
    (Bf (hh x) = obj + 16 \/ exists y, In y P /\ Bf (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x) ->
    cell8 ASEGS M (Bf (hh x)) nt -> 0 <= nt < 2 ^ 64 ->
    STEPR R M (match S' with [] => R_EXIT | _ => R_LOOP end)
      (fun M' => munch [(Bf (hh x), Bf (hh x) + 8); (addr x, addr x + 8); (addr (last P d0), addr (last P d0) + 8)] M M'
                 /\ wmono asegs M M' /\ cell8 ASEGS M' (Bf (hh x)) (addr x) /\ cell8 ASEGS M' (addr x) nt
                 /\ cell8 ASEGS M' (addr (last P d0)) (hdaddr S'))
      (addr (last P d0)) (hdaddr S') (hh (last P d0)).
  Proof using All.
    intros P x S' Bf M R nt LR LM Hd Hb1 Hbor Cnt Hnt. 
    pose proof LR as [G2 G3 G4 G5 G6 G8 G9 G10 G11 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27].
    pose proof LM as [Lperm Lbinv LP Lp1 Lch Lhash Lbkt Ladp Ladh Ladn Lmu Lwm Lmi Lwrp Lwrh Lwrn].
    assert (Inx : In x ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; left; reflexivity]).
    assert (Inl : In (last P d0) ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; apply LbB_HRehK.last_in; exact LP]).
    assert (Hne0 : ents <> []) by (intro E0; rewrite E0 in Inx; exact Inx).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & Hx3 & Axo & Apx & Ox).
    destruct (nodeF _ Inl) as (Hl0 & Hl1 & Hl2 & Hl3 & Alo & Apl & Ol).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    destruct pF as (Hp0 & Hp16 & Hp8 & Hp1).
    assert (Hxl : addr (last P d0) <> addr x) by
      (apply (LbB_HRehK.nodup_app_ne P (x :: S') (last P d0) x);
       [exact (LbB_HRehK.perm_nodup obj bl bc ents A0 M0 _ U0 Lperm) | apply LbB_HRehK.last_in; exact LP | left; reflexivity]).
    pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Inl Inx Hxl) as Alx.
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    pose proof (hh_range Z n ltac:(lia) (last P d0)) as Hhl.
    pose proof (Lhash x Inx) as Cxh.
    pose proof (LbB_HRehK.chain_head_next M P x S' Lch) as Cxn.
    pose proof (Lbkt (hh x) Hhx) as Cbk.
    pose proof (Lwrn x Inx) as Wx. pose proof (Lwrn _ Inl) as Wl.
    assert (Wx8 : wr_at asegs M (addr x) 8) by (apply (wr_at_subE M (addr x) 24 (addr x) 8 Wx); lia).
    assert (Wl8 : wr_at asegs M (addr (last P d0)) 8) by (apply (wr_at_subE M _ 24 _ 8 Wl); lia).
    pose proof (gzA M (addr x) 24 (Ladn x Inx) eq_refl) as Gx.
    pose proof (gzA M _ 24 (Ladn _ Inl) eq_refl) as Gl.
    pose proof (gzA M p (8 * n) Ladp ltac:(rewrite Z.mul_comm; apply Z_mod_mult)) as Gp.
    pose proof (gzA M obj 40 Ladh eq_refl) as Go.
    assert (H14 : 2 <= bv_unsigned (getr R 14%bv) < 2 ^ 64) by
      (split; [exact G14 | pose proof (bv_unsigned_in_range 64 (getr R 14%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia]).
    assert (G11x : getr R 11%bv = Z_to_bv 64 (addr x)) by (rewrite G11; destruct x; reflexivity).
    unfold STEPR.
    destruct (bkt_facts P x S' Bf M LM Inx Hbor) as (Hb1' & Hb2 & Hb8 & Ob & Abl & Abx & Abp & Wb8 & Gb & _ & _ & _).
    pose proof Abx as Abx'; pose proof Abl as Abl'; pose proof Alx as Alx'; unfold apart in Abx', Abl', Alx'.
    destruct S' as [|y S''].
    - cbn [hdaddr] in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) (Bf (hh x)) p nt) SCR_kpx HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|].
        split; [rwcL HX Wb8|]. split; [rwcL HX Wx8|]. rwcL HX Wl8.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) (Bf (hh x)) p nt) SCR_rpx HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|].
        split; [rwcL HX Wb8|]. split; [rwcL HX Wx8|]. rwcL HX Wl8.
    - assert (Iny : In y ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; right; left; reflexivity]).
      destruct (nodeF y Iny) as (Hy0 & Hy1 & Hy2 & _).
      assert (Hny : hdaddr (y :: S'') = addr y) by (destruct y; reflexivity).
      rewrite Hny in Cxn |- *.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) (Bf (hh x)) (addr y) nt) SCR_kpl HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|].
        split; [rwcL HX Wb8|]. split; [rwcL HX Wx8|]. rwcL HX Wl8.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runS R M (valsL R (addr (last P d0)) (addr x) (hh (last P d0)) (hkey x) (Bf (hh x)) (addr y) nt) SCR_rpl HX G15.
        finS HX Lmi. split; [munchL HX|]. split; [apply wmono_mem_denot|].
        split; [rwcL HX Wb8|]. split; [rwcL HX Wx8|]. rwcL HX Wl8.
  Qed.

  Lemma loop_step : forall P x S' Bf M R, LREG P (x :: S') R -> LMEM P (x :: S') Bf M ->
    exists R' M' P' Bf', LMEM P' S' Bf' M' /\ (forall r, In r keptL -> getr R' r = getr R r)
      /\ ((S' = [] /\ CatSim.msteps asegs (st R R_LOOP M) (st R' R_EXIT M'))
          \/ (S' <> [] /\ CatSim.msteps asegs (st R R_LOOP M) (st R' R_LOOP M') /\ LREG P' S' R')).
  Proof using All.
    intros P x S' Bf M R LR LM. 
    pose proof LR as [G2 G3 G4 G5 G6 G8 G9 G10 G11 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27].
    pose proof LM as [Lperm Lbinv LP Lp1 Lch Lhash Lbkt Ladp Ladh Ladn Lmu Lwm Lmi Lwrp Lwrh Lwrn].
    assert (Inx : In x ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; right; left; reflexivity]).
    assert (Inl : In (last P d0) ents) by (eapply Permutation_in; [exact Lperm | apply in_or_app; left; apply LbB_HRehK.last_in; exact LP]).
    assert (Hne0 : ents <> []) by (intro E0; rewrite E0 in Inx; exact Inx).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & Hx3 & Axo & Apx & Ox).
    destruct (nodeF _ Inl) as (Hl0 & Hl1 & Hl2 & Hl3 & Alo & Apl & Ol).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    destruct pF as (Hp0 & Hp16 & Hp8 & Hp1).
    assert (Hxl : addr (last P d0) <> addr x) by
      (apply (LbB_HRehK.nodup_app_ne P (x :: S') (last P d0) x);
       [exact (LbB_HRehK.perm_nodup obj bl bc ents A0 M0 _ U0 Lperm) | apply LbB_HRehK.last_in; exact LP | left; reflexivity]).
    pose proof (LbB_HRehK.nodes_apart obj bl bc ents A0 M0 _ _ U0 Inl Inx Hxl) as Alx.
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    pose proof (hh_range Z n ltac:(lia) (last P d0)) as Hhl.
    pose proof (Lhash x Inx) as Cxh.
    pose proof (LbB_HRehK.chain_head_next M P x S' Lch) as Cxn.
    pose proof (Lbkt (hh x) Hhx) as Cbk.
    pose proof (Lwrn x Inx) as Wx. pose proof (Lwrn _ Inl) as Wl.
    assert (Wx8 : wr_at asegs M (addr x) 8) by (apply (wr_at_subE M (addr x) 24 (addr x) 8 Wx); lia).
    assert (Wl8 : wr_at asegs M (addr (last P d0)) 8) by (apply (wr_at_subE M _ 24 _ 8 Wl); lia).
    pose proof (gzA M (addr x) 24 (Ladn x Inx) eq_refl) as Gx.
    pose proof (gzA M _ 24 (Ladn _ Inl) eq_refl) as Gl.
    pose proof (gzA M p (8 * n) Ladp ltac:(rewrite Z.mul_comm; apply Z_mod_mult)) as Gp.
    pose proof (gzA M obj 40 Ladh eq_refl) as Go.
    assert (H14 : 2 <= bv_unsigned (getr R 14%bv) < 2 ^ 64) by
      (split; [exact G14 | pose proof (bv_unsigned_in_range 64 (getr R 14%bv)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; lia]).
    assert (G11x : getr R 11%bv = Z_to_bv 64 (addr x)) by (rewrite G11; destruct x; reflexivity).
   
    assert (PE : Permutation ((P ++ [x]) ++ S') ents) by (rewrite <- app_assoc; exact Lperm).
    assert (PN : P ++ [x] <> []) by (intro E0; apply app_eq_nil in E0; destruct E0 as [_ E0]; discriminate E0).
    assert (Hlx : last (P ++ [x]) d0 = x) by apply last_last.
    destruct (Z.eq_dec (hh x) (hh (last P d0))) as [Hs|Hd].
    - destruct (step_sl P x S' Bf M R LR LM Hs) as (R' & M' & MS & K & H10 & H11 & H16 & MI' & EQ). subst M'.
      assert (LM' : LMEM (P ++ [x]) S' Bf M).
      { apply (lmem_frame P (x :: S') Bf M (P ++ [x]) S' Bf M [] LM (munch_refl [] M) (wmono_refl asegs M) Lmi).
        - intros y _. exact I.
        - intros e _ y _. exact I.
        - constructor.
        - exact PE.
        - apply HRehashModel.step_same; [exact Lbinv | exact LP |].
          change (hh x = hh (@last (Z * (Z * Z)) P x)). rewrite (LbB_HRehK.last_any P x d0 LP). exact Hs.
        - exact PN.
        - rewrite <- app_assoc. exact Lp1.
        - rewrite <- app_assoc. exact Lch.
        - exact Lbkt. }
      exists R', M, (P ++ [x]), Bf. split; [exact LM'|]. split; [exact K|].
      destruct S' as [|y S'']; [left; split; [reflexivity | exact MS] | right; split; [discriminate|]; split; [exact MS|]].
      apply (lreg_step P (x :: y :: S'') R); [exact LR | exact K | rewrite Hlx; exact H10 | exact H11 | rewrite Hlx, Hs; exact H16].
    - destruct (Z.eq_dec (Bf (hh x)) 0) as [Hb0|Hb1].
      + destruct (step_el P x S' Bf M R LR LM Hd Hb0) as (R' & M' & MS & K & H10 & H11 & H16 & MI' & MU & WM & Cst).
        set (Bf' := fun i => if i =? hh x then addr (last P x) else Bf i).
        assert (LM' : LMEM (P ++ [x]) S' Bf' M').
        { apply (lmem_frame P (x :: S') Bf M (P ++ [x]) S' Bf' M' [(p + 8 * hh x, p + 8 * hh x + 8)] LM MU WM MI').
          - intros y Hy. cbn [outside]. split; [exact (sub_bkt (hh x) y Hhx Hy) | exact I].
          - intros e He y Hy. cbn [outside]. split; [|exact I].
            destruct (nodeF e He) as (_ & _ & _ & _ & _ & Ape & _). unfold apart in Ape. lia.
          - constructor; [cbn [fst snd]; unfold OSHR in Op; lia | constructor].
          - exact PE.
          - apply HRehashModel.step_empty; [exact Lbinv | exact LP | lia |].
            change (addr (@last (Z * (Z * Z)) P x) <> 0). rewrite (LbB_HRehK.last_any P x d0 LP). lia.
          - exact PN.
          - rewrite <- app_assoc. apply (cellw_agree ASEGS M M' sent 8%N _ Lp1); [| cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
            apply (agree_of_munch _ M M' sent 8 MU); [| lia | lia].
            intros y Hy. cbn [outside]. split; [pose proof HPO as A; unfold apart in A; lia | exact I].
          - rewrite <- app_assoc. apply LbB_HRehK.lnk_chain. apply (LbB_HRehK.lnk_agree M M' _ 0).
            + apply LbB_HRehK.lnk_chain. exact Lch.
            + intros a Ha. assert (Ia : In a ents) by (eapply Permutation_in; [exact Lperm | exact Ha]).
              destruct (nodeF a Ia) as (Ea0 & Ea1 & _ & _ & _ & Ape & _).
              apply (agree_of_munch _ M M' (addr a) 8 MU); [| lia | lia].
              intros y Hy. cbn [outside]. split; [unfold apart in Ape; lia | exact I].
            + intros a Ha. assert (Ia : In a ents) by (eapply Permutation_in; [exact Lperm | exact Ha]).
              destruct (nodeF a Ia) as (Ea0 & Ea1 & _). lia.
          - intros i Hi. unfold Bf'; cbv beta. destruct (Z.eq_dec i (hh x)) as [->|Hix].
            + rewrite Z.eqb_refl, (LbB_HRehK.last_any P x d0 LP). exact Cst.
            + rewrite (proj2 (Z.eqb_neq _ _) Hix).
              apply (cellw_agree ASEGS M M' (p + 8 * i) 8%N _ (Lbkt i Hi)); [| cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
              apply (agree_of_munch _ M M' (p + 8 * i) 8 MU); [| lia | lia].
              intros y Hy. cbn [outside]. split; [lia | exact I]. }
        exists R', M', (P ++ [x]), Bf'. split; [exact LM'|]. split; [exact K|].
        destruct S' as [|y S'']; [left; split; [reflexivity | exact MS] | right; split; [discriminate|]; split; [exact MS|]].
        apply (lreg_step P (x :: y :: S'') R); [exact LR | exact K | rewrite Hlx; exact H10 | exact H11 | rewrite Hlx; exact H16].
      + destruct (LbB_HRehK.splice_facts n obj bl bc ents A0 M0 P S' Bf x M U0 Lperm Lbinv LP Lp1 Lch Hhx Hb1)
          as (nt & P' & Cnt & Hnt & Hbor & HlP & P'ne & PE' & BI' & CONT).
        destruct (bkt_facts P x S' Bf M LM Inx Hbor) as (Hb1' & Hb2 & Hb8 & Ob & Abl & Abx & Abp & Wb8 & Gb & Hbn & Hbs & Hbw).
        destruct (step_pl P x S' Bf M R nt LR LM Hd Hb1 Hbor Cnt Hnt)
          as (R' & M' & MS & K & H10 & H11 & H16 & MI' & MU & WM & C1 & C2 & C3).
        assert (AG : forall a, In a (P ++ S') -> addr a <> addr (last P d0) -> addr a <> addr x -> addr a <> Bf (hh x) ->
                       agree_on M M' (addr a) 8).
        { intros a Ha Hal Hax Hab.
          assert (Ia : In a ents).
          { eapply Permutation_in; [exact Lperm|]. apply in_app_iff in Ha. apply in_or_app.
            destruct Ha as [Ha|Ha]; [left; exact Ha | right; right; exact Ha]. }
          destruct (nodeF a Ia) as (Ea0 & Ea1 & _). pose proof (Hbn a Ia Hab) as A1.
          apply (agree_of_munch _ M M' (addr a) 8 MU); [| lia | lia].
          intros y Hy. cbn [outside]. split; [unfold apart in A1; lia|].
          split; [exact (node_node a x y Ia Inx Hax Hy)|]. split; [exact (node_node a _ y Ia Inl Hal Hy) | exact I]. }
        assert (AGs : Bf (hh x) <> obj + 16 -> agree_on M M' (obj + 16) 8).
        { intros Hbs'. pose proof (Hbs Hbs') as A1.
          apply (agree_of_munch _ M M' (obj + 16) 8 MU); [| lia | lia].
          intros y Hy. cbn [outside]. unfold apart in A1, Axo, Alo. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
        destruct (CONT M' C1 C2 C3 AG AGs) as (Cs & Chn).
        assert (LM' : LMEM P' S' Bf M').
        { apply (lmem_frame P (x :: S') Bf M P' S' Bf M'
                   [(Bf (hh x), Bf (hh x) + 8); (addr x, addr x + 8); (addr (last P d0), addr (last P d0) + 8)] LM MU WM MI').
          - intros y Hy. cbn [outside]. split; [exact (Hbw y Hy)|].
            split; [exact (sub_node x y Inx Hy)|]. split; [exact (sub_node _ y Inl Hy) | exact I].
          - intros e He y Hy. cbn [outside].
            split; [|split; [exact (hash_node e x y He Inx Hy)|split; [exact (hash_node e _ y He Inl Hy) | exact I]]].
            destruct (Z.eq_dec (addr e) (Bf (hh x))) as [E|E]; [lia|].
            pose proof (Hbn e He E) as A. unfold apart in A. lia.
          - constructor; [cbn [fst snd]; unfold OSHR in Ob; lia|].
            constructor; [cbn [fst snd]; unfold OSHR in Ox; lia|].
            constructor; [cbn [fst snd]; unfold OSHR in Ol; lia | constructor].
          - exact (Permutation_trans PE' Lperm).
          - exact BI'.
          - exact P'ne.
          - exact Cs.
          - exact Chn.
          - intros i Hi. apply (cellw_agree ASEGS M M' (p + 8 * i) 8%N _ (Lbkt i Hi)); [| cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
            apply (agree_of_munch _ M M' (p + 8 * i) 8 MU); [| lia | lia].
            intros y Hy. cbn [outside]. unfold apart in Abp, Apx, Apl.
            split; [lia|]. split; [lia|]. split; [lia | exact I]. }
        exists R', M', P', Bf. split; [exact LM'|]. split; [exact K|].
        destruct S' as [|y S'']; [left; split; [reflexivity | exact MS] | right; split; [discriminate|]; split; [exact MS|]].
        apply (lreg_step P (x :: y :: S'') R); [exact LR | exact K | rewrite HlP; exact H10 | exact H11 | rewrite HlP; exact H16].
  Qed.

  Lemma relink : forall S P Bf M R, S <> [] -> LREG P S R -> LMEM P S Bf M ->
    exists R' M' P' Bf', CatSim.msteps asegs (st R R_LOOP M) (st R' R_EXIT M') /\ LMEM P' [] Bf' M'
                         /\ (forall r, In r keptL -> getr R' r = getr R r).
  Proof using All.
    intros S. induction S as [|x S' IH]; intros P Bf M R Hne LR LM; [contradiction|].
    destruct (loop_step P x S' Bf M R LR LM) as (R1 & M1 & P1 & Bf1 & LM1 & K1 & [[E1 MS1]|[NE1 [MS1 LR1]]]).
    - subst S'. exists R1, M1, P1, Bf1. split; [exact MS1|]. split; [exact LM1 | exact K1].
    - destruct (IH P1 Bf1 M1 R1 NE1 LR1 LM1) as (R2 & M2 & P2 & Bf2 & MS2 & LM2 & K2).
      exists R2, M2, P2, Bf2. split; [exact (CatSim.msteps_trans asegs _ _ _ MS1 MS2)|]. split; [exact LM2|].
      intros r Hr. rewrite (K2 r Hr). exact (K1 r Hr).
  Qed.
  Definition REGF (R : bvmap 5 word) : Prop :=
    getr R 2%bv = Z_to_bv 64 (spz - 64) /\ getr R 3%bv = gp /\ getr R 4%bv = tp /\ getr R 8%bv = Z_to_bv 64 n /\ getr R 9%bv = Z_to_bv 64 obj
    /\ getr R 18%bv = Z_to_bv 64 (obj + 8) /\ getr R 19%bv = Z_to_bv 64 SHBASE
    /\ getr R 20%bv = Z_to_bv 64 (obj / 8 + SHBASE) /\ getr R 21%bv = Z_to_bv 64 ((obj + 8) / 8 + SHBASE)
    /\ getr R 22%bv = s6 /\ getr R 23%bv = s7 /\ getr R 24%bv = s8 /\ getr R 25%bv = s9 /\ getr R 26%bv = s10 /\ getr R 27%bv = s11.
  Definition REGX (R : bvmap 5 word) : Prop :=
    getr R 2%bv = Z_to_bv 64 (spz - 64) /\ getr R 3%bv = gp /\ getr R 4%bv = tp
    /\ getr R 22%bv = s6 /\ getr R 23%bv = s7 /\ getr R 24%bv = s8 /\ getr R 25%bv = s9 /\ getr R 26%bv = s10 /\ getr R 27%bv = s11.

  Definition KNMS : list kentry := [KRange (EVar 32) 1 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 35) 3 (2 ^ 25);
    KRange (EVar 33) AIMG_TOP (2 ^ 47); KAlign (EVar 33) 8; KRange (EVar 37) 1 (2 ^ 47); KAlign (EVar 37) 16;
    KRange (EVar 40) 0 (2 ^ 32); KRange (EVar 42) 1 (2 ^ 47); KAlign (EVar 42) 16].
  Definition KNMS0 : list kentry := [KRange (EVar 33) AIMG_TOP (2 ^ 47); KAlign (EVar 33) 8].
  Definition srMS : list expr := srs sr_id [(8%bv, EVar 35); (19%bv, ELit SHBASE); (9%bv, EVar 33);
    (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit SHBASE))].
  Definition SCR_memp := SCR [] [ELit 0] [].
  Definition SCR_mkl := SCR [true; true; false] [EVar 37; EVar 40; EVar 32; EVar 42] [].
  Definition SCR_mkx := SCR [true; true; false] [EVar 37; EVar 40; EVar 32; ELit 0] [].
  Definition SCR_mrl := SCR [true; false; false; false] [EVar 37; EVar 40; EVar 32; EVar 42] [].
  Definition SCR_mrx := SCR [true; false; false; false] [EVar 37; EVar 40; EVar 32; ELit 0] [].
  Definition valsM (a32 a33 a35 a37 a40 a42 : Z) : list word :=
    [Z_to_bv 64 a32; Z_to_bv 64 a33; Z_to_bv 64 0; Z_to_bv 64 a35; Z_to_bv 64 0; Z_to_bv 64 a37; Z_to_bv 64 0;
     Z_to_bv 64 0; Z_to_bv 64 a40; Z_to_bv 64 0; Z_to_bv 64 a42; Z_to_bv 64 0].

  Definition popcM : expr :=
    Eval vm_compute in
      (let '(ss, _, _) := sym_exec asegs 400 true L_STOPS SCR_mkl
                            (SS R_MS srMS [] (kn_fix 30%nat L_STOPS SCR_mkl R_MS srMS KNMS 60%N) 60%N) [] in
       sr_get (s_regs ss) 14%bv).
  Definition popcwM (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcM.
  Lemma popcM_env : forall E, edenot E popcM = popcwM (ev E 35).
  Proof. intros E. unfold popcwM, popcM. cbn [edenot ev]. reflexivity. Qed.
  Ltac vm_popcM :=
    match goal with |- context [bv_unsigned (popcwM ?w)] =>
      let v := eval vm_compute in (bv_unsigned (popcwM w)) in
      replace (bv_unsigned (popcwM w)) with v by (vm_compute; reflexivity) end.
  Lemma popcwM_ge2 : forall c, In c BSEQ -> 3 <= c -> 2 <= bv_unsigned (popcwM (Z_to_bv 64 c)).
  Proof.
    intros c Hin Hc. unfold BSEQ in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [exfalso; lia | vm_popcM; lia] |]).
    destruct Hin.
  Qed.

  Lemma sh_wordL : forall x, 0 <= x < 2 ^ 64 ->
    alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SHBASE) = Z_to_bv 64 (x / 8 + SHBASE).
  Proof.
    intros x Hx. rewrite w_srlR by lia. change (2 ^ 3) with 8.
    assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHBASE. rewrite w_add by lia. reflexivity.
  Qed.

  Lemma lreg_first : forall R R' x S', REGF R -> (forall r, In r keptM -> getr R' r = getr R r) ->
    2 <= bv_unsigned (getr R' 14%bv) ->
    getr R' 5%bv = Z_to_bv 64 1 -> getr R' 6%bv = Z_to_bv 64 (2 ^ 60) ->
    getr R' 10%bv = Z_to_bv 64 (addr x) -> getr R' 11%bv = Z_to_bv 64 (hdaddr S') ->
    getr R' 15%bv = Z_to_bv 64 (n - 1) -> getr R' 16%bv = Z_to_bv 64 (hh x) -> getr R' 17%bv = Z_to_bv 64 p ->
    LREG [x] S' R'.
  Proof.
    intros R R' x S' RF K H14 H5 H6 H10 H11 H15 H16 H17.
    destruct RF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    constructor; cbn [last];
      first [ assumption | match goal with |- getr R' ?r = _ => rewrite (K r) by inb; assumption end ].
  Qed.

  Lemma lmem_first : forall x S' M', ents = x :: S' ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    (forall i, 0 <= i < n -> cell8 ASEGS ML (p + 8 * i) 0) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 24) ->
    wr_at asegs ML p (8 * n) -> wr_at asegs ML obj 40 -> (forall e, In e ents -> wr_at asegs ML (addr e) 24) ->
    munch [(p + 8 * hh x, p + 8 * hh x + 8)] ML M' -> wmono asegs ML M' -> mem_inv asegs M' ->
    cell8 ASEGS M' (p + 8 * hh x) sent ->
    LMEM [x] S' (fun i => if i =? hh x then sent else 0) M'.
  Proof using All.
    intros x S' M' Ee C1 CH HKs BK ADP ADH ADN WRP WRH WRN MU WM MI Cst.
    assert (Hne0 : ents <> []) by (rewrite Ee; discriminate).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct pF as (Hp0 & _ & _ & Hp1). destruct objF as (Ho0 & _ & Ho1 & _ & Op).
    destruct n_factsL as (N0 & N1 & N2 & N3).
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    pose proof HPO as Apo. unfold apart in Apo.
    assert (FW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(p + 8 * hh x, p + 8 * hh x + 8)])
      by (constructor; [cbn [fst snd]; unfold OSHR in Op; lia | constructor]).
    constructor.
    - rewrite Ee. apply Permutation_refl.
    - apply (HRehashModel.binv_start Z n (obj + 16) x); lia.
    - discriminate.
    - change (hdaddr ([x] ++ S')) with (hdaddr (x :: S')). rewrite <- Ee.
      apply (cellw_agree ASEGS ML M' sent 8%N _ C1); [| cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
      apply (agree_of_munch _ ML M' sent 8 MU); [| lia | lia].
      intros y Hy. cbn [outside]. split; [lia | exact I].
    - change ([x] ++ S') with (x :: S'). rewrite <- Ee.
      apply LbB_HRehK.lnk_chain. apply (LbB_HRehK.lnk_agree ML M' _ 0).
      + apply LbB_HRehK.lnk_chain. exact CH.
      + intros a Ha. destruct (nodeF a Ha) as (Ea0 & Ea1 & _ & _ & _ & Ape & _).
        apply (agree_of_munch _ ML M' (addr a) 8 MU); [| lia | lia].
        intros y Hy. cbn [outside]. split; [unfold apart in Ape; lia | exact I].
      + intros a Ha. destruct (nodeF a Ha) as (Ea0 & Ea1 & _). lia.
    - intros e He. destruct (nodeF e He) as (E0 & E1 & _ & _ & _ & Ape & _).
      apply (cellw_agree ASEGS ML M' (addr e + 8) 8%N (hkey e) (HKs e He)); [| cbn; lia | cbn; lia].
      apply (agree_of_munch _ ML M' (addr e + 8) 8 MU); [| lia | lia].
      intros y Hy. cbn [outside]. split; [unfold apart in Ape; lia | exact I].
    - intros i Hi. cbv beta. destruct (Z.eq_dec i (hh x)) as [->|Hix].
      + rewrite Z.eqb_refl. exact Cst.
      + rewrite (proj2 (Z.eqb_neq _ _) Hix).
        apply (cellw_agree ASEGS ML M' (p + 8 * i) 8%N _ (BK i Hi)); [| cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
        apply (agree_of_munch _ ML M' (p + 8 * i) 8 MU); [| lia | lia].
        intros y Hy. cbn [outside]. split; [lia | exact I].
    - apply (addressable_transport _ ML M' p (8 * n) ADP MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - apply (addressable_transport _ ML M' obj 40 ADH MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - intros e He. destruct (nodeF e He) as (E0 & E1 & _).
      apply (addressable_transport _ ML M' (addr e) 24 (ADN e He) MU WM). apply dsh_app; [exact FW | lia | lia | lia].
    - apply (munch_weaken [(p + 8 * hh x, p + 8 * hh x + 8)] WL ML M'); [| exact MU].
      intros y Hy. cbn [outside]. split; [exact (sub_bkt (hh x) y Hhx Hy) | exact I].
    - exact WM.
    - exact MI.
    - exact (wr_at_wmono ML M' p (8 * n) WRP WM).
    - exact (wr_at_wmono ML M' obj 40 WRH WM).
    - intros e He. exact (wr_at_wmono ML M' (addr e) 24 (WRN e He) WM).
  Qed.

  Ltac regsM := apply regs_ok_srs; [apply regs_ok_seed|];
    repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; cbn [edenot];
      first [reflexivity | assumption | (rewrite sh_wordL by lia; assumption)]] |]); apply Forall_nil.
  Ltac sc_sltuM HX :=
    lazymatch goal with
    | |- sc_denot _ _ _ (SCBr false BC_EQ (ELit 1) (EAlu ALU_SLTU _ (ELit 1))) =>
        cbn [sc_denot]; evs; cbn [edenot]; nrmL HX; rewrite HWord.w_sltu by lia;
        rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity
    end.
  Ltac runM R M vals scr kn HX :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in let Hpc := fresh "Hpc" in
    let vs := eval unfold valsM in vals in
    pose (E := Eseed R vs);
    assert (HR : regs_ok E srMS R) by regsM;
    assert (HK : know_ok asegs E M (kn_fix 30%nat L_STOPS scr R_MS srMS kn 60%N)) by (kn_eval; knL HX);
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popcM) = b ->
                  sc_denot asegs M E (SCBr b BC_LTU (ELit 1) popcM)) by (intros b Hb; exact Hb);
    xrun_at (PropExec.mkFP F fc) asegs R R_MS M (seg_rom asegs) HR HK 400%nat L_STOPS scr 60%N;
    [ split_scs; first [ apply Hpc; rewrite popcM_env; evs; rewrite branch_ltu_lit_l by lia; bool_lia
                       | sc_sltuM HX
                       | scL HX ]
    | ].
  Ltac regM HR' HX :=
    lazymatch goal with |- getr _ ?r = _ =>
      let G := fresh "G" in rreg HR' r G; rewrite G; nrmL HX; rewrite ?w_addm by lia;
      first [reflexivity | f_equal; lia]
    end.
  Ltac finM HX MI Wh8 RF Hp2 :=
    lazymatch goal with
    | Hms : CatSim.msteps _ (@PropExec.mkst _ ?R _ ?M0 _) (@PropExec.mkst _ ?R' _ ?mm _) |- _ =>
    lazymatch goal with
    | HR : regs_ok ?E _ R, HR' : regs_ok ?E _ R', Hlf : log_flat ?E ?lg |- _ =>
        change mm with (mem_denot E M0 lg) in Hms;
        let K := fresh "K" in let G14 := fresh "G14" in let NE := fresh "NE" in
        assert (K : forall r, In r keptM -> getr R' r = getr R r) by
          (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
           refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ keptM HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true));
        assert (G14 : getr R' 14%bv = popcwM (Z_to_bv 64 n)) by exact (eq_trans (HR' 14%bv) (popcM_env E));
        exists R', (mem_denot E M0 lg); split; [exact Hms|]; split; [exact K|];
        split; [munchL HX|]; split; [apply wmono_mem_denot|]; split; [exact (msteps_mem_inv asegs _ _ Hms MI)|];
        split; [rwcL HX Wh8|];
        intros NE;
        first [ exfalso; apply NE; reflexivity
              | apply (lreg_first R R' _ _ RF K); [rewrite G14; exact Hp2 | regM HR' HX ..] ]
    end end.

  Lemma first_emp : forall R, REGF R -> ents = [] -> cell8 ASEGS ML sent (hdaddr ents) -> addressable ML obj 40 ->
    exists R', CatSim.msteps asegs (st R R_MS ML) (st R' R_EXIT ML) /\ (forall r, In r keptM -> getr R' r = getr R r).
  Proof using All.
    intros R RF Ee C1 ADH. rewrite Ee in C1. cbn [hdaddr] in C1.
    pose proof RF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    assert (Hob : AIMG_TOP <= obj) by (clear - OAPP; unfold aapp, aapp_lo, aapp_hi, AHI_LO, AIMG_TOP in *; lia).
    unfold AIMG_TOP in Hob.
    pose proof (gzA ML obj 40 ADH eq_refl) as Go.
    assert (HX : Z.succ 0 = 1) by reflexivity.
    runM R ML (valsM 0 obj n 0 0 0) SCR_memp KNMS0 HX.
    lazymatch goal with
    | Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R' _ _ _), HR : regs_ok ?E _ R, HR' : regs_ok ?E _ ?R' |- _ =>
        exists R'; split; [exact Hms|];
        intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ keptM HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)
    end.
  Qed.

  Lemma first_ne : forall R x S', REGF R -> ents = x :: S' ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    cell8 ASEGS ML obj p -> addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 24) ->
    mem_inv asegs ML -> wr_at asegs ML p (8 * n) ->
    exists R' M', CatSim.msteps asegs (st R R_MS ML) (st R' (match S' with [] => R_EXIT | _ => R_LOOP end) M')
      /\ (forall r, In r keptM -> getr R' r = getr R r)
      /\ munch [(p + 8 * hh x, p + 8 * hh x + 8)] ML M' /\ wmono asegs ML M' /\ mem_inv asegs M'
      /\ cell8 ASEGS M' (p + 8 * hh x) sent /\ (S' <> [] -> LREG [x] S' R').
  Proof using All.
    intros R x S' RF Ee C1 CH HKs CO ADP ADH ADN MI WRP.
    pose proof RF as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    assert (Inx : In x ents) by (rewrite Ee; left; reflexivity).
    assert (Hne0 : ents <> []) by (rewrite Ee; discriminate).
    destruct (nF Hne0) as (Hn3 & Hn25 & Hbc).
    destruct (nodeF x Inx) as (Hx0 & Hx1 & Hx2 & Hx3 & Axo & Apx & Ox).
    destruct objF as (Ho0 & Ho8 & Ho1 & Oo & Op).
    destruct pF as (Hp0 & Hp16 & Hp8 & Hp1).
    destruct n_factsL as (N0 & N1 & N2 & N3).
    assert (Hob : AIMG_TOP <= obj) by (clear - OAPP; unfold aapp, aapp_lo, aapp_hi, AHI_LO, AIMG_TOP in *; lia).
    unfold AIMG_TOP in Hob.
    pose proof (hh_range Z n ltac:(lia) x) as Hhx.
    assert (C1x : cell8 ASEGS ML (obj + 16) (addr x)) by (rewrite Ee in C1; destruct x; exact C1).
    clear C1.
    pose proof (HKs x Inx) as Cxh.
    assert (Cxn : cell8 ASEGS ML (addr x) (hdaddr S')) by (rewrite Ee in CH; exact (LbB_HRehK.chain_head_next ML [] x S' CH)).
    assert (Wh8 : wr_at asegs ML (p + 8 * hh x) 8) by (apply (wr_at_subE ML p (8 * n) (p + 8 * hh x) 8 WRP); lia).
    pose proof (gzA ML (addr x) 24 (ADN x Inx) eq_refl) as Gx.
    pose proof (gzA ML p (8 * n) ADP ltac:(rewrite Z.mul_comm; apply Z_mod_mult)) as Gp.
    pose proof (gzA ML obj 40 ADH eq_refl) as Go.
    pose proof (bv_unsigned_in_range 64 (popcwM (Z_to_bv 64 n))) as PWR. change (bv_modulus 64) with (2 ^ 64) in PWR.
    pose proof (popcwM_ge2 n N0 Hn3) as Hp2.
    destruct S' as [|y S''].
    - cbn [hdaddr] in Cxn.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runM R ML (valsM p obj n (addr x) (hkey x) p) SCR_mkx KNMS HX.
        finM HX MI Wh8 RF Hp2.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runM R ML (valsM p obj n (addr x) (hkey x) p) SCR_mrx KNMS HX.
        finM HX MI Wh8 RF Hp2.
    - assert (Iny : In y ents) by (rewrite Ee; right; left; reflexivity).
      destruct (nodeF y Iny) as (Hy0 & Hy1 & Hy2 & _).
      assert (Hny : hdaddr (y :: S'') = addr y) by (destruct y; reflexivity).
      rewrite Hny in Cxn.
      destruct (Z.ltb_spec (hkey x) n) as [Hk|Hk].
      + assert (HX : hkey x mod n = hkey x) by (apply Z.mod_small; lia). assert (Hhk : hh x = hkey x) by exact HX.
        runM R ML (valsM p obj n (addr x) (hkey x) (addr y)) SCR_mkl KNMS HX.
        finM HX MI Wh8 RF Hp2.
      + assert (HX : hkey x mod n = hh x) by reflexivity.
        runM R ML (valsM p obj n (addr x) (hkey x) (addr y)) SCR_mrl KNMS HX.
        finM HX MI Wh8 RF Hp2.
  Qed.

  Lemma loop_all : forall R, REGF R ->
    cell8 ASEGS ML sent (hdaddr ents) -> chain ASEGS ML ents -> (forall e, In e ents -> cell8 ASEGS ML (addr e + 8) (hkey e)) ->
    cell8 ASEGS ML obj p -> (forall i, 0 <= i < n -> cell8 ASEGS ML (p + 8 * i) 0) ->
    addressable ML p (8 * n) -> addressable ML obj 40 -> (forall e, In e ents -> addressable ML (addr e) 24) ->
    mem_inv asegs ML -> wr_at asegs ML p (8 * n) -> wr_at asegs ML obj 40 -> (forall e, In e ents -> wr_at asegs ML (addr e) 24) ->
    exists R' M', CatSim.msteps asegs (st R R_MS ML) (st R' R_EXIT M') /\ REGX R'
      /\ ((ents = [] /\ M' = ML) \/ (exists P' Bf', LMEM P' [] Bf' M')).
  Proof using All.
    intros R RF C1 CH HKs CO BK ADP ADH ADN MI WRP WRH WRN.
    assert (RX : forall R', (forall r, In r keptM -> getr R' r = getr R r) -> REGX R').
    { intros R' K. destruct RF as (G2 & G3 & G4 & _ & _ & _ & _ & _ & _ & G22 & G23 & G24 & G25 & G26 & G27).
      unfold REGX. repeat match goal with |- _ /\ _ => split end; (rewrite K by inb; assumption). }
    assert (KM : forall r, In r keptM -> In r keptL) by (intros r Hr; unfold keptM, keptL in *; cbn [In] in *; tauto).
    assert (Hc : forall l : list ent, l = [] \/ exists x S', l = x :: S')
      by (intros [|x S']; [left; reflexivity | right; exists x, S'; reflexivity]).
    destruct (Hc ents) as [E0|(x & S' & E0)].
    - destruct (first_emp R RF E0 C1 ADH) as (R' & MS & K).
      exists R', ML. split; [exact MS|]. split; [exact (RX R' K)|]. left. split; [exact E0 | reflexivity].
    - destruct (first_ne R x S' RF E0 C1 CH HKs CO ADP ADH ADN MI WRP) as (R1 & M1 & MS1 & K1 & MU & WM & MI1 & Cst & LR1).
      pose proof (lmem_first x S' M1 E0 C1 CH HKs BK ADP ADH ADN WRP WRH WRN MU WM MI1 Cst) as LM1.
      destruct S' as [|y S''].
      + exists R1, M1. split; [exact MS1|]. split; [exact (RX R1 K1)|]. right. eexists; eexists. exact LM1.
      + assert (NE : y :: S'' <> []) by discriminate.
        destruct (relink (y :: S'') [x] _ M1 R1 NE (LR1 NE) LM1) as (R2 & M2 & P2 & Bf2 & MS2 & LM2 & K2).
        exists R2, M2. split; [exact (CatSim.msteps_trans asegs _ _ _ MS1 MS2)|].
        split; [apply RX; intros r Hr; rewrite (K2 r (KM r Hr)); exact (K1 r Hr)|].
        right. exists P2, Bf2. exact LM2.
  Qed.
End RehL.
