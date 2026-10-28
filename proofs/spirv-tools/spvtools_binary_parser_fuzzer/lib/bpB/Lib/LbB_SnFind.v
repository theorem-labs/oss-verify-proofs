(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare RefMemcpyLib LibIface SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HLib HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_HFind2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_SnFind () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib@bv_swrap32_casesC4ARocqVerifyHarness?AgentSubmission8PropExec=bv_wrap64_modC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3sxwK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind@sxw_unsigned_modC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C45stdpp9bitvector;definitions6bv_mulC45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3divC47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3mulC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitions?bv_and_unsignedC45stdpp9bitvector;definitions?bv_mul_unsignedC45stdpp9bitvector;definitions9bv_shiftrC45stdpp9bitvector;definitionsBbv_shiftr_unsignedC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_mult_compK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrI47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics5Riscv3Sem5low32C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedK47Corelib7Numbers7BinNums1N01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit3sh0C4ARocqVerifyHarness?AgentSubmission8LibIface3memC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6hdaddrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5chainI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep3hdr00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind2>in_split_entsAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind2=hdaddr_casesAC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind2;BSEQ_boundAC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind5keptSC46Stdlib5Lists4List2InK45stdpp9bitvector;definitions2bv01C4ARocqVerifyHarness?AgentSubmission8PropExec4getrK47Corelib4Init5Logic3and01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind8non_argSK47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6aonlyTI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8non_argTC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7syms_idC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=syms_id_soundI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00C47Corelib4Init5Logic3notC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind26popcwAC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4hmodI47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7ZlengthC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell4C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7definedC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep8u_obj_hiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind2<popcwA_casesI5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_hdrC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_bseqC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_andK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_addmK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib<regs_ok_seedC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6reg_evK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib;regs_ok_srsK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind4KNSAC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C56Stdlib6ZArith6BinInt1Z6ltb_geC4ARocqVerifyHarness?AgentSubmission7SymRun3@branch_ltu_lit_lC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind29popcA_envC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC4ARocqVerifyHarness?AgentSubmission8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8v_addi_ZC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26adenotC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib=sc_read_cellwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib7sc_flatC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_eqC35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit:div8_boundC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC4ARocqVerifyHarness?AgentSubmission7SymRun39run_soundC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind=keptS_of_symsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC47Corelib4Init5Logic8eq_transc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9zx_of_sxwK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_ltuK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr06C4ELinuxProcessSemantics5Riscv7Prelude4sextC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind2:remuw_valAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9low32_sxwc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind5atBBsI4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cell8C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SNF_ENTRYc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind4srSAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6SNF_BBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind7bc_rngSK4ELinuxProcessSemantics5Riscv5Instr5aluop0:C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4BSEQI5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6SCRS_2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind25popcAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SNF_STOPSI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind7SCRS_ltc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind7SCRS_geK4ELinuxProcessSemantics5Riscv5Instr5mulop08C56Stdlib6ZArith6BinInt1Z6eqb_eqc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind<SNF_NOTFOUNDc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind8SCRS_bc0C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_loC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_bl_hiC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5w_mulC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind4KNSxI47Corelib4Init9Datatypes6option00C4ARocqVerifyHarness?AgentSubmission8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic5proj1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind7atLoopSC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z;le_gt_casesC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6br_geuC46Stdlib4Bool4Bool>negb_false_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind4srSBC46Stdlib9micromega8ZifyInst7Inj_Z_Zc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6SNF_LMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6SNF_LPc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SCRS_B_b0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SCRS_B_q0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind8SCRS_B_mK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind8SCRS_B_pC46Stdlib5Lists4List:in_app_iffC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6u_nodeC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5apartC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep7u_chainc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind;node_factsSC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5cellwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib9br_ne_sxwC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib@sc_read_cell4_sxK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5br_neC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib6w_remuC46Stdlib5Lists4List9app_assocc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind;keptS_transC4ARocqVerifyHarness?AgentSubmission6CatSim<msteps_transc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind5walkSc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind4srSLK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SNF_FOUNDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_HFind27land_1Ac6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6blkSA0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind<keptS_aonlyTc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind5blkSAC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5u_bktC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep9bucket_okC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5hdkeyc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind7gz_subSC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep4h_p1C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind5blkSBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6loopSMc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind6loopSPc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind;snfind_stmtc6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind>snfind_correctI4ARocqVerifyHarness?AgentSubmission8LibIface;MallocIface00C4ARocqVerifyHarness?AgentSubmission8LibIface2ASC4ARocqVerifyHarness?AgentSubmission8PropExec7seg_romI4ARocqVerifyHarness?AgentSubmission9AllocCeil<AllocCeiling00I4ARocqVerifyHarness?AgentSubmission8LibIface6Layout00I4ARocqVerifyHarness?AgentSubmission8PropExec7FPState00C5ARocqVerifyHarness?AgentSubmission6LibPrs:PrsGrammar4sx32".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition SNF_ENTRY : Z := 0xf96a8.
Definition SNF_BB : Z := 0xf9768.
Definition SNF_LP : Z := 0xf97d4.
Definition SNF_LM : Z := 0xf9850.
Definition SNF_FOUND : Z := 0xf9b24.
Definition SNF_NOTFOUND : Z := 0xf98d0.
Definition SNF_STOPS : list Z := [SNF_BB; SNF_LP; SNF_LM; SNF_FOUND; SNF_NOTFOUND].

Definition SNF_OBJ : Z := 136.

Definition srSA : list expr := srs sr_id [(10%bv, EVar 36); (21%bv, EVar 32); (20%bv, EVar 33); (24%bv, ELit SHBASE)].

Definition popcS : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec ASEGS 100 true SNF_STOPS (SCR [false; false] [EVar 34; EVar 35] [])
                          (SS SNF_ENTRY srSA [] [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 136)) (ELit 3)) SHBASE) 1 (ELit 0)] 50) [] in
     sr_get (s_regs ss) 11%bv).

Lemma sxw_unsigned_mod : forall k, 0 <= k < 2 ^ 32 -> bv_unsigned (sxw k) mod 2 ^ 32 = k.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) [] "p'0h04__x1h17__arithh26__sat0h36__sat1h41zh52Hah66__sat2h76__sat3h84__ffh98__varmaph:5__with;6__sat4h<6__sat5h=1Hh>2H0h?2Hkh@1bi001bhA2b0hB1kp;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8p1000ep4p710g001BR0p4p710p8g001^j18Tg002Cj19Tg002aj2FTg003>j23Tg003Zj2=Tg0045j1NTg004Sj2[Tg005:j2XTg005`j21Tg006@j1;Tg006ej2ITg007Bj24Tg007_j2jTg008Aj2>Tg008]R1j3hTg009Aj2ETg009ij3DTg00:Mj1_Tg00:mj1]Tg00;Mj2\Tg00;kj1ZTg00<Ij1YTg00=4j2<Tg00=Wj2WTg00>:j4:Tg00>ej3JTg00?Hj1VTg00?jj2UTg00@Lj2TTg00@fj2STg00ARj3HTg00Alj3QTg00BKj4RTg00C=j3?Tg00C`j3GTg00DCj3BTg00Dfj1iTg00EDj3PTg00Egj22Tg00FDj2OTg00Faj3KTP0j6LTg00GFj2gTg00HHj1fTg00ICj2eTg00Iij2MTg00JSj2aTg00KBj1bTg00L7j7`Tg00L[j7cTg00M?j8dTg00Mcj6^Tg00NAR0f0R2'>p=5g00N_R3f1R4;H2p=0P4g00O=R5g00O\R6P6g00P<R7P2g00P\F`p=7P3P4g00Q<P2C:p=Af2R8P5P6P6P7P4P2Fcp=Cf3R9P5P6P6P7P8P4P2Gdp=@P3f4R5P9P8P4P2E^p=6%52g00QcR:#8R;#9R<%8;#8#8#8R;#9R='FR>,32'=R?%8;R@#NRA%N;R;/[4RB'XRC112>RD/08X43RE%9@R@,F<RF,1BPEg00RHREP3%;:#;#;#;#9RG,F<RH,I4RIP4144>n0100000020000112F/1>RJ/08X431j4H134H1>H4;hI1I8HPEP1139H1>H9PEP3P4f5R1141>RIn0100000020000/1F/1>/01P4135HP1f6RK,0DX431E<=RL130<RM%5=130>[[RN%5<ROg00RhRPAD<=4UW5R=%5>\P^5ORQ1E<GRR%5G130H[\MRSAD<G4VPX5ORG%5H\P^5ORTg00SDRU#_RV%]URU1\34RW%Z3RX%Y3RYP31<30RZg00T0R[1W3:R\C:,7YR]1<3<R^=J3;R;,A\,7Y5CYR_%V6R6P_C@1UY7R7P2P8g00TWR`,TE1S28=HE`dAQ304CRR`b8b9b:X03RE%54R8134>'=\?^03RaP2f:f9O2b1b2b3b6b79?1>111FPLPNP=PQ1E<@Rb%5@130F[\MRMAD<@4VPX5OR@%5F\P^5OROPRPSPGPTPVPUPWPXPYP_P6AJ3^AR^,A\,7Y9CY]C@P7P`b8b9b:X03134F,=8\?^03P2f<R8f;O2R]b1b2b3b6b7b;b<9?1FD6W=P2O11>H5PLPNP=PQPbPMP@POPRPSPGPTPVPUPWPXP3AG3\^=B3;RH%i:RP,<3=P3^5G3g00U7R<AB3\;C:,7YP7P`b8b9b:X03122F/4>R01OPFRc'2142>'0^03P2P8O1b1b2b3b6b7b;b<121F/4>/2c/0IP312KF/4>RI/2cRcf7R1,0JX4311IFRJ10D1X43RdPIPdPLPNP=PQPbPMP@POPRPSPGPTPVPUPWPXP3%9:R:,<39B3;=P3;9G3\P<PHC:,7YP7P`b8b9b:X0314>:R:/O>R<,22/00^03P2f=R0O1b1b2b3b6b7b;b<12K</0IP3121<R<f8R\,0DX43111>102\X43PLPNP=PQPRPSPGPTPEPaP]b1b2b3b6b79?1>11<>AK1:>D6121F/4>P2ELb>PJPLPNP=PQPbPMP@POPRPSPGPTPVPUPWPXPYP_P6P3PZP[PHC:,7Y1AH^,7Y5CYC@P7P`b8b9b:X03124F/4>R`#513`F'=\?^03P2P0P8O2b1b2b3b6b7b;b<9?IFD611cFAKIPFD614K>P2ELb>W=P2O1n200210000000021100011000bAb@PBPLPNP=PQPEPaP2P5P9O2b1b2b3,g4D6PC%fBD61eAB,MA1aABD6%b4,MA/1>/04eW?XB3o"). Qed.
Lemma zx_of_sxw : forall k, 0 <= k < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (sxw k)) (Z_to_bv 64 32) = Z_to_bv 64 k.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) [] "p'0h01zh17__arithh24__ffh38__varmaph45__with56__sat0h66__sat1h74__x1h82Hah94__x2h:6__sat2h;6__sat3h<6__sat4h=5heq_xh>1Hh?4__p1h@4__p2hA6__sat5hB4__x3hC2b1hD2b2hE1nhF1xi001xhG1yi011yhH1EhI2EMhJ2HkhK1RhL1ahM1bhN1khO5lemmai022x'i032y'p%0p&0p;1p;2p;3p;4p;;p;:p;9p;6p;7p;8g001^j1>Tg002Cj1BTg002aj2hTg00U^k205Tg0045j1^Tg00KBj1ETg00Iij24Tg005`R0j21Tg00Vfj2jTg00WYk10OTg00XBj1LTg00ARj3<j1rTg00Xek30>Tg00ICj2MTg00YIk404Tg00Z3k302Tg00Z[j3}Tg006@j1GTg00[@j3zTg00[ej2UTg00FDR1j20Tg005:j27Tg00\Ej29Tg00\cj2ATg00EgR2j2:Tg00]@j1pTg00^0j2oTg00Dfj1nTg00^Qj2kTg00_>j4RTg00_ej1iTg00`Tj4[Tg00aKk30NTg00bAj2ZTg00bmm;0LTg00chm:0KTg00dUm90ETg009Aj2fTg003>j2KTg009ij3eTg00:Mk10=Tg00:mk10<Tg00eOk10;Tg00;kk107Tg00<Ik106Tg00=4j2ITg00>ej3dTg00?jk203Tg00@Lj2WTg00@fk201Tg00Alk300Tg00BKj4~Tg00emj3|Tg00fNj2{Tg00g?j2STg00;Mj2VTg00h0j4aTg00=Wj2TTg00EDj3PTg00C`j3`Tg00hNj2yTg00i7j1FTg00iVj2NTg00j?j3xTg00jhj3XTg00kQj2_Tg00l=j2wTg00lij3bTg00?Hj1vTg003ZR3j2\Tg00C=j3HTg00Faj3uTg001Bj6tTg00mIj4sTg00mek309Tg00nFk20:Tg00nhj3qTg00HHj1JTg00JSj2OTg00oQk30?Tg010?k30@Tg010mk30ATg011Uk30BTg008Ak20CTg012Fm90DTg012nl:mTg00>:j4YTg00L7j7gTg013Yk60FTg00M?k80GTg014=k60HTg00L[k70ITg00Mck60JTg00NAR4f0R5+0Cp=2%>5#>#>#>p=Cf2R6f1R7/K5'\p=?g00N_R8?<75p=5%>5#>p>081U67=<85p=6P8P4P6P2P7g007BR9g014aR:P5g015>R;N90Dp=lP8P4P6P2P7P9P:P5P;g015gM:mp>0MP8P7g00U7P5CYp=QP7g00O=R;g00O\R:P:g00P<R9P5g00P\R2Fgp=8P7P;P:P:P9P5J0Fp=cP6P;P:P:P9P8P7g00T0P5CYP2Fgp=;f3R2P;P:P:P9P6P7P5L0Gp=@P7P;P:P:P9P5J0Hp=]P6P;P:P:P9P7P5K0Ip==P8P7g00Q<P5CYp=DP8f4R;P2P6P7P5J0Jp=3%25g00QcR<#>R=#BR>%C=R?#BR@'hRA7?5RB20575%>?RC#^RD%E7'4/1A/57%E6RE,jD14DERE#2&0OD7?E%E2,4DP8g016NRE%L5RF%L7RGP3%L6?<7514261427'5R3[14671465'5%L2?<67[RH%L;?<26\3B0>675P5n2001000000120000000WDWCWEPH^DG^CF^EEP5PDg016lPDg017X&08C#C#C#C#C#C#C#BRE,MDRFf5RG#ERHH041MD@R3402S001MDGS01A}DFHRI,4DS02%G<RJ#G#G#G#G#BRK,MDRL9zD3RM,4DRN'Uf6RO,MD,4DRP,55X0814DFRQ14DHRR'0,7DA65NPX0814D3S0314DLRS'9RT%EO,4DRU,0Q,7D?65PX0817DERV105URW,7D?6TPX0817D@RT10VU,7DRX195S;6PX0817DKRY19T5=6XPX0817DGS0419TYRP=6X5X0810VRRX%BCRC,h>RZ'117DOR[965PX0811EZR\11WZ?6P[X0811@ZRP10\U/1ZRW195Y;6[X0811KZR]19P5=6W[X0811GZR[19P]R^=6W5X08PE1056/1Z11OZRW76^X08P@10E6R_/1ZR`195];6WX08PK19@5=6`WX081A7ARa,0ARb117AS05':,57P8%r8Rc%p8P`1A6ARd,0ARe116A':Rf,0ERg/1ZP8^M8Rh^L8RiP8Ph%B<RjP8P8P7P4P8P8P7P41o75Rk#BRl%nkRkn011010003001010310103P8P8P7P4PkPln011010003001010310103n011000003001010210102XG8XF8Rl;lc,k8RkP8P8PcPcCRRmCRRnP8PhPmP8P8Pc%i8C[C[:0NinP0P_PgP8P8^G8PkP8P8PcPkCRP1B0MjlcPE1Z8EP6PfP5N;0LPZPZ1Z8ZN:0K10EORfPf1Z8fN90EWO1f>@Rl1K4>Rj%2@Rc1K4A[[R1%2>Rkg00RhRgAe>@7UW8R_%2AR0\g^8kRng00SDRi$0=Rm&0<iRh&0;8Ro&078Rp&068Rq1I8>Rr%^?5d8R?1I84Rs'Q,8q'c203q9R9P5P6g00RHRtg00TWRu'W20156=<tudB00847C~Rub2b3b4A<8A4g018DS06[P5b1b5b69|7APG1:e5,0E/1Z/5fX081W8R157RRtePt1{6A%26Rt1A;A#2\0[PlP1P_Pn1f>CRv%2C1K4Z[\jRjAe>C7VgX8kRC%2ZR>\g^8kRkf7Rg/SARw%2gf9Rx/1AS07#2\0[RyPmPhP81V86S08P7PoCaPp1I8ERz1T8<R<5P8R{1T8=R=Ad8rDRr5P85`8AP8?==`8<9P8z'Q,8qP9Pub2b3b4X78X9810E5107Z':10A7/:5,0E'5^78^98P51AxAf=R|O2b1b5b6b:b;b<bAb=10EGR}10aZ':1:bG,0E'5P810dZ,:fRb115Z10EgRa'5X0811fZ155aX081W8U156URUeS09PUPlP1P_PnPvPjPCPkPwPyp-0Ry1y8Eg018aRw#FRa,N85x81N8wRw5X8g019@R~'_%Fa#FRa#F#F,N81N8a5X89X8w/_~,ww=bim5biPhP8Q08P71V82CaPpPqPq1T8J9;qsRJ%v:R:PqA;qs?P:A;qs=C@C@P:Pq1]qG9=qJP:Pq1Q=<,8qP:Pq1]qO1D<?,8qR?5=qP:A;qs{1D{r,8q5=qC@C@C@C@P9Pub2b3b4X78X98XB8X?yW@%22R{\0\t1\{;1526A?g2A10E;R;#2??;Z[[[[^78^98^B8^?y^@yP5%2|1KxZPxQ07P|P7f:Rxf;f<O9b1b5b6b:b;b<b=9HfZ11bZAufdZD31:eO,0EP5Etb>Q05P2D3O210E7/1Z/5}Pf11gZRg965@X081AfA155gX08Re10OERd1A5E/5gX08POPeP8PWPOQ09PU10E2R2/SZ%2211}Z#2\>[PlP1P_PnPvPjPCPkf8Rn/SA%2n11xA#2\0[PmPh1V87PpPqA;qs<R0==q?P:1D<r,8q9=q0C@P9Pub2b3b4X78%27??7Z\B^78P5f>P|O2b1b5b6b:b;b<bAb=9HOZCs1AdEPmPhPoPp1Qzs,8q,cqP9Pub2b3b4A<8E4Q06[P5b1:09OED3Pf20:EOD31Uf@PmPhPoPp1I8@RO9;qsR4P9Pub2b3b4PcP5b19qf@D3P`P5D3bIP]PvPjPCPkPmPhPoPp1I8KR]9;qs1D]r,8q5=qP9Pub2b3b4%2K??KZP5b1b5b69HKZD3PPPvPjPCPkPmPhPoPp1DOr,8q9=q4P9Pub2b3b4A?c@ZP5b1b5b69H@ZD3P\PvPjPCPkPmPhPoPpA;qsz1Dzr,8q5=qP9Pub2b3b4%2E??EZP5b1b5b69HEZD310\R/1Z?6^[eQ04%JGD3PY%JKD3PT%J@D3PV%JED317DX%JXD3Q01,4DRX1ODGD3PS1ODKD3Q031OD@D3PQ1ODED3PNB0?D3LD3Q02B0@DFHD3B0ADIM,4DB0BDIMD3Q00,4D/5XeO4b>bFbKbHWJXN8o"). Qed.
Lemma low32_sxw : forall k, 0 <= k < 2 ^ 32 -> low32 (sxw k) = low32 (Z_to_bv 64 k).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) [] "h01zh12Hah24__x1h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with92b1h:2b2h;1nh<1Hh=2Hkh>6__sat2h?6__sat3h@1kp;1p;2p;3p;4p;7p;8p;6g001^j17Tg002Cj1;Tg002aj2ATg003>j25Tg003ZR0j2?Tg00XBj18Tg00ARj39Tg00Iij20Tg00Xej3QTg0045j1ETg00KBj1DTg019lj1LTg00ICj2KTg01:Tj1`Tg00[ej26Tg005:j22Tg01;2j4<Tg005`j2:Tg009Aj2HTg009ij3GTg00:Mj1ZTg00:mj1YTg00;Mj2XTg00;kj1WTg00<Ij1VTg00=4j2FTg00=Wj2UTg00>:j4=Tg00>ej3CTg00?Hj1PTg00?jj2OTg00@Lj2RTg00@fj2NTg00Alj3STg00BKj4TTg00C=j3MTg00mIj4dTg00HHj1cTg00JSj2bTg00U^j2aTg01;[j1JTg01<?j4ITg008Aj2_Tg00L7j7]Tg00L[j7\Tg00M?j8^Tg00Mcj6[Tg00NAR1f0R2'_p=4g00N_R3f1R4;92p=1P4g00O=R5g00O\R6P6g00P<R7P2g00P\F]p=>f2R8P5P6P6P7P4P2F\p=@f3R9P5P6P6P7P8P4P2G^p=BP3f4R5P9P8P4P2E[p=3%42g00QcR:#7R;#;R<%7;#7#7#7R;#;R='AR>,52'?R?g016NR@%82RA%84RBP0%88?94210981094'1R0[10841082'1%89?984[RC%85?998\0AQ842P2n2001000000120000000W:W9W;PC^:B^9A^;@P2%E;R@%D8RA#LRB%7;R;#ERC/K8R0#LRD10CAREg01=1RF#`RG'6,2@PCPFP@1KC9RHC<,0@,12X0310C0RI/6G,2@%D9,0CRJ/6G,2@/12X03PE12@2RK10CHRH/6G,2@'1X03PI12@J/1KX03P81:H>,12X0312C8RH1:2>,19X03R9%;;R;,A<RK,:8RJP9P8P9P31:8>P81H<=R9151<RG%4=151>[[RL%4<RMg00RhRNAG<=4UW1R=%4>\N^1MROg00SDRP#ZRQ%YPRP1X34RR%W3RS%V3RTP31F31g00T01U3:R:C=,>TRUP3P:g00Q<RV1F3<RW=C3@C=,>T5@TRX%P6R6PXCB1OT7R7P2P8g00RHRYg00TWRZ'R1N28=9YZdAS314CTRZb4b7b8X23%44RY154>'?\?^23P2f5P5O2b3b5b69M8>CdPJP9PLP=PO1H<;%4;151K[\GAG<;4VNX1M%4K\N^1MPQPPPRPSPTPXP6P3P:PVAC3WCC=,>T9@TUCBP7PZb4b7b8X23154K,?Y\?^23P2f7f6O2b3b5b6b>b?9M8KD3PH%c8D3PI1bC8D31:E>1a84D312@E12@I'1e16I1%JID316E1%JED3PCPFP@P0C<,0@PCPFP@P0CID3PCPFP@PAC<,0@PCPFP@PACID310@B10@D'1eO4b<W=X@3o"). Qed.

Lemma gz_subS : forall M a n b m, gz M a n -> a <= b -> b + m <= a + n -> gz M b m.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) [] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with74__x4h84__x5h91Hh:2H0h;3Habh<3Hbmh=2Hih>1Mh?1ah@1bhA1ihB1mhC1nhD1zp;3p;2p;1p;4p;6p;7p;8g01=Oj3GTg008Aj21Tg00Egj20Tg003>j2=Tg003Zj2@Tg00:Mj1WTg00:mj1UTg00;Mj27Tg00h0j48Tg00;kj1LTg00<Ij1KTg00=Wj24Tg001^j1CTg00DCj3FTg006@j1DTg00>:j4:Tg00?jj2VTg00@Lj2TTg00@fj2QTg00ARj3?Tg00Alj3PTg00BKj4OTg007Bj2<Tg01>Fj2NTg00i7j19Tg00iVj25Tg00jhj36Tg00kQj2BTg00lij3ATg00eOj1JTg00=4j2MTg00?Hj1ITg001Bj6HTg00C`j3RTg00L7j7STg00L[j7YTg00M?j8XTg00N_R0f1R1f0R23Rp=3P1g00O=R3g00O\R4P4g00P<R5P2g00P\FSp=2P0P1g00T0P2C:p=;f2R6P3P4P4P5P1P2FYp=Ef3R7P3P4P4P5P6P1P2GXp=>g01?>f4R3?G7611361076f5R8/03'1g00NAR9/121=23'@g00SDR:#WR;%U:R<P01706P11707C8%L0R=%K0R>P0g00QcR?,40R@%C?RA,40RB=F0@%D?,40R?'3'3g00U713B?C:'21V>5R5P2P6g00RHRCg00TWRD'T1Q26=?CDdAP091CORDb4b5b6X00X10X201<12/06,0210165?0^00^10^20P2P6f7RCf9REO3b3f8RFf6RG/<F/01'010G15?0P01<CE/06RH,0Ef;/N2XD0P8PHg018aRH#9RI#9RJ#9RK,50150J150HRH560560g019@RJ'B%9K,50150I=60H560/BJ=A:;5A:P<P0P01703P6%J0R<C8P1P01708P7P<C8C8P=P>1M09R=/;?,2>P0P?g00Q<R<%DA,40R:C:,2>5E>%I4R4P>13@:%CA,40RA,3B';,2>P4P>1;B@,2>P4AF0@B/3?R?,;=,2>P0P?P<PAC:,2>5E>C>C>C>P5PDb4b5b6X00X10X20X70X8011961=63'@10181063'111761<73/08R1,191=1G'@[[[^00^10^20^70^80P2PCPEP7f:PFP6P3P8O8b3O210C6P2EHb:W=XA0AGC37eW<W;W9XB0X@0XC0X?0W>o"). Qed.

Section SnFind.
  Context {fx : FPState}.
  Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface ASEGS L.
  Variables (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop).
  Variable rom : word -> option byte.
  Variables (A : AS MI) (M0 : mem) (this bl bc key : Z) (ents : list (Z * (Z * V))).
  Hypothesis U0 : umapx MI NS nval A M0 (this + 136) bl bc ents.
  Hypothesis Hkey : 0 <= key < 2 ^ 32.
  Hypothesis HNS : 24 <= NS.
  Hypothesis Hthis : 0 <= this.
  Hypothesis Hz_obj0 : gz M0 (this + 136) 40.
  Hypothesis Hz_bl0 : bc <> 0 -> gz M0 bl (8 * bc).
  Hypothesis Hz_nd0 : forall p k v, In (p, (k, v)) ents -> gz M0 p NS.

  #[local] Abbreviation st R pc M := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hhdr0 : hdr ASEGS M0 (this + 136) bl bc ents := u_hdr U0.
  Let Hbc_in : In bc BSEQ := u_bseq U0.

  Lemma bc_rngS : 0 <= bc <= 26339969.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) ["SnFind"] "p;2p,1Vp4p300R0p1000Np4p710p8P0p1001Bp4p710p8P0p1000ep4p710p8P0p100Mcp4p710p8P0p101?op4p710p8P0p101@gp4p7210p8P0p101A^p4p7210p8P0p101BUp4p710p8P0p101C[p4p710p8P0p101D`p4p710p8P0p101EBp4p710p8g01E_j20Tp,2bcp,6Hbc_in'0o"). Qed.

  Definition non_argS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
  Definition keptS (R R' : bvmap 5 word) : Prop :=
    (forall r, In r non_argS -> getr R' r = getr R r)
    /\ getr R' 20%bv = getr R 20%bv /\ getr R' 21%bv = getr R 21%bv /\ getr R' 24%bv = getr R 24%bv.
  Lemma keptS_trans : forall R1 R2 R3, keptS R1 R2 -> keptS R2 R3 -> keptS R1 R3.
  Proof.
    intros R1 R2 R3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2).
    exact (conj (fun r Hr => eq_trans (A2 r Hr) (A1 r Hr)) (conj (eq_trans B2 B1) (conj (eq_trans C2 C1) (eq_trans D2 D1)))).
  Qed.
  Lemma keptS_aonlyT : forall R R', keptS R R' -> aonlyT R R'.
  Proof.
    intros R R' (KA & KB & KC & KD) r Hr.
    assert (Hc : In r non_argS \/ 20%bv = r \/ 21%bv = r \/ 24%bv = r)
      by (unfold non_argT in Hr; unfold non_argS; cbn [In] in *; tauto).
    destruct Hc as [Hc | [Hc | [Hc | Hc]]]; [exact (KA r Hc) | subst r; exact KB | subst r; exact KC | subst r; exact KD].
  Qed.
  Lemma keptS_of_syms : forall R vals sr R',
    regs_ok (Eseed R vals) sr R' -> syms_id sr non_argS = true ->
    getr R' 20%bv = getr R 20%bv -> getr R' 21%bv = getr R 21%bv -> getr R' 24%bv = getr R 24%bv -> keptS R R'.
  Proof.
    intros R vals sr R' HR Hk H20 H21 H24.
    exact (conj (syms_id_sound R vals sr R' non_argS HR Hk) (conj H20 (conj H21 H24))).
  Qed.

  Definition atBBs (R R' : bvmap 5 word) : Prop :=
    keptS R R' /\ getr R' 15%bv = Z_to_bv 64 bl /\ getr R' 11%bv = popcwA (Z_to_bv 64 bc) /\ getr R' 12%bv = Z_to_bv 64 bc
    /\ getr R' 13%bv = Z_to_bv 64 key /\ getr R' 14%bv = Z_to_bv 64 (hmod key bc).

  Definition KNSA (scr : scripts) : list kentry := kn_fix 20 SNF_STOPS scr SNF_ENTRY srSA [] 50.
  Definition SCRS_bc0 := SCR [true] [EVar 34; EVar 35] [].
  Definition SCRS_2 := SCR [false; false] [EVar 34; EVar 35] [].
  Definition SCRS_lt := SCR [false; true; true] [EVar 34; EVar 35] [].
  Definition SCRS_ge := SCR [false; true; false] [EVar 34; EVar 35] [].

  Ltac seedR R sr :=
    apply regs_ok_srs; [apply regs_ok_seed|];
    repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; first [assumption | match goal with H : getr R 24%bv = _ |- _ => rewrite H; reflexivity end]] |]); apply Forall_nil.

  Ltac keptS_tac R R' HR' :=
    eapply keptS_of_syms; [exact HR' | vm_cast_no_check (@eq_refl bool true) | | | ];
    [ let G := fresh "G" in rreg HR' 20%bv G; rewrite G; symmetry; assumption
    | let G := fresh "G" in rreg HR' 21%bv G; first [exact G | rewrite G; symmetry; assumption]
    | let G := fresh "G" in rreg HR' 24%bv G; rewrite G; symmetry; first [assumption | match goal with H : getr R 24%bv = _ |- _ => rewrite H; reflexivity end] ].

  Ltac runSA R scr :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in let Hpc := fresh "Hpc" in
    pose (E := Eseed R [Z_to_bv 64 this; sxw key; Z_to_bv 64 bc; Z_to_bv 64 bl; Z_to_bv 64 (this + 144)]);
    assert (HR : regs_ok E srSA R) by (seedR R srSA);
    assert (HK : know_ok ASEGS E M0 (KNSA scr)) by (kn_eval; know_tac);
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popcA) = b ->
                  sc_denot ASEGS M0 E (SCBr b BC_LTU (ELit 1) popcA)) by (intros b Hb; exact Hb);
    xrun HR HK 100%nat SNF_STOPS scr 50%N;
    [ split_scs; try sc_auto1; try sc_shdj; try sc_dj;
      try (apply Hpc; rewrite popcA_env; evs; rewrite branch_ltu_lit_l by lia; bool_lia);
      try (cbn [sc_denot]; evs; rewrite ?zx_of_sxw by lia; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia; bool_lia)
    | ].

  Ltac idxS :=
    first [ unfold hmod; rewrite Z.mod_small by lia; reflexivity
          | rewrite ?low32_sxw by lia; rewrite remuw_valA by lia; reflexivity
          | rewrite ?w_addm by lia; rewrite w_and by lia; f_equal; unfold hmod;
            match goal with H : bc = 2 |- _ => rewrite H end;
            rewrite Z.land_comm; exact (Z.land_ones key 1 ltac:(lia)) ].

  Ltac finSA R :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let KP := fresh "KP" in let PC := fresh "PC" in
    assert (KP : keptS R R') by (keptS_tac R R' HR');
    assert (PC : getr R' 11%bv = popcwA (Z_to_bv 64 bc)) by (exact (eq_trans (HR' 11%bv) (popcA_env E')));
    let G15 := fresh "G" in rreg HR' 15%bv G15; let G12 := fresh "G" in rreg HR' 12%bv G12;
    let G13 := fresh "G" in rreg HR' 13%bv G13; let G14 := fresh "G" in rreg HR' 14%bv G14;
    let G13' := fresh "G" in assert (G13' : getr R' 13%bv = Z_to_bv 64 key) by (rewrite G13; apply zx_of_sxw; lia);
    let G14' := fresh "G" in assert (G14' : getr R' 14%bv = Z_to_bv 64 (hmod key bc)) by (rewrite G14; rewrite ?zx_of_sxw by lia; idxS);
    exact (ex_intro _ R' (conj Hms (conj KP (conj G15 (conj PC (conj G12 (conj G13' G14')))))))
    end.

  Lemma blkSA : forall R,
    getr R 10%bv = Z_to_bv 64 (this + 144) -> getr R 21%bv = Z_to_bv 64 this -> getr R 20%bv = sxw key ->
    getr R 24%bv = Z_to_bv 64 SHBASE ->
    bc <> 0 -> exists R', msteps ASEGS (st R SNF_ENTRY M0) (st R' SNF_BB M0) /\ atBBs R R'.
  Proof.
    intros R H10 H21 H20 H24 Hbc.
    pose proof bc_rngS as Hbcr.
    pose proof Hhdr0 as Hh. destruct Hh as [Hblc Hbcc Hp1c Hszc Hmlfc Hdefc].
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1.
    pose proof (u_bl_lo U0 Hbc) as Hbl0. pose proof (u_bl_hi U0) as Hbl1.
    destruct (popcwA_cases bc Hbc_in Hbc) as [[H2 Hp] | [H2 Hp]].
    - runSA R SCRS_2. finSA R.
    - destruct (Z.ltb_spec key bc) as [Hlt | Hge].
      + runSA R SCRS_lt. finSA R.
      + runSA R SCRS_ge. finSA R.
  Qed.

  Lemma blkSA0 : forall R,
    getr R 10%bv = Z_to_bv 64 (this + 144) -> getr R 21%bv = Z_to_bv 64 this -> getr R 20%bv = sxw key ->
    getr R 24%bv = Z_to_bv 64 SHBASE ->
    bc = 0 -> exists R', msteps ASEGS (st R SNF_ENTRY M0) (st R' SNF_NOTFOUND M0) /\ keptS R R'.
  Proof.
    intros R H10 H21 H20 H24 Hbc.
    pose proof bc_rngS as Hbcr.
    pose proof Hhdr0 as Hh. destruct Hh as [Hblc Hbcc Hp1c Hszc Hmlfc Hdefc].
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1.
    runSA R SCRS_bc0.
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
      exists R'; split; [exact Hms | keptS_tac R R' HR'] end.
  Qed.

  Definition KNSx (pc : Z) (sr : list expr) (scr : scripts) : list kentry := kn_fix 20 SNF_STOPS scr pc sr [] 50.
  Definition srSB : list expr :=
    srs sr_id [(15%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36); (20%bv, EVar 37);
               (24%bv, ELit SHBASE)].
  Definition SCRS_B_b0 := SCR [false; false; false; false; true] [EVar 38; EVar 39] [].
  Definition SCRS_B_q0 := SCR [false; false; false; false; false; false; true] [EVar 38; EVar 39] [].
  Definition SCRS_B_m := SCR [false; false; false; false; false; false; false; true] [EVar 38; EVar 39] [].
  Definition SCRS_B_p := SCR [false; false; false; false; false; false; false; false] [EVar 38; EVar 39] [].

  Definition atLoopS (R R' : bvmap 5 word) (q bcx : Z) : Prop :=
    keptS R R' /\ getr R' 10%bv = Z_to_bv 64 q /\ getr R' 12%bv = Z_to_bv 64 bcx
    /\ getr R' 13%bv = Z_to_bv 64 key /\ getr R' 14%bv = Z_to_bv 64 (hmod key bc).

  Ltac ubS hm Hbal :=
    first [ eapply (sc_trap_wrap _ _ _ _ _ bl (8 * hm)); [evs; rewrite ?w_mul, ?w_add by lia; f_equal; lia | evs; reflexivity | lia | lia | lia]
          | eapply (sc_trap_nullxor _ _ _ _ _ bl (8 * hm)); [evs; reflexivity | evs; rewrite ?w_mul, ?w_add by lia; f_equal; lia | lia | lia | lia]
          | eapply (sc_trap_null _ _ _ _ bl); [evs; reflexivity | lia]
          | eapply (sc_trap_align _ _ _ _ (8 * hm + bl));
              [evs; rewrite ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia] | lia | apply align8_add; apply align16_8; assumption]
          | match goal with Hb : cell8 _ _ (bl + 8 * hm) ?b |- _ =>
              first [ eapply (sc_trap_align _ _ _ _ b); [evs; reflexivity | lia | apply Hbal; lia]
                    | eapply (sc_read_cellw _ _ _ _ (bl + 8 * hm) 8%N b);
                        [exact Hb | lia | evs; rewrite ?w_mul, ?w_add, ?v_addi_Z by lia; f_equal; lia | evs; reflexivity] ] end
          | eapply (sc_flat _ _ _ _ (8 * hm + bl));
              [evs; rewrite ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia] | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
          | cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia; bool_lia ].

  Ltac runSB R pw b q0 scr Hbal :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R [Z_to_bv 64 bl; Z_to_bv 64 pw; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key;
                        Z_to_bv 64 b; Z_to_bv 64 q0]);
    assert (HR : regs_ok E srSB R) by (seedR R srSB);
    assert (HK : know_ok ASEGS E M0 (KNSx SNF_BB srSB scr)) by (kn_eval; know_tac);
    xrun HR HK 100%nat SNF_STOPS scr 50%N;
    [ split_scs; try sc_auto1; try sc_shdj; try ubS (hmod key bc) Hbal
    | ].

  Ltac finSB_nf R :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
      split; [exact Hms | keptS_tac R R' HR'] end.

  Ltac finSB_loop R :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let KP := fresh "KP" in
    assert (KP : keptS R R') by (keptS_tac R R' HR');
    let G10 := fresh "G" in rreg HR' 10%bv G10; let G12 := fresh "G" in rreg HR' 12%bv G12;
    let G13 := fresh "G" in rreg HR' 13%bv G13; let G14 := fresh "G" in rreg HR' 14%bv G14;
    split; [exact Hms|]; split; [exact KP|]; split; [exact G10|];
    split; [rewrite G12; first [reflexivity | apply w_addm; lia]|];
    split; [exact G13 | exact G14]
    end.

  Lemma blkSB : forall R (pw b q0 : Z),
    getr R 15%bv = Z_to_bv 64 bl -> getr R 11%bv = Z_to_bv 64 pw -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 key -> getr R 14%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 20%bv = sxw key -> getr R 24%bv = Z_to_bv 64 SHBASE ->
    0 <= pw < 2 ^ 64 -> bc <> 0 ->
    cell8 ASEGS M0 (bl + 8 * hmod key bc) b -> 0 <= b -> b + 8 <= 2 ^ 47 -> (b <> 0 -> cell8 ASEGS M0 b q0) -> (b <> 0 -> gz M0 b 8) ->
    exists R',
      ((b = 0 \/ q0 = 0) /\ msteps ASEGS (st R SNF_BB M0) (st R' SNF_NOTFOUND M0) /\ keptS R R')
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= pw /\ msteps ASEGS (st R SNF_BB M0) (st R' SNF_LM M0) /\ atLoopS R R' q0 bc)
      \/ (b <> 0 /\ q0 <> 0 /\ pw < 2 /\ msteps ASEGS (st R SNF_BB M0) (st R' SNF_LP M0) /\ atLoopS R R' q0 (bc - 1)).
  Proof.
    intros R pw b q0 H15 H11 H12 H13 H14 H20 H24 Hpw Hbc Hb Hb0 Hb1 Hbq Hbgz.
    pose proof bc_rngS as Hbcr.
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (u_bl_lo U0 Hbc) as Hbl0. pose proof (u_bl_hi U0) as Hbl1. pose proof (u_bl_al U0) as Hblal.
    pose proof (Hz_bl0 Hbc) as Gbl.
    assert (Hhm : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    assert (Hbal : b <> 0 -> b mod 8 = 0).
    { intros Hbnz. destruct (u_bkt U0 (hmod key bc) Hhm) as (b' & Hb' & Hbok).
      assert (Hbb : b' = b) by exact (cell8_detA _ _ _ _ Hb' Hb). subst b'.
      destruct Hbok as [Hz | [Hin | (Hbs & _ & _)]]; [lia | |].
      - destruct (in_split_entsA V b ents Hin) as (l1 & k & v & l2 & He).
        assert (Hin2 : In (b, (k, v)) ents) by (rewrite He; apply in_or_app; right; left; reflexivity).
        destruct (u_node U0 b k v Hin2) as (_ & _ & _ & Hal & _). apply align16_8. exact Hal.
      - subst b. apply align_obj16A. exact Hoal. }
    destruct (Z.eq_dec b 0) as [Hbz | Hbnz].
    - subst b. runSB R pw 0 q0 SCRS_B_b0 Hbal.
      exists R'. left. split; [left; reflexivity|]. finSB_nf R.
    - specialize (Hbq Hbnz). specialize (Hbgz Hbnz). pose proof (proj1 Hbq) as Hqr.
      destruct (Z.eq_dec q0 0) as [Hqz | Hqnz].
      + subst q0. runSB R pw b 0 SCRS_B_q0 Hbal.
        exists R'. left. split; [right; reflexivity|]. finSB_nf R.
      + destruct (Z.le_gt_cases 2 pw) as [Hw | Hw].
        * runSB R pw b q0 SCRS_B_m Hbal.
          exists R'. right; left. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [exact Hw|]. finSB_loop R.
        * runSB R pw b q0 SCRS_B_p Hbal.
          exists R'. right; right. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [lia|]. finSB_loop R.
  Qed.

  Definition srSL : list expr :=
    srs sr_id [(10%bv, EVar 32); (12%bv, EVar 33); (13%bv, EVar 34); (14%bv, EVar 35); (20%bv, EVar 36); (24%bv, ELit SHBASE)].

  Lemma node_factsS : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + NS <= 2 ^ 47 /\ cell8 ASEGS M0 (p + 8) k /\ cell4 ASEGS M0 (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 ASEGS M0 p (hdaddr l2) /\ gz M0 p NS.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) ["SnFind"] "p'0h01Hh13Hchh24__x1h32Hah41ah51lh67__arithh74__ffh86__sat3h96__sat4h:6__sat5h;6__sat6h<8__varmaph=5__with>2l1h?1Ah@4__x2hA2l'hB2HehC2HhhD3HinhE2HkhF3HkrhG3Hp0hH3Hp1hI2IHhJ1UhK2_HhL3_H0hM3_H1hN4entshO1khP2kvhQ2l2hR1pi001phS1qhT1vi011zp&0p;2p;1p;3p;=p;4p;6p;Bp;5p;7p;>p;8g01WPR0j2WTg00:mj1STg00ARj3LTg001^j15Tg006@j1JTg002Cj1DTg00Egj2@Tg01]Ql=gTg01HKj34Tg01EBj3MTg01Lij2YTg03VSk405Tg00lij3RTg00@Lj2dTg01MCk304Tg01N:k302Tg00Mcj6|Tg03W2lBzTg03Wjj5qTg002aj2\Tg01T7j1hTg00FDj2fTg03X\j42Tg01?oj2ATg01=Oj3BTg003>j2:Tg003ZR1j20Tg009Aj2cTg009ij3bTg00:Mj1_Tg00;Mj2^Tg00;kk103Tg00<Ik101Tg00=4j2]Tg00=Wj2aTg00>:j4QTg00?Hj1{Tg00?jj2yTg00@fj2xTg00Alj3uTg00BKj4tTg00eOj1rTg00h0j4pTg00C`j3oTg0045j1[Tg00>ej3ZTg00L[j7nTg03YSl>mTg001Bj6lTg03ENj3sTg03J`j3vTg01D`j6wTg01J7j4GTg01dgj4PTg005`j2jTg02a6j4OTg01Xij4`Tg008Aj2FTg00L7j7}Tg00M?j8~Tg01@gk400Tg00N_R2f4R3f3R4P2f2R5f1R6f0R7CPCPp=6AR5679M34p=7P2P2P6P7CPp=Ug00NAR8/:7p=;1j67=L28p=<g02cAR9P41@56P7COp=8AL278p=if5R:P3P4P5P6C2/07'0p=3P9f7R;f6R</@:P3C`1F841:56'0/07'0p=11067,05p=?1@45/F6/07p=T1:831@45/F6/07'0p==P9P4P5P6CO/07p=CP9P31@45P6CO/07p=>1@56/F7p=HP9P41@56P7C`p=X1F841:56'0/07p=e1F86/07p=IP9P4P51A67COp=E1F87p=KP6g00O=R=g00O\R>P>g00P<R?P7g00P\F}p=NP4P=P>P>P?P5P6P7G~p=VP9P5P6P7H00p=9P2P4P5P6CP=R37p=kp,1VR@,W2RA,W2RB#SRCp,4entsRDPBP3PBPAP4P@P5P6D6P7D75LCp,2U0p,2ACREP9p,1LRFp,2MIRGp,2NSRHP@p,4nvalRIp,1ARJp,2M0RKp,4thisg00QcRL#5RM#5#5RN#J#5#5#5#D'@ROp,2blRPp,2bcRQPDM=gPCPBP<PBPAP:P@P3P4D6RRP5D7PAP<P@P:P3D6RS=4B7XNCg000ep4p710RT%S7RU%S6RVP1AM4569447A4364A4365'YRW[A4475A4476'YAM3459436[RXAM:3494:5\WP4P5P6P7H05P7n2001000000120000000X45WAW5W?PX^45^AV^5U^?TP7PBP;ARBS4RTPSA4BS;A4BSTALBSSA4BS41dBS404402O5b0PDP6E|A4BRDPEP9PFPGPHP@PIPJPKPOPPPQPDP6P<P:P3P7MBz1W22RR1U<HPEP9PFPGPJDqRS34%;<P<PH%DMRT%JMRU#J#J#JRV#DRX'\RW%5NRY#DRZ,<<PKP<%DNRNP:C8PKP<PZP:P:P:%5YRY#DR[,\TR\PIPKP<P3O3P<PHPO%5U#5#5#DRU%iQ#hR]P;PHPP1fNQR^C2[E3G13?CT3?P11U;H=4RSP;P;PHPW1<;ZPKP;PNP<C8PKP;PZP<P<P<P\PIPKP;P:O3P;PHPOPUf8R_PHPPP^C2\]E3G13?D=P_P_PHPWPKP_PNP;PKP_PZP;P;P;P\PKP_1A@:ABK_HCCG1D>D=P7f9R;/UH=4RSf:RSPSPHPW1<SZPKPSPNP;C8PKPSPZP;P;P;P\PIPKPSP_O3PSPHPOPUf;R_PHPPP^C2\]E3G13?D=P1%;_P_PHPW1<_ZPKP_PNPSC8PKP_PZPSPSPSP\PIPKP_P;O3P_PHPOPUf<RSPHPPP^C2\]E3G13?CTPSPSPHPWPKPSPNP_PKPSPZP_P_P_P\PKPS1A@;ABKSHCCG1D>D=P7f=R_#;f>RRPHPW1<RZPKPRPNP_C8PKPRPZP_P_P_P\PIPKPRPSO3PRPHPOPUf?RSPHPPP^C2\]E3G13?CTP1AHSHW1<SZPKPSPNPRC8PKPSPZPRPRPRP\PIPKPSP_O3PSPHPOPUf@RRPHPPP^C2\]E3G13?PRPRPHPWPKPRPNPSPKPRPZPSPSPSP\PKPR1A@_ABKRHCCG1D>D=P7fAR_?HHWfBRS/<ZPKPSPNP_C8PKPSPZP_P_P_P\PIPKPSPRO3PSPHPOPUfCRRPHPPP^C2\]E3G13?P11<RZPKPRPNPSPKPRPZPSPSPSP\PIPKPRP_O3PRPHPOPUfDRSPHPPP^C2\]E3G1D>PSPSPHPWPKPSPNPRPKPSPZPRPRPRP\PKPS1A@_ABKSHCCG1D>D=P7fER_/<ZPKfFRRPNP_PKPRPZP_P_P_P\PIPKPRPSO3PRPHPOPUfGRSPHPPP^C2\]E3G1D>P1PKPSPNPRC8PKPSPZPRPRPRP\PIPKPSP_O3PSPHPOPUfHR`PHPPP^C2\]E3G1P`P`PHPWPKP`PNPSPKP`PZPSPSPSP\PKP`1A@_ABK`HCCG1D>D=P7PKfIR_PNP`C8PKfJRSPZP_P_P_P\PIPKPSP`O3PSPHPOPUfKR`PHPPP^C2\]E3G1P1PKP`PZPSCXPSPSP\PIPKP`P_O3P`PHPOPUfLRaPHPPP^C2\]E3CePaPaPHPWPKPaPNP`PKPaPZP`P`P`P\PKPa1A@_ABKaHCCG1D>D=P7PKfMR_PZPaCXP_P_P\PIPKfNR`PaO3P`PHPOPUfORaPHPPP^C2\]E3CeP11:`\,I`PIPKPaP_O3PaPHPOPUfPR1PHPPP^C2\]E3P1P1PHPWPKP1PNPaPKP1PZPaPaPaP\PKP11A@_ABK1HCCG1D>D=P71:1\,I1PIPKfRRbP1O3PbPHPOPUfSRUPHPPP^C2\]E3%;UAHUHWR]PKPUPNPbC8RNPKPUPZPbCXRZ1:b\,IbR^PKPUP@P1CERcABKUHRd'0Re'0Rf'0Rg'0Rh'01cT[Ri%;TRj%K[%;\[[Rk%KTRlg00RhRmAbT[6UW3R[%K\\m^3lRn1cTXRo%KX%;W[\jRjAbTX6VmX3lRX%KW\m^3lRlg00SDRm#_Rp%SmRm1^26Rq&032Rr&012RsP21]28Rtg00Q<Ru1a2LRLCQ,NsRv%{>RwPvCV1ys?RvP7P5g00RHRxg00TWRy'd1x75=LxydAu286CtR8b7b<b=X22%;7%;6[^22P7fXRyPSO2b6b8b9b:b;P]PhPoPjPXPlPiPkP[PnPpPmP21^25P6%r2CpPrPsP21a2M9o2Lg00T0RM1]2TRT%[V5Z2CQ,NsRVPwPVCVPvP8b7b<b=X22X@2AH76WAH65W[^22^@2P7PHPyPRO3b6b8b9b:b;PNPgP;PZPfP:P^PePiPkP[PnPoPjPXPlPpPmPqPrPsPsP=P>P>P?P2PtPMPLCQ,NsP2PLPu%[Y9Z2TCQ,NsFnRsPwPsCVPvP8b7b<b=X221:7\,I71:6\,I6[^22P7fWR\P<O2b6b8b9b:b;PcPdPCPDA9@K7X5CPEP9PFPGPHP@PIPJPKPOPPPQPDP`M>mPBfTR`PBPAPUP@PbfQRDD6P1D7R1PaElA9@K1PBPBP7PBPAfUR1P@P`PUD6PbD799@KPKfVRaP@PUCE]1X>CPB%_BPBPAP`P@PUPbD6PDD799@KPKP1P@PbCEA9@Kb;s7W1P0P2PAPBP7PBPAP\P@PaP1D6P`D799@KPKPyP@P1CE]1PBARB56PBPAPyP@P\PaD6P1D799@KPKfYR`P@PaCE]1[^5CP7PBP7PBPAfZRaP@P`PyD6P\D799@KPKf[R\P@PyCE]1PBPBPAP4P5P6DkPBPAP\P@PaP`D6PyD799@KP6PKP3P@PBP5PBPAf\P@P\PaD6P`D7R`CEA9@K`;v7O1W1WIX>CXPAXS2P6P7O2n2001100000120101100X4BP1P7Ewb1p,6Hz_nd0PUPbPDP_O4CGCGCGCGCGCGWMWFP6P7O2n2001000000121000000W0WEP6P7O2n2001000000121000000W0WCP6P7O2n2001000000121000000W0WLP6P7O2n2001000000121000000W0WHP6P7O2n2001000000121000000W0WGP6P7O2n2001000000121000000W0WKP6P7O2n2001000000121000000b4bDbJWBXQCXT@XO2XR2W>o"). Qed.

  Lemma land_bc1S : forall k, bc = 2 -> Z.land k (bc - 1) = k mod 2.
  Proof.
    intros k H2. rewrite H2. change (2 - 1) with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Ltac runSL R vals scr pc :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E srSL R) by (seedR R srSL);
    assert (HK : know_ok ASEGS E M0 (KNSx pc srSL scr)) by (kn_eval; know_tac);
    xrun HR HK 100%nat SNF_STOPS scr 50%N;
    [ split_scs; try sc_auto1; try sc_shdj;
      try (match goal with Hk : cell4 _ _ _ _ |- _ => unfold cell4 in Hk; sc_rd_sx Hk end);
      try (match goal with Hal : ?p mod 8 = 0 |- _ => eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | exact Hal] end);
      try (cbn [sc_denot]; evs; rewrite ?w_remu by lia; rewrite ?w_and by lia; rewrite ?land_bc1S by lia;
           rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu, ?br_ne_sxw by lia; bool_lia)
    | ].

  Definition walkS (pc : Z) (R : bvmap 5 word) : Prop :=
    exists R', keptS R R' /\
      ((exists p v, msteps ASEGS (st R pc M0) (st R' SNF_FOUND M0) /\ getr R' 10%bv = Z_to_bv 64 p /\ In (p, (key, v)) ents)
       \/ msteps ASEGS (st R pc M0) (st R' SNF_NOTFOUND M0)).

  Ltac finSL_nf R :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let KP := fresh "KP" in
    assert (KP : keptS R R') by (keptS_tac R R' HR');
    exists R'; split; [exact KP | right; exact Hms]
    end.
  Ltac finSL_f R p v He :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let KP := fresh "KP" in
    assert (KP : keptS R R') by (keptS_tac R R' HR');
    let G10 := fresh "G" in rreg HR' 10%bv G10;
    exists R'; split; [exact KP | left; exists p, v; split; [exact Hms | split; [exact G10 | rewrite He; apply in_app_iff; right; left; reflexivity]]]
    end.

  Lemma walkS_pre : forall pc pc' R R1,
    msteps ASEGS (st R pc M0) (st R1 pc' M0) -> keptS R R1 -> walkS pc' R1 -> walkS pc R.
  Proof.
    intros pc pc' R R1 Hms K (R2 & K2 & Hr). exists R2. split; [exact (keptS_trans _ _ _ K K2)|].
    destruct Hr as [(p & v & Hms2 & G & Hin) | Hms2].
    - left. exists p, v. split; [eapply msteps_trans; [exact Hms | exact Hms2]|]. split; [exact G | exact Hin].
    - right. eapply msteps_trans; [exact Hms | exact Hms2].
  Qed.

  Ltac finStepS R :=
    match goal with HR' : regs_ok ?E' _ ?R', Hms : msteps _ _ (mkst _ _ _ _) |- _ =>
    let KP := fresh "KP" in
    assert (KP : keptS R R') by (keptS_tac R R' HR');
    let G10 := fresh "G" in rreg HR' 10%bv G10; let G12 := fresh "G" in rreg HR' 12%bv G12;
    let G13 := fresh "G" in rreg HR' 13%bv G13; let G14 := fresh "G" in rreg HR' 14%bv G14;
    let G20 := fresh "G" in rreg HR' 20%bv G20; let G24 := fresh "G" in rreg HR' 24%bv G24;
    exact (ex_intro _ R' (conj Hms (conj KP (conj G10 (conj G12 (conj G13 (conj G14 (conj G20 G24))))))))
    end.

  Lemma loopSM : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc <> 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 key -> getr R 14%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 20%bv = sxw key -> getr R 24%bv = Z_to_bv 64 SHBASE ->
    walkS SNF_LM R.
  Proof.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc H10 H12 H13 H14 H20 H24;
      pose proof bc_rngS as Hbcr;
      destruct (node_factsS l1 p k v _ He) as (Hp0 & Hp1 & Hk8 & Hk4 & Hkr & Hnx & Hgzp); cbn [hdaddr] in Hnx;
      assert (Hpal : p mod 8 = 0) by (apply align16_8;
        destruct (u_node U0 p k v ltac:(rewrite He; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & Hal & _); exact Hal);
      assert (Hhm : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia);
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk; unfold walkS.
    - destruct (Z.eq_dec k key) as [Hkk | Hne].
      + subst k. runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 key; sxw key] (SCR [false; false; false] [EVar 37; EVar 38] []) SNF_LM.
        finSL_f R p v He.
      + destruct (Z.eq_dec (k mod bc) (hmod key bc)) as [Hc | Hc].
        * destruct (Z.ltb_spec k bc) as [Hlt | Hge].
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; true; false; false] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
          -- runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; false; false; false] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
        * destruct (Z.ltb_spec k bc) as [Hlt | Hge].
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; true; true] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
          -- runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; false; true] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsS _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [Hkk | Hne].
      + subst k. runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 key; sxw key] (SCR [false; false; false] [EVar 37; EVar 38] []) SNF_LM.
        finSL_f R p v He.
      + destruct (Z.eq_dec (k mod bc) (hmod key bc)) as [Hc | Hc].
        * assert (STEP : exists R1, msteps ASEGS (st R SNF_LM M0) (st R1 SNF_LM M0) /\ keptS R R1
              /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 12%bv = Z_to_bv 64 bc
              /\ getr R1 13%bv = Z_to_bv 64 key /\ getr R1 14%bv = Z_to_bv 64 (hmod key bc)
              /\ getr R1 20%bv = sxw key /\ getr R1 24%bv = Z_to_bv 64 SHBASE).
          { destruct (Z.ltb_spec k bc) as [Hlt | Hge].
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 p'] (SCR [false; true; true; false; true] [EVar 37; EVar 38] []) SNF_LM. finStepS R.
            -- runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 p'] (SCR [false; true; false; false; true] [EVar 37; EVar 38] []) SNF_LM. finStepS R. }
          destruct STEP as (R1 & Hms1 & K1 & G10 & G12 & G13 & G14 & G20 & G24).
          exact (walkS_pre _ _ R R1 Hms1 K1 (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' Hbc G10 G12 G13 G14 G20 G24)).
        * destruct (Z.ltb_spec k bc) as [Hlt | Hge].
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; true; true] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
          -- runSL R [Z_to_bv 64 p; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; false; true] [EVar 37; EVar 38] []) SNF_LM. finSL_nf R.
  Qed.
  Lemma loopSP : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 (bc - 1) ->
    getr R 13%bv = Z_to_bv 64 key -> getr R 14%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 20%bv = sxw key -> getr R 24%bv = Z_to_bv 64 SHBASE ->
    walkS SNF_LP R.
  Proof.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H12 H13 H14 H20 H24;
      pose proof bc_rngS as Hbcr;
      destruct (node_factsS l1 p k v _ He) as (Hp0 & Hp1 & Hk8 & Hk4 & Hkr & Hnx & Hgzp); cbn [hdaddr] in Hnx;
      assert (Hpal : p mod 8 = 0) by (apply align16_8;
        destruct (u_node U0 p k v ltac:(rewrite He; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & Hal & _); exact Hal);
      assert (Hhm : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia);
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hm2; unfold walkS.
    - destruct (Z.eq_dec k key) as [Hkk | Hne].
      + subst k. runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 key; sxw key] (SCR [false; false; false] [EVar 37; EVar 38] []) SNF_LP.
        finSL_f R p v He.
      + destruct (Z.eq_dec (k mod 2) (hmod key bc)) as [Hc | Hc].
        * runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; false; false] [EVar 37; EVar 38] []) SNF_LP. finSL_nf R.
        * runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; true] [EVar 37; EVar 38] []) SNF_LP. finSL_nf R.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsS _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [Hkk | Hne].
      + subst k. runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 key; sxw key] (SCR [false; false; false] [EVar 37; EVar 38] []) SNF_LP.
        finSL_f R p v He.
      + destruct (Z.eq_dec (k mod 2) (hmod key bc)) as [Hc | Hc].
        * assert (STEP : exists R1, msteps ASEGS (st R SNF_LP M0) (st R1 SNF_LP M0) /\ keptS R R1
              /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 12%bv = Z_to_bv 64 (bc - 1)
              /\ getr R1 13%bv = Z_to_bv 64 key /\ getr R1 14%bv = Z_to_bv 64 (hmod key bc)
              /\ getr R1 20%bv = sxw key /\ getr R1 24%bv = Z_to_bv 64 SHBASE).
          { runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 p'] (SCR [false; true; false; true] [EVar 37; EVar 38] []) SNF_LP. finStepS R. }
          destruct STEP as (R1 & Hms1 & K1 & G10 & G12 & G13 & G14 & G20 & G24).
          exact (walkS_pre _ _ R R1 Hms1 K1 (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' Hbc2 G10 G12 G13 G14 G20 G24)).
        * runSL R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 key; Z_to_bv 64 (hmod key bc); sxw key; Z_to_bv 64 k; Z_to_bv 64 0] (SCR [false; true; true] [EVar 37; EVar 38] []) SNF_LP. finSL_nf R.
  Qed.

  Lemma find_okS : forall R,
    getr R 10%bv = Z_to_bv 64 (this + 144) -> getr R 21%bv = Z_to_bv 64 this -> getr R 20%bv = sxw key ->
    getr R 24%bv = Z_to_bv 64 SHBASE -> walkS SNF_ENTRY R.
  Proof.
    intros R H10 H21 H20 H24.
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc].
    { destruct (blkSA0 R H10 H21 H20 H24 Hbc0) as (R' & Hms & K). exists R'. split; [exact K | right; exact Hms]. }
    destruct (blkSA R H10 H21 H20 H24 Hbc) as (R1 & Hms1 & K1 & B15 & B11 & B12 & B13 & B14).
    apply (walkS_pre _ _ R R1 Hms1 K1).
    assert (B20 : getr R1 20%bv = sxw key) by (rewrite (proj1 (proj2 K1)); exact H20).
    assert (B24 : getr R1 24%bv = Z_to_bv 64 SHBASE) by (rewrite (proj2 (proj2 (proj2 K1))); exact H24).
    pose proof bc_rngS as Hbcr.
    pose proof Hhdr0 as Hh. destruct Hh as [Hblc Hbcc Hp1c Hszc Hmlfc Hdefc].
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1.
    assert (Hhm : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    destruct (u_bkt U0 (hmod key bc) Hhm) as (b & Hb & Hbok).
    assert (HB : b = 0 \/ exists pre l, ents = pre ++ l /\ cell8 ASEGS M0 b (hdaddr l) /\ 0 < b /\ b + 8 <= 2 ^ 47 /\ gz M0 b 8).
    { destruct Hbok as [Hz | [Hin | (Hbs & _ & _)]]; [left; exact Hz | right | right].
      - destruct (in_split_entsA V b ents Hin) as (l1 & k & v & l2 & He).
        destruct (node_factsS l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx & Hgz).
        exists (l1 ++ [(b, (k, v))]), l2. split; [rewrite He, <- app_assoc; reflexivity|].
        split; [exact Hnx|]. split; [exact Hp0|]. split; [lia|].
        exact (gz_subS M0 b NS b 8 Hgz ltac:(lia) ltac:(lia)).
      - subst b. exists [], ents. split; [reflexivity|]. split; [exact Hp1c|]. split; [lia|]. split; [lia|].
        exact (gz_subS M0 (this + 136) 40 (this + 136 + 16) 8 Hz_obj0 ltac:(lia) ltac:(lia)). }
    assert (H11 : getr R1 11%bv = Z_to_bv 64 (bv_unsigned (popcwA (Z_to_bv 64 bc))))
      by (rewrite B11; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (bv_unsigned_in_range _ (popcwA (Z_to_bv 64 bc))) as Hpwr.
    pose proof (popcwA_cases bc Hbc_in Hbc) as Hpc.
    set (pw := bv_unsigned (popcwA (Z_to_bv 64 bc))) in *. clearbody pw.
    assert (Hpw : 0 <= pw < 2 ^ 64) by exact Hpwr.
    destruct HB as [Hb0 | (pre & l & He & Hbq & Hbp & Hb8 & Hbgz)].
    - destruct (blkSB R1 pw b 0 B15 H11 B12 B13 B14 B20 B24 Hpw Hbc Hb ltac:(lia) ltac:(lia)
                  (fun Hn => False_ind _ (Hn Hb0)) (fun Hn => False_ind _ (Hn Hb0)))
        as (R2 & [(_ & Hms2 & K2) | [(Hn & _) | (Hn & _)]]); [| contradiction | contradiction].
      exists R2. split; [exact K2 | right; exact Hms2].
    - destruct (blkSB R1 pw b (hdaddr l) B15 H11 B12 B13 B14 B20 B24 Hpw Hbc Hb ltac:(lia) Hb8
                  (fun _ => Hbq) (fun _ => Hbgz))
        as (R2 & [(_ & Hms2 & K2) | [(_ & Hqn & Hw & Hms2 & A2) | (_ & Hqn & Hw & Hms2 & A2)]]).
      + exists R2. split; [exact K2 | right; exact Hms2].
      + destruct (hdaddr_casesA V l) as [(Hq0 & _) | (p & k & v & l2 & Hl & Hq)]; [contradiction|].
        rewrite Hq in A2. destruct A2 as (K2 & L10 & L12 & L13 & L14).
        assert (He2 : ents = pre ++ (p, (k, v)) :: l2) by (rewrite He, Hl; reflexivity).
        apply (walkS_pre _ _ R1 R2 Hms2 K2).
        apply (loopSM l2 pre p k v R2 He2 Hbc L10 L12 L13 L14).
        * rewrite (proj1 (proj2 K2)); exact B20.
        * rewrite (proj2 (proj2 (proj2 K2))); exact B24.
      + destruct Hpc as [(H2 & _) | (_ & Hp2)]; [|lia].
        destruct (hdaddr_casesA V l) as [(Hq0 & _) | (p & k & v & l2 & Hl & Hq)]; [contradiction|].
        rewrite Hq in A2. destruct A2 as (K2 & L10 & L12 & L13 & L14).
        assert (He2 : ents = pre ++ (p, (k, v)) :: l2) by (rewrite He, Hl; reflexivity).
        apply (walkS_pre _ _ R1 R2 Hms2 K2).
        apply (loopSP l2 pre p k v R2 He2 H2 L10 L12 L13 L14).
        * rewrite (proj1 (proj2 K2)); exact B20.
        * rewrite (proj2 (proj2 (proj2 K2))); exact B24.
  Qed.

  Theorem snfind_correct : forall R,
    getr R 10%bv = Z_to_bv 64 (this + 144) -> getr R 21%bv = Z_to_bv 64 this -> getr R 20%bv = sxw key ->
    getr R 24%bv = Z_to_bv 64 SHBASE ->
    exists R', aonlyT R R' /\
      ((exists p v, msteps ASEGS (st R SNF_ENTRY M0) (st R' SNF_FOUND M0) /\ getr R' 10%bv = Z_to_bv 64 p /\ In (p, (key, v)) ents)
       \/ msteps ASEGS (st R SNF_ENTRY M0) (st R' SNF_NOTFOUND M0)).
  Proof.
    intros R H10 H21 H20 H24. destruct (find_okS R H10 H21 H20 H24) as (R' & K & Hr).
    exists R'. split; [exact (keptS_aonlyT R R' K) | exact Hr].
  Qed.
End SnFind.

Definition snfind_stmt {AC : AllocCeiling} (L : Layout) (MI : MallocIface ASEGS L) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop) : Prop :=
  forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem) (this bl bc key : Z) (ents : list (Z * (Z * V))),
    umapx MI NS nval A M (this + 136) bl bc ents -> 24 <= NS -> 0 <= key < 2 ^ 32 -> 0 <= this ->

    gz M (this + 136) 40 -> (bc <> 0 -> gz M bl (8 * bc)) -> (forall p k v, In (p, (k, v)) ents -> gz M p NS) ->
    getr R 10%bv = Z_to_bv 64 (this + 144) -> getr R 21%bv = Z_to_bv 64 this -> getr R 20%bv = sxw key -> getr R 24%bv = Z_to_bv 64 SHBASE ->
    exists R', aonlyT R R' /\
      ((exists p v, msteps ASEGS (@mkst fx R (Z_to_bv 64 SNF_ENTRY) M (seg_rom ASEGS)) (@mkst fx R' (Z_to_bv 64 SNF_FOUND) M (seg_rom ASEGS))
                    /\ getr R' 10%bv = Z_to_bv 64 p /\ In (p, (key, v)) ents)
       \/ msteps ASEGS (@mkst fx R (Z_to_bv 64 SNF_ENTRY) M (seg_rom ASEGS)) (@mkst fx R' (Z_to_bv 64 SNF_NOTFOUND) M (seg_rom ASEGS))).

Theorem snfind_spec {AC : AllocCeiling} : forall (L : Layout) (MI : MallocIface ASEGS L) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop),
  snfind_stmt L MI NS V nval.
Proof.
  intros L MI NS V nval fx A R M this bl bc key ents U HNS Hk Ht Hzo Hzb Hzn H10 H21 H20 H24.
  eapply snfind_correct; eassumption.
Qed.

Lemma sxw_sx32 : forall k, 0 <= k < 2 ^ 32 -> sxw k = Z_to_bv 64 (PrsGrammar.sx32 k).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_SnFind ()) [] "p'0h01zh12Hah24__x1h31Hh42H0h57__arithh64__ffh76__sat0h86__sat1h98__varmaph:5__with;2b1h<2b2h=1nh>2Hkh?6__sat2h@6__sat3hA6__sat4hB6__sat5hC1bi001bhD2b0hE1kp;1p;2p;3p;4p;6p;7p;8g001^j1;Tg002Cj1<Tg002aj2ATg003>j22Tg003ZR0j2NTg006@j1=Tg006ej2KTg007Bj20Tg0045j1JTg00XBj1:Tg00ICj25Tg00Egj24Tg00ARj36Tg007_j2fTg008Aj2?Tg008]R1j3\Tg00@Lj2DTg00Iij27Tg00Xej3XTg005:j2>Tg005`j28Tg009Aj2CTg009ij3BTg00:Mj1WTg00:mj1VTg00;Mj2UTg00;kj1TTg00<Ij1STg00=Wj2RTg00=4j2@Tg00>ej3ITg00C`j3GTg00DCj3HTg00Dfj1QTg00EDj3PTg00>:j4FTg00?jj2OTg00@fj2iTg00Alj3hTg00BKj4gTg00FDj2eTg00Faj3bTg001Bj6]Tg00HHj1LTg00JSj2MTg004Sj2[Tg00L[j7^Tg00?Hj1_Tg00M?j8ZTg00GFj2`Tg00KBj1aTg04;7j1YTg00L7j7cTg00Mcj6dTg00NAR2f0R3'?p=3g00N_R4f1R5;63p=1P5g00O=R6g00O\R7P7g00P<R8P3g00P\Fcp=EP4f4R9f3R:f2R;P5P3Edp=9%33g00QcR<#;R=#<R>%;=#;#;#;R=#<R?'AR@,23'NRAg00RHRBP4%=<#=#=#=#<RC,A>RD,K5REP5105@n0100000020000%;=RF#JRG#:RH15G3PBP41K;DRIP;%<FRF,A>RJ,4;/0@n0100000020000,5G36X041f5D125D1?D5;\EPIPBP112:D1?D:PBP4P5f5R1101@n0100000020000,5GPBP4P5P1141J/0@n0100000020000,5G56HP5129D15G1,DHW3P3O11?D9g016NR1%:3RI%:5REP0%:;?65317:;17:5'1R0[17;517;3'1%::?6;5[RK%:9?6:;\0AX;53P3n2001000000120000000W<W;W=PK^<E^;I^=1P3PGf6R1/0@RI,5GRE141J/0@R1,5GRK1>GIR0f7RL/4J/0@RM,5G,7G,13X041>G1RN10L@RL,>G/13X0418IJ1>GM,13X04181J18LJ/13X041C>?RO122>RP%3?122@[[RQ%3>RRg00RhRSAB>?5UW1R?%3@\S^1RRT1C>F%3F122J[\PAB>F5VSX1R%3J\S^1R1C>C%3C122D[\PAB>C5VSX1R%3D\S^1Rg00SDRR#WRS%VRRR1U45RD%T4RC%S4RPP41R4<RF1@4>R>=I4GRU5G4%J=R=9I4>R>5H4%Q<R<,@4=P4U5G4g00U7AH4F>CF'E1OP8RUP3P;g00TWRV,DB1i3;=6BVdAh425CgRVb6b9b:X24143J/0@1e<JRB'4103@'1^24P3f=O1b5b7b8b?b@bAbB141B/1IP414MBRB183Jf8/4J/0@/8JR;'1X0418MJRW113;X041D4W18BJAbM<JD9PLP3E]b4PN%L1D9P0%LID917GK1MG1D917GE1MGID9O4b4W3P3O1n200210000000021000011000bDbC1[=5POPQP?PTPSPRPDPCPPP6P7P7P8PPP6P7P7P8P41@42g00T0PFCF,EPP4PFg00Q<P>CF,EPF^RP%_7PPGZPUPVb6b9b:X24%35125@'N\A^24P3P9P:O2b5b7b8,`5D9%a5%Y5,5G56HeW>XE4o"). Qed.
