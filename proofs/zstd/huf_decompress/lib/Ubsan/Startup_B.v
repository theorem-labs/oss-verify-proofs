(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_memset F_memcpy Startup_A.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Startup_B () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List6nth_okK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B=rmemsetZ_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3addK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission5Ubsan8F_memset;memset_postC5ARocqVerifyHarness?AgentSubmission5Ubsan8F_memset;memset_specC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC47Corelib5Lists7ListDef6repeatI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_monoK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C47Corelib4Init9Datatypes6lengthc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B=rmemcpyZ_postC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission5Ubsan8F_memcpy;memcpy_postC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5Ubsan8F_memcpy;memcpy_specC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6shiftlC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00C46Stdlib4Bool4Bool;orb_false_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z=testbit_neg_rc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BBtestbit_small_highC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lor_specC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4of_Nc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B@lor_byte_testbitC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z;shiftr_specC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z=shiftl_nonnegK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BDbytes_le_to_Z_nonnegc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B=lor_byte_highc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B<lor_byte_lowC5ARocqVerifyHarness?AgentSubmission3Lib3MemIbytes_le_to_Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z3mulc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BKZ_to_le_bytes_bytes_le_to_ZC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BCbytes_le_to_Z_boundC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List:length_appc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B<canary_bytesC46Stdlib5Lists4List9app_nil_rc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BCcanary_bytes_lengthc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BDle8_le_bytes_to_wordc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B9canary_ofK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit8td_cellsc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B>rinit_ssp_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveK47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFastFbytes_at_write_other_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast=munch_write_nC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast;stk_write_nC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64K4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B=rmemcpy_specZK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_BCcanary_recast_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib9StoreFast@rw_cells_frame_nK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit6rd_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I46Stdlib5Lists4List6Exists00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B8rpn_postC46Stdlib5Lists4List9nth_errorI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app2C5ARocqVerifyHarness?AgentSubmission3Lib3Arr9u8ro_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Peano2ltC46Stdlib5Lists4List>nth_error_app1C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC46Stdlib5Lists4List>nth_error_NoneC47Corelib4Init9Datatypes7nat_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B7pauxv20C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit:libc_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Nodes7at_nodeI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C5ARocqVerifyHarness?AgentSubmission3Lib5ITree5enodeC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5epostC47Corelib4Init3Nat3mulC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B=rmemset_specZC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9rd_u64s_gC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B8rpn_loopC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=stk_lo_nonnegC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_A>rinit_tls_postC5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_A>rinit_tls_specc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B?rinit_libc_postc5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B>rinit_ssp_specC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit9rtd_cellsC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_16C5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit>impl_epost_evtC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim9ex_elim_2c5ARocqVerifyHarness?AgentSubmission5Ubsan9Startup_B@renvp_count_loopC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=impl_from_evtC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4implC5ARocqVerifyHarness?AgentSubmission6Common;Startup_kit<rw_cells_appC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK4ELinuxProcessSemantics5Riscv5Instr5aluop03K5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node07C5ARocqVerifyHarness?AgentSubmission3Lib6Decode;dec_set_tidK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmemsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma rmemset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt rsegs (rmemsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x28eb0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
 assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

Definition rmemcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at rsegs m' S src.

Lemma rmemcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m S src ->
  length src = Z.to_nat n ->
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt rsegs (rmemcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x28aac) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
 assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGOT_SSP := 0x2a528%Z (only parsing).
Notation RGUARD := 0x5bb10%Z (only parsing).


(* [comment removed for export] *)
Section LeRoundtrip.
Local Open Scope Z_scope.
Lemma testbit_small_high : forall a k, 0 <= a < 2 ^ 8 -> 8 <= k -> Z.testbit a k = false.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "p'0h04__x1h14__p1h22Hah37__arithh44__ffh58__varmaph65__with71ah86__sat1h91bh:1Hh;2Hkh<3Hnzh=6__sat0h>1ei001eh?1kh@1si011si021np;1p;2p;3p;7p;4p;6p;5p;8g002kj1=Tg008lj1?Tg009Jj2<Tg009gj20Tg00BCR0j21Tg00Agj26Tg015^j2ITg016>j1;Tg016WR1j2ETg0177j2ATg008Rj39Tg017Xj1]Tg000Mj7VTg006Xj1UTg005Xj1RTg00GBj2QTg00G`j1NTg00H>j1LTg00Hij2:Tg00ILj2KTg00Ioj43Tg00JZj6HTg00<7j1GTg00Kaj2FTg00C5j2@Tg00LCj2JTg00Loj3DTg00MNj4MTg0188j18Tg018Vj3CTg00oVj2OTg010>j3PTg010bj2BTg019<j6STg003Pj1TTg00K>j3\Tg019`j5[Tg01:Ej4ZTg00[lj7WTg00\Pj7XTg00]4j8YTg00_bR2f0R3'6p=2g00`@R4?932p=7f1R5g00cLR6g00ckR7P7g00dKR8P3g00dkFWp=4f2R9P6P7P7P8P5P3FXp=>f3R:P6P7P7P8P9P5P3GYp=5%25R;g00eKR<#=R=#?R>%==#=R=#?R?'<R@,05RA'116?5RB1I:2%7:RC%;C'EP1f4R1#7RC%;Cg00hNRCf5RD/A1g01:nRE39P3%7DRFP4P2%23RG103@RH'1f7RI,A5=9CE]2X741622102@RE'1f6RJ#]W2PJP3P1FVW>P3O1%;FPJPDp-0RFg00fTRK#URL%RKRK1Q45RM%N4RN%L4ROP41:42RPg00g@RQ1K4<R<C3,4ORRPOP6P7P7P8P:EHRS5>ORT%G7RUPRC51FO8RRP3P9g00hnRV,@C1J39=9CVdAD425CMRVb4b5b6X04W111G5P;[^04^1FP310I@PIPDO3b3%8JP?PD1025RGP01<>5,09%8:/09[R0%89/051<>9,0:RC[%81/0:\CAC953P5n2001000000120000000UX94X74P0\G^94^74P3PIP?1O>?102>RI%2?PE[RE[%2>RGg014\R0AP>?5UW2%2@\0^2GP5g01581B2>'@PIeO1PEPLPKPMPNPOPOP6P7P7P8P4P<g01;NPPC3,4OESPUPOPTPUP4PPg00ggRPP<C3,4OC5C5PRPVb4b5b6X04X1F%73g01<5[11;91029[[^04^1FP3f;R9/0@P9PDf9O4b3b8b=b8PLPKPMPNPOP4P<PP1:4>%T=5\4C3,4OR=9>OSPUP=C5PRPVb4b5b6X04X1F115HPA[^04^1FP3f8RF#2PFPJO3b3O4b:PLPKPMPNPOP41:4?PQP<C3,4OROPUPOC5PRPVb4b5b6X0416?3PB[^04P3PJP1O2b3D[CZW<P3O1n200110100021010011102b@W;W2X?4X74o"). Qed.

Lemma lor_byte_testbit : forall a r k, 0 <= a < 2 ^ 8 -> 0 <= r -> 0 <= k ->
  Z.testbit (Z.lor a (Z.shiftl r 8)) k = if k <? 8 then Z.testbit a k else Z.testbit r (k - 8).
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "p'0h04__x1h11bi001bh27__arithh34__ffh48__varmaph55__with62Hah76__sat1h82Hkh92Hrh:6__sat0h;1ah<1kh=1li011lh>1ni021nh?1ri031rh@2r0p;1p;2p;3p;4p;6p;7p;8g002kj1>Tg008lj1?Tg009Jj2ETg009gj20Tg00BCj2<Tg0177j21Tg01<Rj2JTg01=2j25Tg01=Oj2@Tg01=lj26Tg008Rj32Tg01>Ij2BTg01>lR0j2aTg01?Oj1]Tg006Xj1WTg005Xj1VTg00GBj2TTg00G`j1OTg00H>j1NTg00ILj2MTg00Hij29Tg00<7j1ITg01?nj3GTg00Kaj2HTg00C5j2=Tg00LCj2FTg00Loj3KTg00MNj4DTg01@Qj3LTg000Mj68Tg016>j1CTg00Ioj4;Tg003Pj1PTg00K>j3QTg00\Pj7RTg00oVj2STg010>j3`Tg010bj2_Tg019<j6^Tg00Agj2ATg01A8j4\Tg01B?j4XTg01Bdj2YTg01CAj3ZTg00[lj7[Tg00]4j8UTg00_bR1f0R2'Ap=3g00`@R3f1R4g00ggP2C;p=:P4g00cLR5g00ckR6P6g00dKR7P2g00dkF[p=4f3R8P5P6P6P7f2R9P4P2GUp=7%39R:g00eKR;#>R<#?R=%><#>R<#?R>'ER?,09'<g00hNR@f5RA/18f4RB/J>RC/18RD'5P@P@1@B>REf6RF/1BRG16B>,1An0100000020000RH92@2X1@P@168>,1B15G2=2@HX1@1B8>108>1@8>'aPEP@P010A>f9R0f7RE'1RHf8RG16E>RI'1RJ'5P@P@P4PHPJn010000002000052@P410F>RFP@g01:nRKf:RL/1GRM/52=2@MX1@%]HPJg00fTRM#WRN%VMRM1T34RO%O3RP%N3RQ1M3;R;193>RR':,4QRS%I6RTAG3;R1931RU':,4QC71HQ7RVP2P9g00hnRW,=@1F29=2@WdAK314CDRWb3b4b5X03102>R9164>/01[^03P2PGP4O2b29LGIE8W=P2O1%CFP@PK16G>,10RG,52=2@GX1@1=@JPHP0PEPNPMPOPPPQPQP5P6P6P7P3PUg00g@RUP;C;,4QR0193=%P<5Q3,:;,4QFRR<PTP<C7PVPWb3b4b5X03%32R<102?'<%34RH104?'<[^03P2PLPEO2b21S=>101=RE%3>101?[RL[%3=RJg014\R@A`=>4UW6%3?\@^6JP4g01581_1='=PEeO1PLPNPMPOPPPQPQP5P6P6P7PSE^PTP3PRPUP;C;,4QC7PVPWb3b4b5X03g01<5\91A>4[^03P2f;PBO2b2b7b:b7C\E8W>P2O1n10210010300021010111102b1b@PDPBP>P8PNPMPOPPPQP0PTP0C7PVPWb3b4b5X03PH\<^03P2PBP4O2b2CXE81YAC/18AZAC8E8X8:X9:W6X<3X?3X;3o"). Qed.

Lemma lor_byte_low : forall (b : byte) r, 0 <= r -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl r 8)) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "p'0h04__x1h17__arithh21ni001nh34__ffh48__varmaph55__with66__sat1h71bi011bh81Hh93Hb0h:1mh;1xh<2Hah=6__sat0h>2b1h?2b2h@2HbhA2HkhB2HrhC2b0hD1khE1li021lhF1ri031rhG2r0hH1yhI1zp;1p;2p;3p;4p;6p;<p;7p;8p;Bg002kj1ATg003Pj1xTg003nj18Tg01Ccj2wTg00O<j22Tg01DVj1]Tg009gR0j20Tg00BCR1j27Tg008Rj31Tg01E?j3LTg008lj1BTg01<Rj2CTg01Bdj2ITg007lj2qTg01Ecj2lTg009JR2j2=Tg00Ofj2HTg01>Ij2^Tg01=Oj26Tg01>lR3j2[Tg0177j25Tg01=lj2DTg01FIj2UTg006Xj1STg005Xj1RTg00GBj2QTg00G`j1OTg00H>j1NTg00ILj2MTg00Hij2>Tg00Ioj4?Tg00<7j1KTg00Kaj2PTg00C5j23Tg00LCj2JTg00Loj3TTg00MNj4vTg01Fij4uTg001Wj6tTg01GER4j1GTg00COj3pTg00D5j1oTg00DSj4kTg00[Gl<bTg00E6j6aTg00E_j4`Tg00K>j3_Tg01Gcj6cTg000Mj6;Tg01Hhj4dTg016>j1\Tg00oVj2fTg010>j3gTg010bj2hTg019<j6iTg00Agj2FTg01A8j4ZTg01ISj4mTg01J?j3nTg01Jbj2YTg00[lj7XTg00]4j8WTg00Z<l<VTg00ZalBrTg00\Pj7sTg00_bR5f0R6'Fp=4g00hNR7g00hnR8716p=<f1R9g00cLR:g00ckR;P;g00dKR<P6g00dkFXp=9f3R=P:P;P;P<f2R>P9P6GWp=:g01KQR?g00`@R@P@P@P4P4f5R4f4RAP=P>P9P6M<Vp=jP@P@P@P@P@P@P2P6P9P>P2P=PAP4f6R2f7RBf8f9RCMBrp=eP@P9g00g@P6C?p=@P>P:P;P;P<P9P6Fsp=Eg00eKRD#ARE#A#ARF#xRG#8%46RH1wG>12G>RI#4%]G,0I'7%86RI%89RJP1%8>?19612=>12=951@RK[12>912>651@%8=?1>9[RL%8A?1=>\KAL>96P6n2001000000120000000W?W>X2?PL^?J^>I^2?P6PG12GARI%BFRF,C='IRJ,qGRLPAP@1lGJRK12G491@6XI@%BERE/=FRM,HJ1^9F109FRN169F'[16>FP7P310=Ff:R3,2GRO1CCF'IRP/HM/54RQ15O4RR517P910AFRAP715P4RSf;RT,2G/52RU9176X77RVP7P7P7164FRWPR1D4F,5Cn0100000020000PVP7PWP8P11696#<10>9R1[1096RX16>9#<[RY16=>#<\11U96P6n2001000000120000000X:@X2@PY^:@^2@P6P2PFg00fTRY#SR1%RYRY1Q@9R=%O@RZ%N@R[P@1M@DRDg00ggR\1>@FR]C?,9[R^%K;R_P^C:1P[<R`P6P>13781J6>#<dAT@59CvRab3b4b5X0@Rb106FRcPN[^0@RNP6PBP>O2b1O3b8CuA178WP7P8P7P7P6f<,2GR8/5BRW1DBF,5Tn0100000020000=17WX77137U162FP6Etb8PSPOPCP4%4ORS%GGRU,=ERW,0ORT'710OM,7SR>PSPTPSP6X;@RTPFO1Rd,=ERe,0Op-0Rf/3SA1fSSe9pSSP@P@P0PTP0%oXXH@X;@POPO13@OPWPePTPTPTP@P@g00f01=96Ck,3@X:@X2@PEPE13@EPUPdPTPT%G6,3@X;?PGPF13@FEjM:eM<bEaPBC`RBP>P1PYP=PZP[1>@5R?/@D,9[RTP@PDP\1>@E=_@GC?,9[5E[R\P_P\C:P`Pab3b4b5X0@106M,7H%49R\109M'7[^0@P6P8P9O2b1b9R8P1PYP=PZP[PTP_PTC:P`Pab3b4b5X0@RTP\\H^0@R\P6P3PCO2b1PTP\P6P2P4O2b1EcE;PQPPPFP4PbPNP6P2P9O2b1CdE;WEP6O1%\AP7g01:nRAPVP7PAA17A6X77137APRPOP4P8PBP>1fEFR8105ERO%4FRR105M[RA[R7%4ERVg014\R2AgEF9UW<RN%4M\2^<VRVP9g01581h5E'3POeO1ROPAP1PYP=PZP[P[P:P;P;P<P^EiR^P_1@]D,9[RDC:P`Pab3b4b5X0@g01<5\cRc1FF9R9[^0@P6P3P4O2R3b1b6b=b6b9CZE;PQPPPFP4PBP>P8P7PNPVPOPAP1PYP=PZP[P^P_1@?],9[=E[DC:P`Pab3b4b5X0@17R9\c^0@P3b1b6b=b6b9CmE;W2P6O1n10210110300021110211100bCbGXAHXD@7nIA1@KIe12GL1YGJE;O4b8b@WBXF@W7o"). Qed.

Lemma lor_byte_high : forall a r, 0 <= a < 2 ^ 8 -> 0 <= r -> Z.shiftr (Z.lor a (Z.shiftl r 8)) 8 = r.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "h04__x1h17__arithh24__ffh38__varmaph45__with51Hh61bh71xh81yh92Hah:2Hkh;2Hrh<1ah=1kh>1rp;2p;1p;3p;4p;8p;6p;7g00Agj22Tg002kj1<Tg008lj1@Tg009Jj2HTg009gj2DTg00BCR0j2BTg01<Rj2ATg01Bdj2?Tg01Koj2>Tg00AJj25Tg0177j20j1FTg008Rj31Tg01=Oj23Tg01=lj27Tg01LOj2XTg006Xj1WTg005Xj1VTg00GBj2UTg00G`j1RTg00H>j1QTg00Hij2;Tg00ILj2MTg00<7j1LTg011aj3KTg00Kaj2ITg00C5j2=Tg00LCj2JTg00Loj3GTg00MNj4NTg01Fij4OTg01?nj3PTg00Ioj4:Tg0023j8ETg001Wj6STg003Pj1TTg00K>j3_Tg00\Pj7^Tg01Gcj6]Tg000Mj6CTg01Loj4\Tg01J?j3[Tg00[lj7YTg00]4j8ZTg00hNR1f0R2g01:nR331p=9g00`@R4f1R5g00g@P2C:p=8P5g00cLR6g00ckR7P7g00dKR8P2g00dkFYp=4f3R9P6P7P7P8f2R:P5P2GZp=6g00_bR;/25R<g00eKR=#<R>#@R?%<>#<R>#@R@'HRA,D5'BRB1A:@,?9/>@12;2RCP1f5RDf4RE/A@'?RF155@RG'0RH10D:9112X61RIP1P1P113G@RJ10DG17G@,0En0100000020000PIP1PJP3P01352#9125:R0[122513:5#9[RI139:#9\01X52P2n2001000000120000000X84X74PI^84^74P215:@RIP@g00fTR0#WRK%V0R01U45RL%R4RM%Q4RN1;4;RO1M4=R='8,4NRP%L7RQ1;4@RRAK4=RRS'8,4NC61IN8RTP2P:g00hnRU,=11J2:=11UdAG4;5CNRUb2b3b4X0412@G\C^04P2P9P:O2b1O3b5COA113JP1P3P1P1P2f7159@R3'0f6RJ173@'0n010000002000010J9511X61P4P1%FDR3P317I@P:P1\4/=3PKP0PLPMP4AP4SRg01;NP=C:,4NPTPUb2b3b4X04152@/7@=142^04P2P9O1b1GE13I@P2ESb5PHPDPEPGPKP0PLPMPNPNP6P7P7P8PPP4P=g00gg1;4?%T>5_4C:,4NF^R>PQP>C6PTPUb2b3b4X041D2A,BCPB[^04P2PJPEO2b1PKP0PLPMPNPPPQPPC6PTPUb2b3b4X04REP<\C^04RJP2PDP9O2b1PKP0PLPMPNPPPQ18OS,4NC6PTPUb2b3b4X0412;G\C^04P2P:P5O2R2b1E]EC1>F@/05PFP@P5PEPJP2b1C\ECW:X=47[:X;<W9X>4X<4o"). Qed.

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "h01bh11ah21nh31Hh42bsh52IHh67__arithh74__ffh88__varmaph95__witp;1p;2p;4p;7p;3p;5g002kj15Tg003Pj1PTg003nj19Tg005Xj1:Tg01MTj11Tg006Xj18Tg01NQj1BTg00G`j1@Tg00H>j1?Tg00Hij2>Tg00Ioj4<Tg00[lj7;Tg00Kaj2OTg00C5j2NTg00LCj2MTg008Rj3FTg00Loj3ETg00MNj4CTg00Agj27Tg01Bdj23Tg00BCR0j26Tg01Noj2ATg00O<j24Tg008lj1DTg01<Rj22Tg01DVj1GTg009gj2HTg01Ccj2ITg01OSj2JTg01P:j4KTg00T=j3=Tg01PUj5LTg00_bR1f0R2'7p=0g00eK#5#5#5R3#PR4#9R5#:R6P5%12#0R7X46g00fTR8#8%:8g00`@R8#B%@8%?8R9g00cLg00ckR:P:g00dKR:P81>81R;g00g@P;C<g00dkF;1O9:P2f2R:g00hNR9g00hnR;'N1M2:=F9;df1R;9E81CCb7b8b91711P2b6%85#1#0eP013;2#0%0:R1%0;R9'6R<[%02,6913:;#0[R=f3R>/3:#0\<1A;2P2n2001000000120000000X08X18P=^08^18P2144>R=%1:%D3R3'2R<%0=%0<g01KQR<%92R=P014;2R?#0R@%G;,H?14:;#01I;2P;n2001000000120000000W0W2P@^0=^2<P2P4f4O2b3P012;2#0P1[12:;#0\9R912>:#0\11J;2P2n2001000000120000000X28X18P9^28^18P2%1>P3P:O3b3CKO3b3A=5:;#1#0eX57X46X05P2DLW4o"). Qed.

Lemma Z_to_le_bytes_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "h04__x1h12bsh21xh33Hb0h47__arithh54__ffh68__varmaph75__with81bh92Hbh:2Hrh;2IHh<1lh=1mh>1nh?1yh@1zp;1p;2p;3p;6p;4p;<p;7p;5p;Bp;8g002kj1<Tg003Pj1gTg003nj1VTg005Xj1@Tg00jUj29Tg01MTj13Tg01Q7j26Tg008Rj32Tg006Xj1ATg00C5j20Tg01R4j1KTg00Agj27Tg01Ccj2HTg00O<j28Tg01DVj1cTg009gR0j21Tg00BCj25Tg008lj1ETg01<Rj2GTg01Bdj2DTg01Koj2CTg00T=j34Tg000Mj6;Tg01GER1j1BTg009JR2j2:Tg00COj3UTg00D5j1TTg00DSj4STg00[Gl<NTg00E6j6JTg00E_j4LTg00GBj2MTg00G`j1ITg00H>j1OTg00Hij2>Tg00ILj2RTg00Ioj4?Tg00K>j3fTg00\Pj7eTg00<7j1dTg00Kaj2bTg00LCj2_Tg00Loj3]Tg00MNj4\Tg01S=j4[Tg007lj2ZTg01T?j3YTg01PUj5^Tg00Z<l<XTg00ZalB`Tg00[lj7aTg00]4j8WTg01KQR3g00`@R4P4P4P1P1f5R1f4R5f3R6f2R7f1R8f0R9M<Xp=QP4P4P4P4P4P4P2P9P8P7P2P6P5P1f6R2f7f8f9MB`p=PP8g00cLR:g00ckR;P;g00dKR<P9g00dkFap==P6P:P;P;P<P7P8P9GWp=Fg00eKR=#<R>#<#<R?#gR@#VRA#@RBPA19A9%39'6=2B9RCX1B%AA,0B%K8g00_bRD%38'71H@618@6RE,7D%c@,1E'5PAP519A5RE18@1%35%E?R?'G'D/C?'694A9A4A15RF52BX8AP4%36RG16E994A1=2BFX@4PBP6A4A19=2BFX<BA4A56,0B19A6/6GP7E;18@5RF1GG?'DRE/C?PFPG17DFRH%E>R>%B@RI':RJ,1FRK'51:>?RL,1F,5HRMPHPKPHP9X24RKP?O1RN,:>RO,1Fp-0RP/0HA2PHHe9UHHP4P4P0PKP01189#TX?4X24PFPF104FPJPOPKPKPKP4P4g00f01:89CS,04X=4X>4P>P>104>PIPNPKPK%B9,04X23P@P?104?EQM:PM<NEJP9CLR?PMg00fTR3#ARK%@3R31M48RN%I4RI%O4ROPOP:P;P;P<P41>4Dg00g@1R4=R=C?,=OR:P4P=g00gg1>4>=f4@C?,=OFeR>%d;R;P>CF1bO<R<P9P7g00hNR>g00hnR='01_97=2>=dA]4D8C\R=b5b6b7X0417D9R>119L'517D8RD118L'5[^04P918@2P8O2b4b3P?PMPKP3PNPIPOP:P;P:CFP<P=b5b6b7X04PD\>^04P9%31P6O2b4b3C[E;1Z@EAY5G8E;b9b:A4A78R8,9A%38'6=2B8eX;CX1BX8AP9D^W1o"). Qed.

Lemma bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "h01Eh17__arithh24__ffh38__varmaph45__with54__x1h61ah71bh84cstrh91Hh:2bsh;1lh<5lemmah=1xh>1yp;1p;2p;3p;6p;4p;:p;8p;7g002kj1;Tg003Pj1eTg003nj1PTg005Xj1@Tg00jUj22Tg01MTj13Tg01R4j1RTg01U@j3OTg01Q7j2>Tg008lj1?Tg00@jj11Tg01VFj25Tg009Jj28Tg00Ofj20Tg008Rj34j1VTg01Vcj1YTg001Wj6XTg01X3j4UTg01XQj4ATg01Y8j3QTg01Yij4=Tg01Z`j3NTg01[Vj2MTg01\Bl:LTg009gR0j27Tg00Agj26Tg01\oj3ITg00n2j1HTg006Xj1JTg01NQj1KTg00G`j1GTg00H>j1FTg00Hij29Tg00Ioj4<Tg00Kaj2ETg00C5j2DTg00LCj2STg00Loj3TTg00MNj4dTg01]Vj2CTg01^?j1BTg01^^j3cTg01_Gj2bTg01`3j2aTg00T=j3ZTg00GBj2[Tg00ILj2\Tg00<7j1WTg01`_j3]Tg00]4j8^Tg00oVj4_Tg00[lj7`Tf1R1g00cLR2g00ckR3P3g00dKR4f0R5g00dkF`p=:g00eKR6#;R7#;#;R8#e#PR9#@R:1295R;%35R<%R53Og00`@R=1>;<#3%?7R7%?8R8%1;'5'8,0<34P:1291R;%31R>'>f2R?#3R@129?#1,58,87'0RA94=<X;:P5P1%Y1EX%1;,58,87,0>94=>A4=@Ap-0RA^>=R@^==R>P=P@%V=R;P=PAP;PAPAPAg01aBR;CUR:CAR<CARBP=P@P<P=PAP:g01a`9QA;C=C=9N>BP0f3R0#3RB1290R>#1R;,58RA,87R:,0BP5P:P:1M=:M:LW<P5g00_bR</75R@g00BC10?1RC,6<17C1RC100?/7?AI?15P5n2001000000120000000UX7=X6=PC\@^7=^6=P5PBP:P7PA%H>R>16<;R;g00fTRA#JR:%@ARB%K=%G=R@%F=RCP=19=<R0g00gg19=7C<':1EC4RDP5P?g00hNREg00hnRF'D1S5?=4EFdAT=<1CdRFb2b3b417<7P5b1b8P>P;g00bmR;,C=R>%B;#B,C=9c=>g01bQ'b'a=ZA:PB1[=1P@PCP2P3P3P4P=P0g00g@R41\=6R6C<,:C%W3P=P0P419=8=]=6C<,:CG^PDPFb2b3b4X5=16<51581,6<[^5=P5f5,29#1P1O2b1b8C_O3b9O2b0b0W:o"). Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) ["LeRoundtrip"] "h01nh11xh21Bh34__x1h41mh51yh62B0h71Lh82L0h91Nh:7__arithh;4__ffh<8__varmaph=5__with>2bsh?4cstrh@1zp;1p;2p;3p;6p;<p;4p;7p;Bp;8g002kj16Tg003Pj1DTg003nj1YTg005Xj1?Tg00jUj27Tg01^?j12Tg008Rj30j1=Tg01c=j1XTg01MTj19Tg008lj1<Tg00@jR0j15Tg01VFR1j28Tg009JR2j23Tg009gR3j21Tg001Wj6HTg01R4j1lTg00Agj2:Tg01Ecj2_Tg01Q7j2;Tg01Vcj1]Tg01GEj1[Tg00Ofj2ZTg00D5j1WTg00[Gl<@Tg00E_j4>Tg00m2j2PTg00mUj3OTg00n2j1NTg006Xj1MTg00GBj2QTg00G`j1RTg00H>j1LTg00ILj2STg00Hij2ATg00K>j3oTg00Ioj4KTg00<7j1nTg00\Pj7mTg00Kaj2kTg00C5j2ETg00LCj2hTg00Loj3bTg00MNj4aTg00BCj2FTg00PFj3`Tg000Mj6ITg007lj2cTg00O<j2^Tg01Jbj2dTg01dEj1eTg01eEj1\Tg00DSj4fTg00Z<l<gTg00ZalBGTg00[lj7iTg00]4j8jTg00`@R4f0R5'Ep=4P4P4g00f0P5Cfp=Bg00`^R6P4P4P4P0P0f5R7f4R8f3R9f2R:f1R;P5M<gp=VP4P4P4P4P4P4P1P5P;P:P1P9P8P7f6R1f7R<f8R=f9R>MBGp=UP4P4P4P4P4P4P2P5P;P:P2P9P8P7P1P<P=P>MBGp=TP;g00cLR>g00ckR<P<g00dKR2P5g00dkFip=JP9P>P<P<P2P:P;P5Gjp=Cg00eKR?#6R@#6#6RA#D#YRB#?RC17B5g00bm#2#2#2#2#2#2#2#2RD506%X;%9;%<@R@%<ARE17B;#5'8'3'1P617B:%99RF%55RG,8E,3@'1X06P5PDP;EH%9:%5DRH,8ERI,3@RJ'1%l9g00_bRK/:FP4%6A#6#6RA#DRF%98RL'_RM1;D5=0C7X@4RNP4PLPNP617B8%97,;5=0C7X06%]8PDP9EH%[F,3@RN,ZL11LJ18EE,3@,1LROP4P4P3P5X14RPP311;5#WX54X14PLPL%4LPJPPPEO1RJ,8ER3,3@PPPPPP13;5#B#4X44X04P@P@%4@PIP3PPPPPP18;5#B#4X44X04PEPE%4ER3PHPJPPPP%4GX16PDPEP3EVM:UM:TM<@P;C>PO17B7R7=06D%57RO=04ERPP6P4%=6P0%=4%5;=04GA06;51P;53OX56X16P7PO%4OPDPEP3M<@P8C>PP17B1RB#N%5B,:Kg00fTRB#M%?B1Q4;%R4%L4RBP41S4?R?g00gg1A4@=o4FCK,JBR1%n<RPPBP41A4Kg00g@P?CK,JBR?PPPBP>P<P<P2P?P1FmCCCC1kB2P5P:g00hNRBg00hnR2'E1h5:=0B2dAb4K;Cab;b<b=X34%<A,3@R@,151:K;1:K:11:@'F[[^34P5%9=P9P8O3b:b?b8b61:KL11LN'Fe9`LNEI1;DM=0C8e1cFL,^F1dFLEIb9b2b2%e;#\=0C;eW7W>o"). Qed.
End LeRoundtrip.

(* [comment removed for export] *)
Definition canary_bytes (cr : word) : list byte := firstn 1 (le8 cr) ++ [Z_to_bv 8 0] ++ skipn 2 (le8 cr).
Definition canary_of (cr : word) : word := le_bytes_to_word (canary_bytes cr).
Lemma canary_bytes_length : forall cr, length (canary_bytes cr) = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) [] "h01nh12crp;1p;3p;2p;6g002kj13Tg003Pj18Tg003nj1:Tg01^?j12Tg01eEj1>Tg01f5j3;Tg00jUj20Tg007lj2BTg006Xj1@Tg00T=j3?Tg01fTj37Tg01g2j39Tg00B^j21Tg01gOj26Tg01gfj2=Tg00C5j2GTg01h=j1FTg000Mj65Tg01i4j3ETg01iUj3DTg01j7j3<Tg01jVj1ATg008Rj3CTg00`^R0f1R1f0R23Cp=4g00eK#3#3#3R3#3#3#3#8#:P0%83R3#:R4g00bm#2R5%>2R65;4R7'0R8g00_b,B3%@45?4R3%25R9=746R:594R;,04R<'1%29#2#2#2#2#2R=,42X00P01043R>104:R?'1%>1R19;45,04/12/4=X00P01046R@,65A7491,04,1>,12/4=X00P01=@91041,6511>2'1/4=X00P0P=16521=29,1>'1/4=X001G0=P@%F2E5P?AE496E5P8AD456E5P<A<43:E5A947;,04A<47;E5%A2,04/4=eW1o"). Qed.
Lemma canary_recast_bytes : forall cr,
  cells_bytes [C8 (canary_of cr)] = cells_bytes [CB 1 (firstn 1 (le8 cr)); C1 (Z_to_bv 8 0); CB 6 (skipn 2 (le8 cr))].
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_B ()) [] "h01lh12crp;1p;3p;2p;6g002kj13Tg003Pj1>Tg003nj1:Tg005Xj1@Tg01jVj1HTg006Xj1<Tg01g2j30Tg01^?j12Tg01eEj15Tg01f5j39Tg007lj2?Tg01fTj38Tg00T=j31Tg008Rj34Tg00C5j2GTg01kWj2=Tg000Mj66Tg01dEj1FTg01l5j1ETg01m=j2DTg01nFj1CTg01oDj1BTg0209j1;Tg00X4j27Tg0213j1ATg00eK#3#3#3R0#3#3#3#>#:%>0R0#:R1#@R2f0R3#HR4%<1R59013g00bm#2R6f1#5R7591R8g00_b,?0R0%26R9=817R7=015511501R:542X02P2%53R;9916R<A1105R=A819;R;501501R>A423:X02P2P;A01=79018A11039018542X02A110;901<,G2A01;5R81=1;E6A01>51=1>E6A0145A1108901<R8542e%F4#5%E3,D4E6%C3R3#5=015=428eg00^mR8%B3%<8R331#;176<%A0%29#2#2#2/7;=183518518#;542eW1o"). Qed.

Definition rinit_ssp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R : Z) (cr : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x5bb18); (0x3b890, 0x3b898)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
    /\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells rsegs m' RTD (rtd_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (canary_of cr) x10 x11)
    /\ bytes_at rsegs m' R (le8 cr).

Lemma rinit_ssp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (cr : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (junk : list byte),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m R (le8 cr) ->
  rw_cells rsegs m RGUARD [CB 8 junk] ->
  rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
  rw_cells rsegs m RTD (td_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11) ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 R ->
  (lo <= bv_unsigned sp - 16)%Z -> (0x5d000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
  evt rsegs (rinit_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R cr x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21a84) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
  unfold td_cells in TDC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x5bb18); (0x3b890, 0x3b898)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
 carve_frame 16%nat ST.
  lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  do 4 lstep.
  lstep. call (rmemcpy_specZ RGUARD R 8); [exact RND | rewrite length_le8; reflexivity | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
  lstep. lstep. lstep. lstep.
  apply (rw_cells_recast rsegs _ _ _ [C8 (canary_of cr)]) in GU;
    [| cbn; repeat split; exact I | apply canary_recast_bytes | reflexivity].
  lstep. lstep. lstep.
  do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
  unfold rinit_ssp_post, rtd_cells. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pauxv20 (hw uid rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10; Z_to_bv 64 16; hw;
   Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].

Notation RENVIRON := 0x3b7d0%Z (only parsing).
Notation RPROGNAME := 0x5bb20%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x5bb98%Z (only parsing).
Notation RGOT3 := 0x2a500%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x2110c) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x21100) fc None m (seg_rom rsegs)).
Proof.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 rsegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 rsegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed.





Section RInitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 uid hw cr : word) (gjunk : list byte).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x3b7d8); (RTD, 0x3b928); (0x5b8b0, 0x5b8e0);
                 (RGUARD, 0x5bb18); (RPROGNAME, 0x5bb30); (RLIBC, 0x5bba0)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition rinit_libc_post : Z -> machine_state -> Prop :=
    fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x3b850) (Z_to_bv 64 0x5bb68) (canary_of cr) (Z_to_bv 64 0x3b8b0) z64)
    /\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
    /\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells rsegs m' RSYSINFO [C8 z64]
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
    /\ rw_cells rsegs m' RHWCAP [C8 hw]
    /\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
    /\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
    /\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x5bb28); C8 (Z_to_bv 64 RPROGNAME)]
    /\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
    /\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 R)))
    /\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
    /\ bytes_at rsegs m' R (le8 cr)
    /\ (0 < t < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x5d000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x210f4) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 (* [comment removed for export] *) x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x211d0) fc None m' (seg_rom rsegs)
    /\ munch [(RPROGNAME, 0x5bb28)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x5bb28)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
    bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x210f4) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x211c4) fc None mm (seg_rom rsegs)).
Proof.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia).
      unfold rpn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac rscan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  Lemma rinit_libc_spec : forall tp a0 a1,
    stk rsegs m lo (bv_unsigned sp) ->
    bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 R))) ->
    bytes_at rsegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at rsegs m R (le8 cr) ->
    rw_cells rsegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells rsegs m RHWCAP [C8 hw0] ->
    rw_cells rsegs m RENVIRON [C8 env0] ->
    rw_cells rsegs m RSYSINFO [C8 z64] ->
    rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells rsegs m RGUARD [CB 8 gjunk] ->
    rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x5bb28); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x210c8) fc None m (seg_rom rsegs)).
Proof.
    intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
    unfold td_cells, libc_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. cbn [length pauxv20] in EB.
    pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
    pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
    pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
    iprefix.
 carve_frame 384%nat ST.
    do 10 lstep.
    apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
    replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
    lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
    apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    lstep. lstep. lstep.
    eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
    lstep. lstep. lstep.
    pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
    apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    rscan_it AUXB 1%nat 2%nat. rscan_it AUXB 3%nat 4%nat. rscan_it AUXB 5%nat 6%nat. rscan_it AUXB 7%nat 8%nat.
    rscan_it AUXB 9%nat 10%nat. rscan_it AUXB 11%nat 12%nat. rscan_it AUXB 13%nat 14%nat. rscan_it AUXB 15%nat 16%nat.
    rscan_it AUXB 17%nat 18%nat.
    steps_to 0x21184%Z.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    steps_to 0x211c4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
    rename POST into G2. try rename MI0 into MI.
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
    cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
    replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
    replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
    lstep. lstep.
    name_sp sp (-384)%Z. name_sp sp (-336)%Z.
    icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp; unname_sp
         | |- _ => unname_sp; unname_sp;
                   first [ hyp_by_addr | reflexivity | lia
                         | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                             replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
         end.
    rename PC into ST. unfold td_cells, libc_cells in *.
    lstep. lstep.
    call_sp (rinit_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R cr).
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- ?g => first [ hyp_by_addr | reflexivity | lia ]
         end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
    do 5 lstep.
    join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
    release_frame FRlo ST (bv_unsigned sp).
    lstep.
    unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
    all: hyp_by_addr.
  Qed.
End RInitLibc.

