(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the libc start-up's auxv scan over the revision's launch auxv, both CONFIG_RSEQ layouts; 10 recorded proofs replaced by written proofs (testbit_small_high, lor_byte_testbit, lor_byte_low and 7 more); rinit_libc_spec restated for the revision's model; adds pauxv_length; rinit_libc_post redefined for the revision's model; defines pauxv). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_memset F_memcpy Startup_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Startup_B () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List6nth_okK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib5Plain9Startup_B=rmemsetZ_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C47Corelib4Init3Nat3addK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib5Plain8F_memset;memset_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_memset;memset_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib5Plain9Startup_B=rmemcpyZ_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5Plain8F_memcpy;memcpy_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5Plain8F_memcpy;memcpy_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6shiftlC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00C46Stdlib4Bool4Bool;orb_false_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z=testbit_neg_rc59OSSVerify5KrLib5Plain9Startup_BBtestbit_small_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lor_specC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4of_Nc59OSSVerify5KrLib5Plain9Startup_B@lor_byte_testbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z;shiftr_specC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z=shiftl_nonnegK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib5Plain9Startup_BDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B=lor_byte_highC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B<lor_byte_lowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemIbytes_le_to_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib5Plain9Startup_BKZ_to_le_bytes_bytes_le_to_ZC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib5Plain9Startup_BCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List:length_appc59OSSVerify5KrLib5Plain9Startup_B<canary_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib5Plain9Startup_BCcanary_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_BDle8_le_bytes_to_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B9canary_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit8td_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B>rinit_ssp_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast=munch_write_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast;stk_write_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c59OSSVerify5KrLib5Plain9Startup_B=rmemcpy_specZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC59OSSVerify5KrLib3Lib4Step>store_bytes_1'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_BCcanary_recast_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib6Common;Startup_kit6rd_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I46Stdlib5Lists4List6Exists00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib5Plain9Startup_B8rpn_postC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app2C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib3Lib3MemAzext_extract_byteC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Peano2ltC46Stdlib5Lists4List>nth_error_app1C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib3Lib7ZBridge5zr_bvC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC47Corelib4Init9Datatypes7nat_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib5Plain9Startup_B7pauxv20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit:libc_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B=rmemset_specZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit9rd_u64s_gC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib3Lib8PropExec6v_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib5Plain9Startup_B8rpn_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=stk_lo_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Startup_A>rinit_tls_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9Startup_A>rinit_tls_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B?rinit_libc_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B>rinit_ssp_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit9rtd_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit>impl_epost_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim9ex_elim_2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9Startup_B@renvp_count_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8alu_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK4ELinuxProcessSemantics5Riscv5Instr5aluop03K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := PImg.psegs.
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
        F (Z_to_bv 64 0x24e34) fc None m (seg_rom rsegs)).
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
        F (Z_to_bv 64 0x24a30) fc None m (seg_rom rsegs)).
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
Notation RGOT_SSP := 0x264b0%Z (only parsing).
Notation RGUARD := 0x57aa0%Z (only parsing).


(* [comment removed for export] *)
Section LeRoundtrip.
Local Open Scope Z_scope.
Lemma testbit_small_high : forall a k, 0 <= a < 2 ^ 8 -> 8 <= k -> Z.testbit a k = false.
Proof.
  intros a k Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_byte_testbit : forall a r k, 0 <= a < 2 ^ 8 -> 0 <= r -> 0 <= k ->
  Z.testbit (Z.lor a (Z.shiftl r 8)) k = if k <? 8 then Z.testbit a k else Z.testbit r (k - 8).
Proof.
  intros a r k Ha Hr Hk. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec0 k 8).
  - rewrite (Z.testbit_neg_r r (k - 8)) by lia. apply orb_false_r.
  - rewrite (testbit_small_high a k) by lia. reflexivity.
Qed.

Lemma lor_byte_low : forall (b : byte) r, 0 <= r -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl r 8)) = b.
Proof.
  intros b r Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.ltb_spec0 k 8).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite lor_byte_testbit by lia.
    replace (k <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite (testbit_small_high (bv_unsigned b) k) by lia. reflexivity.
Qed.

Lemma lor_byte_high : forall a r, 0 <= a < 2 ^ 8 -> 0 <= r -> Z.shiftr (Z.lor a (Z.shiftl r 8)) 8 = r.
Proof.
  intros a r Ha Hr. apply Z.bits_inj'. intros k Hk.
  rewrite Z.shiftr_spec by lia. rewrite lor_byte_testbit by lia.
  replace (k + 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma Z_to_le_bytes_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg bs) as Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite lor_byte_low by exact Hr. rewrite lor_byte_high by lia. rewrite IH. reflexivity.
Qed.

Lemma bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs.
  pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)) as E.
  rewrite Z_to_le_bytes_bytes_le_to_Z in E. rewrite E at 1.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (bytes_le_to_Z_nonneg bs) as N.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.
End LeRoundtrip.

(* [comment removed for export] *)
Definition canary_bytes (cr : word) : list byte := firstn 1 (le8 cr) ++ [Z_to_bv 8 0] ++ skipn 2 (le8 cr).
Definition canary_of (cr : word) : word := le_bytes_to_word (canary_bytes cr).
Lemma canary_bytes_length : forall cr, length (canary_bytes cr) = 8%nat.
Proof. intros cr. unfold canary_bytes. rewrite !length_app, length_firstn, length_skipn, length_le8. reflexivity. Qed.
Lemma canary_recast_bytes : forall cr,
  cells_bytes [C8 (canary_of cr)] = cells_bytes [CB 1 (firstn 1 (le8 cr)); C1 (Z_to_bv 8 0); CB 6 (skipn 2 (le8 cr))].
Proof.
  intros cr. cbn [cells_bytes cbytes app]. unfold canary_of. rewrite le8_le_bytes_to_word by apply canary_bytes_length.
  unfold canary_bytes. rewrite !app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition rinit_ssp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R : Z) (cr : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x57aa8); (0x37820, 0x37828)]%Z m m'
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
  (lo <= bv_unsigned sp - 16)%Z -> (0x59000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
  evt rsegs (rinit_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R cr x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1da08) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
  unfold td_cells in TDC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x57aa8); (0x37820, 0x37828)]%Z m) as MU.
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
(* The 08b1429 auxv as a word list: 27 pairs, or 29 with CONFIG_RSEQ. *)
Definition pauxv (la : LaunchAuxv) (entry uid gid hw rnd efn : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries la p_phdrs entry uid gid hw rnd efn).
Lemma pauxv_length : forall la entry uid gid hw rnd efn,
  length (pauxv la entry uid gid hw rnd efn) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros [ehdr c msz [|]] ? ? ? ? ? ?; reflexivity. Qed.

Notation RENVIRON := 0x37760%Z (only parsing).
Notation RPROGNAME := 0x57ab0%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x57b28%Z (only parsing).
Notation RGOT3 := 0x26488%Z (only parsing).       (* [comment removed for export] *)

Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1d090) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1d084) fc None m (seg_rom rsegs)).
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
            (pn0 pnf0 hw0 env0 uid hw cr : word) (gjunk : list byte)
            (la : LaunchAuxv) (entry gid efn : word).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x37768); (RTD, 0x378b8); (0x57840, 0x57870);
                 (RGUARD, 0x57aa8); (RPROGNAME, 0x57ac0); (RLIBC, 0x57b30)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

Definition rinit_libc_post : Z -> machine_state -> Prop :=
fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
(Z_to_bv 64 0x377e0) (Z_to_bv 64 0x57af8) (canary_of cr) (Z_to_bv 64 0x37840) z64)
/\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
/\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' RSYSINFO [C8 z64]
/\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
/\ rw_cells rsegs m' RHWCAP [C8 hw]
/\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
/\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
/\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x57ab8); C8 (Z_to_bv 64 RPROGNAME)]
/\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
/\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
/\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv la entry uid gid hw (Z_to_bv 64 R) efn))
/\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
/\ bytes_at rsegs m' R (le8 cr)
/\ (0 < t < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x59000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x1d078) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 (* [comment removed for export] *) x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1d154) fc None m' (seg_rom rsegs)
    /\ munch [(RPROGNAME, 0x57ab8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x57ab8)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
    bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x1d078) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1d148) fc None mm (seg_rom rsegs)).
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
  (* A key above AT_CNT-1 (37): the loop skips the store and loads the next key. *)
  Ltac rskip_it AUXB ki := lstep; if_true; ldaux AUXB ki; lstep; astep.

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
    bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (pauxv la entry uid gid hw (Z_to_bv 64 R) efn)) ->
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
    rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x57ab8); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d04c) fc None m (seg_rom rsegs)).
Proof.
    intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
    unfold td_cells, libc_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8, pauxv_length in EB.
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
    unfold pauxv, auxv_entries in AUXB.
    try change (Z_to_bv 64 (Z.of_N (ph_addr p_phdrs))) with (Z_to_bv 64 0x10040) in AUXB.
    try change (Z_to_bv 64 (Z.of_N (ph_ent p_phdrs))) with (Z_to_bv 64 56) in AUXB.
    try change (Z_to_bv 64 (Z.of_N (ph_num p_phdrs))) with (Z_to_bv 64 10) in AUXB.
    unfold AT_SYSINFO_EHDR, AT_L1I_CACHESIZE, AT_L1I_CACHEGEOMETRY, AT_L1D_CACHESIZE, AT_L1D_CACHEGEOMETRY,
      AT_L2_CACHESIZE, AT_L2_CACHEGEOMETRY, AT_L3_CACHESIZE, AT_L3_CACHEGEOMETRY, AT_MINSIGSTKSZ,
      AT_HWCAP, AT_PAGESZ, AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY,
      AT_UID, AT_EUID, AT_GID, AT_EGID, AT_SECURE, AT_RANDOM, AT_EXECFN,
      AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN, AT_NULL in AUXB.
    (* Both kernels: with CONFIG_RSEQ the loop runs two iterations more. *)
    destruct (la_rseq la) eqn:HRSEQ; try rewrite HRSEQ in AUXB; cbv zeta in AUXB; cbn [app flat_map fst snd] in AUXB.
    all: ldaux AUXB 0%nat; lstep; if_false; lstep; lstep; lstep; lstep.
    all: rscan_it AUXB 1%nat 2%nat.
    all: rskip_it AUXB 4%nat; rskip_it AUXB 6%nat; rskip_it AUXB 8%nat; rskip_it AUXB 10%nat; rskip_it AUXB 12%nat.
    all: rskip_it AUXB 14%nat; rskip_it AUXB 16%nat; rskip_it AUXB 18%nat; rskip_it AUXB 20%nat.
    all: rscan_it AUXB 21%nat 22%nat; rscan_it AUXB 23%nat 24%nat; rscan_it AUXB 25%nat 26%nat; rscan_it AUXB 27%nat 28%nat.
    all: rscan_it AUXB 29%nat 30%nat; rscan_it AUXB 31%nat 32%nat; rscan_it AUXB 33%nat 34%nat; rscan_it AUXB 35%nat 36%nat.
    all: rscan_it AUXB 37%nat 38%nat; rscan_it AUXB 39%nat 40%nat; rscan_it AUXB 41%nat 42%nat; rscan_it AUXB 43%nat 44%nat.
    all: rscan_it AUXB 45%nat 46%nat; rscan_it AUXB 47%nat 48%nat; rscan_it AUXB 49%nat 50%nat; rscan_it AUXB 51%nat 52%nat.
    1: (rscan_it AUXB 53%nat 54%nat; rscan_it AUXB 55%nat 56%nat).
    all: steps_to 0x1d108%Z.
    all: astep. all: if_cases K; zify_cond K; [|exfalso; lia]. all: clear K.
    all: astep. all: if_cases K; zify_cond K; [|exfalso; lia]. all: clear K.
    all: steps_to 0x1d148%Z.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
    all: rename POST into G2. all: try rename MI0 into MI.
    all: apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. all: destruct AUX as [AUXa AUX].
    all: apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. all: destruct AUX as [AUX3 AUXb].
    all: cbn [cells_size csize Nat.add] in AUX3, AUXb. all: change (Z.of_nat 24) with 24%Z in *.
    all: replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
    all: replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
    all: lstep. all: lstep.
    all: name_sp sp (-384)%Z. all: name_sp sp (-336)%Z.
    all: icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp; unname_sp
         | |- _ => unname_sp; unname_sp;
                   first [ hyp_by_addr | reflexivity | lia
                         | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                             replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
         end.
    all: rename PC into ST. all: unfold td_cells, libc_cells in *.
    all: lstep. all: lstep.
    all: call_sp (rinit_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R cr).
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- ?g => first [ hyp_by_addr | reflexivity | lia ]
         end.
    all: match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    all: do 3 lstep. all: if_false. all: lstep. all: lstep. all: lstep. all: if_false. all: lstep. all: lstep. all: if_true.
    all: do 5 lstep.
    all: join2 FRlo AUXa. all: join2 FRlo AUX3. all: join2 FRlo AUXb. all: join2 FRlo FRhi.
    all: release_frame FRlo ST (bv_unsigned sp).
    all: lstep.
    all: unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. all: sys_finish; try lia.
    all: hyp_by_addr.
  Qed.
End RInitLibc.

