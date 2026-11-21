(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import F_syscalls RMallocRep.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_mm_syscalls () := "C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP@alloc_ceiling_loC13~~~I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_carveC13~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls<rvmwait_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C56Stdlib6ZArith6BinInt1Z3powK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C47Corelib5Lists7ListDef6firstnK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;stk_releaseC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib5Lists7ListDef5skipnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls7RVMLOCKC13~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8mmap_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes7at_nodeC13~~~I:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0;C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode:dec_munmapC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5enodeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls<rmunmap_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5epostC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_mm_syscalls;mmap_len_geC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4nretC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep=stk_lo_nonnegC13~~~C56Stdlib6ZArith6BinInt1Z4of_NC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls<rvmwait_specC13~~~K46Stdlib9micromega5Tauto8GFormula01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame=disjoint_fromC13~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6sub_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame<munch_weakenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_evenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState5MSsvcC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4aregC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode?dec_munmap_SomeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes6efferrC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4eff0C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans01C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls;sysret_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls;sysret_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep:sysret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8errno_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6DecodeBerrno_of_errno_retC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7w_addiwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep>apply_mem_noneC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4tsetC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep:nret_MSsvcC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepErw_cells_unmaps_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep@stk_unmaps_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep<munch_unmapsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep>mem_inv_unmapsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep<sysret_errnoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode<errno_of_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep@apply_mem_unmapsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep9evt_ecallC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree:impl_enodeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameBrw_cells_transportC13~~~K46Stdlib9micromega5Tauto8GFormula07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node00C13~~~I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op205C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4respC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmunmap_entryC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4landC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_mm_syscalls:land_m4096C13~~~C56Stdlib6ZArith6BinInt1Z9land_commK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0<C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode<dec_mprotectC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls>rmprotect_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls>rmprotect_argsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6DecodeAdec_mprotect_SomeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_mm_syscalls@mmap_len_alignedC13~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepAref_ro_addr_falseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7ro_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepDrw_cells_zeros_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep9stk_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep;munch_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep;wmono_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep=mem_inv_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepBrw_cells_zeros_newC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep?apply_mem_zerosC13~~~C47Corelib5Lists7ListDef6repeatC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RPAGE_SIZEC13~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep?rmprotect_entryC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode=dec_mmap_noneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8dec_mmapC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls?rmmap_anon_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_andiC13~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_andiC13~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6DecodeBdec_mmap_none_SomeC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8mmap_ans01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8mmap_ans02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode=dec_mmap_SomeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_xoriC13~~~C56Stdlib6ZArith6BinInt1Z4lxorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_xoriC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_orC13~~~C56Stdlib6ZArith6BinInt1Z3lorC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6alu_orC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge7zr_wordC13~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z7lor_0_lC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge<zb_lxor_onesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStepBunsigned_errno_retC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6DecodeAmmap_addr_ok_trueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode6avoidsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeAunsigned_lit_landC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls;land_ones64C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node0:C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode<mmap_addr_okC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8mmap_ans00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmmap_entryC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_mm_syscalls@rmmap_fixed_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_mm_syscalls;fixed_shapeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_lorC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge7zr_lxorC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iff".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RVMLOCK : Z := 0xebc34.
Definition rvmwait_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RVMLOCK [C4 (Z_to_bv 64 0)].

Lemma rvmwait_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z -> (alloc_ceiling <= lo)%Z ->
  evt rsegs (rvmwait_post ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xaeb58) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST VML MI LO CEILJ. pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 7 step.
  step. if_cases KVW; zify_cond KVW. 2:{ exfalso. rewrite ?unsigned_lit in KVW by lia. first [lia | apply KVW; reflexivity]. }
  clear KVW.
  do 5 step.
  release_frame FR ST (bv_unsigned sp).
  unfold rvmwait_post. finish.
Qed.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.

Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] -> (alloc_ceiling <= lo)%Z ->      (* [comment removed for export] *)
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 64)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR MI VML CEILJ -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in VML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step.

  step.
  call_sp rvmwait_spec; [exact ST | unfold RVMLOCK; exact VML | exact MI | lia | lia | ]. unfold RVMLOCK in *.
  match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ 0xebc34 _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
  do 3 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells rsegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z
       | RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

Lemma rmprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (A + L <= 0x10000 \/ 0xec000 <= A)%Z ->
  (0xec000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMprotect A L P) (dec_mprotect A L))
       (epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr rsegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2
        /\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose_ceil.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; exact D. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    pose_ceil. pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono rsegs m m')
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] -> (alloc_ceiling <= lo)%Z ->      (* [comment removed for export] *)
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 96)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DEC ST ERR MI VML CEILJ -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in VML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step.

  step.
  call_sp rvmwait_spec; [exact ST | unfold RVMLOCK; exact VML | exact MI | lia | lia | ]. unfold RVMLOCK in *.
  match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ 0xebc34 _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
  do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv rsegs ?mm |- mem_inv rsegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk rsegs ?mm ?a ?b |- stk rsegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells rsegs ?mm ?a ?c |- rw_cells rsegs ?mm _ _ => exact H end.
Qed.
End CEIL_WRAP_1.

