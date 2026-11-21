(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F F_am_G F_am_H.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C RF_am_F RF_am_G.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_am_H () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~K47Corelib4Init9Datatypes3nat02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr08K47Corelib7Numbers7BinNums1Z03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums8positive03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums1Z01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RMLOCKC13~~~K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate03C13~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K46Stdlib9micromega6VarMap1t01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~C56Stdlib6ZArith6BinInt1Z9add_assocK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes7at_nodeC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node09C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8dec_brk0C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4nretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState5MSsvcC13~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv3Sem7reg_getC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4aregC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode=dec_brk0_SomeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4eff0C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep>apply_mem_noneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep:mkR_set_a0C13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep:nret_MSsvcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep9evt_ecallC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree:impl_enodeC13~~~I:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5enodeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_H9rbrk_regsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5epostC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4respC13~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode7dec_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_H7brk_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode<dec_brk_SomeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode=brk_new_pagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode8zeros_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SysStep?apply_mem_zerosC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_H7brk_resC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode7brk_ans00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode7brk_ans01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode7brk_ans02C13~~~C56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_H@land_neg_alignedC13~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_commI47Corelib4Init5Logic2ex00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_subC13~~~C56Stdlib6ZArith6BinInt1Z3oppC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C56Stdlib6ZArith6BinInt1Z6shiftlC4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop03C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr5instr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmmap_entryC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~K46Stdlib9micromega7EnvRing5PExpr06C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_H;ram_b_storeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7set_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~K46Stdlib9micromega5Tauto8GFormula01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8agree_onC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B?rrw_cells_agreeC13~~~I35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge;Z_to_bv_eqmC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B@rmrep_ctx_frameWC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate02C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8brk_wordC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_H<ram_brk_deadC13~~~C46Stdlib4Bool4Bool=negb_true_iffC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsigned".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e87c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in C6.

  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x9e8a0) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e87c) fc None m (seg_rom rsegs)).
Proof.
  intros until off. intros MR CNT BRK C0 C1b.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in C6.

  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma ram_brk0_node :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x9e8bc) fc None m (seg_rom rsegs) /\ 0 <= r < 2^64))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x9e8b8) fc None m (seg_rom rsegs)).
Proof.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x9e8b8 + 4)%Z with 0x9e8bc%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x9e8a0 \/ pc = 0x9e8dc) -> forall cur req, req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom rsegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e8dc) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8bc) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC. change (963664 + 920) with 964584 in MU. change (963664 + 928) with 964592 in MU.

  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.

  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9e900) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8e0) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.

  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e98c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e900) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.
  change (963664 + 40) with 963704 in MU. change (963664 + 48) with 963712 in MU. change (963664 + 920) with 964584 in MU. change (963664 + 928) with 964592 in MU.

  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

(* [comment removed for export] *)
Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e98c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.

  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e914) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells rsegs m RCTX cs)
      by (eapply RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.
  change (963664 + 920) with 964584 in MU, MU0. change (963664 + 928) with 964592 in MU, MU0.

  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (963664 + 912) with 964576.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells rsegs ?mX 964576 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until old. intros MR CNT O0 O1 MI.
  pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.

  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.

(* [comment removed for export] *)
Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8e0) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.

  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.
End CEIL_WRAP_1.

