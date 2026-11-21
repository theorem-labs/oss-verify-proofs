(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the vDSO; the model's fetch-failure and unmodeled answers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec ShapeAlg SpinAlg DivergeSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import MState Frame.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_BrRegs () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getK47Corelib4Init5Logic2eq01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8regs_eqvC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState@reg_get_set_sameC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateAreg_get_set_otherC13~~~K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs;reg_get_setC13~~~C45stdpp9bitvector;definitions;bv_unsignedK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv3Sem6c_resvK47Corelib4Init5Logic3and01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8core_eqvC13~~~C4ELinuxProcessSemantics5Riscv3Sem4rgetI4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics5Riscv3Sem4fgetC4ELinuxProcessSemantics5Riscv3Sem7unbox_sc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8fget_eqvC13~~~C4ELinuxProcessSemantics5Riscv3Sem5freadI4ELinuxProcessSemantics5Riscv5Instr4ffmt00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv3Sem4rsetc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs<regs_eqv_setC13~~~C4ELinuxProcessSemantics5Riscv3Sem4fsetC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem9with_fcsrC4ELinuxProcessSemantics5Riscv3Sem9with_resvC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions7Z_to_bvI4ELinuxProcessSemantics5Riscv3Fpu6fflags00C4ELinuxProcessSemantics5Riscv3Sem6fwriteC4ELinuxProcessSemantics5Riscv3Sem7nan_boxc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs=core_eqv_fsetC13~~~C4ELinuxProcessSemantics5Riscv3Sem:inval_resvK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs;core_eqv_mkC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8rget_eqvC13~~~C45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs=core_eqv_rsetC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs9rget_eqvRC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv3Sem3eff07i99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv00C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv07C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics5Riscv3Sem5low32c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsCcore_eqv_inval_resvC13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv01C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv08C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv04C13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv05C13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv3Sem3eff06k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv06C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsBcore_eqv_with_resvC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics5Riscv3Sem7amo_valK4ELinuxProcessSemantics5Riscv5Instr5instr0FC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv3Sem9csr_sliceC4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions5bv_orC4ELinuxProcessSemantics5Riscv3Sem9slice_setK4ELinuxProcessSemantics5Riscv3Sem3eff02k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv03C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsBcore_eqv_with_fcsrC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs;core_eqv_ifC13~~~k99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7eff_eqv02C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldC4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmac99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs?core_eqv_fwriteC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Fpu7fp_sqrtK4ELinuxProcessSemantics5Riscv5Instr5instr0MC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Fpu9fp_minmaxK4ELinuxProcessSemantics5Riscv5Instr5instr0OC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leK4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC4ELinuxProcessSemantics5Riscv3Fpu8int_wrapC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv3Fpu<round_scaledC4ELinuxProcessSemantics5Riscv3Fpu9fp_encodeC47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RC4ELinuxProcessSemantics5Riscv3Fpu8fp_classK4ELinuxProcessSemantics5Riscv5Instr5instr0SC4ELinuxProcessSemantics5Riscv3Sem4execC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv3Sem3eff00I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I47Corelib6Floats9SpecFloat:spec_float00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs=exec_eqv_coreC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs6ms_eqvC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs<regs_eqv_symC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs>regs_eqv_transC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs;eff_eqv_indC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs<ms_reg17_eqvC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8ares_eqvC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsGinterp_eff_accesses_eqvC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsHdecode_exec_accesses_eqvC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegsAstep_accesses_eqvC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7res_eqvC13~~~C47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8res2_eqvC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem3Run<syscall_argsC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs@syscall_args_eqvC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteK4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput01I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs;ms_eqv_reflC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs7cfg_eqvC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs:ms_eqv_symC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs<ms_eqv_transC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps01C13~~~K47Corelib4Init5Logic2ex01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs8step_eqvC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps02C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim:msteps_indC13~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs:reg_of_natC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs:canon_regsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith4Znat5Nat2Z8inj_succc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ6Bridge6BrRegs<is_x0_bv_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop :=
  forall r : reg, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r Hr. symmetry. apply H, Hr. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1|apply H2]; exact Hr. Qed.

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H, Hr]. Qed.

Lemma is_x0_bv_eqb : forall r : reg, is_x0 r = bv_eqb r 0.
Proof. intros r. unfold is_x0, bv_eqb. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ c_fregs c = c_fregs c' /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F pc fc rv, regs_eqv R R' ->
  core_eqv (Core R F pc fc rv) (Core R' F pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Lemma rget_eqv : forall c c' r, core_eqv c c' -> rget c r = rget c' r.
Proof.
  intros c c' r (HR & _). unfold rget. destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR, E.
Qed.
Lemma fget_eqv : forall c c' r, core_eqv c c' -> fget c r = fget c' r.
Proof. intros c c' r (_ & HF & _). unfold fget. rewrite HF. reflexivity. Qed.
Lemma fread_eqv : forall c c' fmt r, core_eqv c c' -> fread c fmt r = fread c' fmt r.
Proof. intros c c' fmt r H. unfold fread. rewrite (fget_eqv c c' r H). reflexivity. Qed.
Lemma c_pc_eqv : forall c c', core_eqv c c' -> c_pc c = c_pc c'.
Proof. intros c c' (_ & _ & H & _). exact H. Qed.
Lemma c_fcsr_eqv : forall c c', core_eqv c c' -> c_fcsr c = c_fcsr c'.
Proof. intros c c' (_ & _ & _ & H & _). exact H. Qed.
Lemma c_resv_eqv : forall c c', core_eqv c c' -> c_resv c = c_resv c'.
Proof. intros c c' (_ & _ & _ & _ & H). exact H. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  repeat split; auto.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
  core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

(* [comment removed for export] *)
Local Ltac solve_core HR :=
  repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
               | apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
               | apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
               | match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
  first [ apply (core_eqv_mk _ _ _ _ _ _ HR) | assumption ].

Local Ltac eqv_struct HR :=
  repeat first
    [ apply EqvDone; solve_core HR
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma rget_eqvR : forall R R', regs_eqv R R' -> forall F pc fc rv r,
  rget (Core R F pc fc rv) r = rget (Core R' F pc fc rv) r.
Proof. intros R R' HR F pc fc rv r. apply rget_eqv. apply core_eqv_mk. exact HR. Qed.

Lemma exec_eqv_core : forall R R' F pc fc rv sz i,
  regs_eqv R R' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F pc fc rv)).
Proof.
  intros R R' F pc fc rv sz i HR.
  destruct i; unfold_exec; rewrite ?(rget_eqvR R R' HR); eqv_struct HR.
Qed.

Lemma exec_eqv : forall sz i c c', core_eqv c c' -> eff_eqv (exec sz i c) (exec sz i c').
Proof.
  intros sz i [R F p f s] [R' F' p' f' s'] (HR & HF & Hp & Hf & Hs); simpl in *; subst.
  apply exec_eqv_core; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_eqv (ms ms' : machine_state) : Prop :=
  regs_eqv (ms_regs ms) (ms_regs ms') /\ ms_fregs ms = ms_fregs ms' /\
  ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
  ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
  ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. repeat split; apply regs_eqv_refl. Qed.
Lemma ms_eqv_sym : forall ms ms', ms_eqv ms ms' -> ms_eqv ms' ms.
Proof.
  intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  repeat split; auto using regs_eqv_sym; congruence.
Qed.
Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; eauto using regs_eqv_trans; congruence.
Qed.

Definition res_eqv (r r' : machine_result machine_state) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv a b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b => core_eqv (fst (@access_value _ a)) (fst (@access_value _ b))
                                /\ snd (@access_value _ a) = snd (@access_value _ b)
                                /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] acc1]| |];
    destruct (interp_eff_accesses segs (k' _) m) as [[[c2 m2] acc2]| |]; cbn in *; try exact H0; try contradiction.
    destruct H0 as (A & B & C). subst. split; [exact A|]. split; reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [| exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [[[c1 m1] acc1]| |];
    destruct (interp_eff_accesses segs k' _) as [[[c2 m2] acc2]| |]; cbn in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (A & B & C). subst. split; [exact A|]. split; reflexivity.
Qed.

Lemma ms_reg17_eqv : forall ms ms', ms_eqv ms ms' -> ms_reg ms 17 = ms_reg ms' 17.
Proof. intros ms ms' (HR & _). unfold ms_reg. cbn. apply HR. reflexivity. Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg17_eqv ms ms' Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold RiscvSemantics.decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F' pc' fc' rv' (Z_to_bv 64 isz) i HR) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F' pc' fc' rv')) m') as [[[c m1] acc1]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc2]| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
Qed.

Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
  intros ms ms' Heqv. unfold RiscvSemantics.step, RiscvSemantics.drop_access_report.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
    cbn in *; try exact K; try contradiction. exact (proj1 K).
Qed.

(* [comment removed for export] *)
Definition res2_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
  match r, r' with
  | MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  res2_eqv (mi_account_step segs ms mo) (mi_account_step segs ms' mo).
Proof.
  intros ms ms' mo Heqv. unfold mi_account_step.
  pose proof (step_accesses_eqv ms ms' Heqv) as K.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
    cbn in *; try exact K; try contradiction.
  destruct K as [K1 <-]. destruct (materialize_model_accesses mo (accessed_ranges machine_state a)); [|exact I].
  split; [exact K1|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR by reflexivity. reflexivity. Qed.

Lemma sys_input_eqv : forall ms ms' x8, ms_eqv ms ms' -> sys_input segs ms x8 = sys_input segs ms' x8.
Proof.
  intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold sys_input. rewrite Ha. reflexivity.
Qed.

Lemma apply_effect_eqv : forall ms ms' eff, ms_eqv ms ms' ->
  ms_eqv (apply_effect ms eff) (apply_effect ms' eff).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv_set.
Qed.

Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Definition cfg_eqv (c c' : config) : Prop :=
  ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros c. split; [apply ms_eqv_refl| reflexivity]. Qed.
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.
Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof. intros a b c [H1 H2] [G1 G2]. split; [eapply ms_eqv_trans; eassumption| congruence]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msteps_eqv : forall ms ms1, CatSim.msteps segs ms ms1 ->
  forall ms', ms_eqv ms ms' -> exists ms1', CatSim.msteps segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof.
  intros ms ms1 H. induction H as [ms | ms msa msb Hsvc Hstep Hms IH]; intros ms' Heqv.
  - exists ms'. split; [apply CatSim.mst_refl| exact Heqv].
  - pose proof (step_eqv ms ms' Heqv) as K. rewrite Hstep in K.
    destruct (RiscvSemantics.step segs ms') as [msa'| |] eqn:E; simpl in K; try contradiction.
    destruct (IH msa' K) as (msb' & Hms' & Hb).
    exists msb'. split; [|exact Hb].
    eapply CatSim.mst_step; [| exact E | exact Hms'].
    destruct Heqv as (_ & _ & _ & Hs & _). congruence.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition canon_regs (R : bvmap 5 word) : bvmap 5 word :=
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
      (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
      (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).

Lemma canon_regs_eqv : forall R, regs_eqv R (canon_regs R).
Proof.
  intros R r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | (unfold canon_regs, getr; cbn; reflexivity)] |]). lia.
Qed.

(* [comment removed for export] *)
Lemma getr_eqv : forall R R' r, regs_eqv R R' -> getr R r = getr R' r.
Proof.
  intros R R' r H. unfold getr. rewrite <- is_x0_bv_eqb. destruct (is_x0 r) eqn:E; [reflexivity|]. apply H, E.
Qed.

