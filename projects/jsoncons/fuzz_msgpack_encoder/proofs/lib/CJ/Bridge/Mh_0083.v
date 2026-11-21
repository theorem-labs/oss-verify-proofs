(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed advance_past_svc_eqv, apply_effect_eqv, at_node_eqv and 29 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Bridge/BrRegs.v, 82 lines within its lines 33-370. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From Stdlib Require IndefiniteDescription. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BrRegs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Frame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.
Ltac2 kr_t_BrRegs () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getK47Corelib4Init5Logic2eq01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8regs_eqvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState@reg_get_set_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC79OSSVerify5KrLib2CJ3Lib7Mh_00396MStateAreg_get_set_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs;reg_get_setC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv3Sem6c_resvK47Corelib4Init5Logic3and01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8core_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rgetI4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics5Riscv3Sem4fgetC4ELinuxProcessSemantics5Riscv3Sem7unbox_sc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8fget_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5freadI4ELinuxProcessSemantics5Riscv5Instr4ffmt00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv3Sem4rsetc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<regs_eqv_setC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4fsetC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem9with_fcsrC4ELinuxProcessSemantics5Riscv3Sem9with_resvC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions7Z_to_bvI4ELinuxProcessSemantics5Riscv3Fpu6fflags00C4ELinuxProcessSemantics5Riscv3Sem6fwriteC4ELinuxProcessSemantics5Riscv3Sem7nan_boxc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs=core_eqv_fsetC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem:inval_resvK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs;core_eqv_mkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8rget_eqvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs=core_eqv_rsetC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs9rget_eqvRC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv3Sem3eff07i79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv00C1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics5Riscv3Sem5low32c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsCcore_eqv_inval_resvC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv01C1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv08C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv04C1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv3Sem3eff06k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv06C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsBcore_eqv_with_resvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics5Riscv3Sem7amo_valK4ELinuxProcessSemantics5Riscv5Instr5instr0FC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv3Sem9csr_sliceC4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions5bv_orC4ELinuxProcessSemantics5Riscv3Sem9slice_setK4ELinuxProcessSemantics5Riscv3Sem3eff02k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv03C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsBcore_eqv_with_fcsrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs;core_eqv_ifC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7eff_eqv02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldC4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmac79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs?core_eqv_fwriteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Fpu7fp_sqrtK4ELinuxProcessSemantics5Riscv5Instr5instr0MC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Fpu9fp_minmaxK4ELinuxProcessSemantics5Riscv5Instr5instr0OC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leK4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC4ELinuxProcessSemantics5Riscv3Fpu8int_wrapC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv3Fpu<round_scaledC4ELinuxProcessSemantics5Riscv3Fpu9fp_encodeC47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RC4ELinuxProcessSemantics5Riscv3Fpu8fp_classK4ELinuxProcessSemantics5Riscv5Instr5instr0SC4ELinuxProcessSemantics5Riscv3Sem4execC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv3Sem3eff00I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I47Corelib6Floats9SpecFloat:spec_float00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs=exec_eqv_coreC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs6ms_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<regs_eqv_symC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs>regs_eqv_transC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs;eff_eqv_indC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<ms_reg17_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8ares_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsGinterp_eff_accesses_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsHdecode_exec_accesses_eqvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsAstep_accesses_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7res_eqvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8res2_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem3Run<syscall_argsC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs@syscall_args_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteK4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput01I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs;ms_eqv_reflC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs7cfg_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs:ms_eqv_symC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<ms_eqv_transC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8step_eqvC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs:reg_of_natC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs:canon_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Frame3mkRC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith4Znat5Nat2Z8inj_succc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<is_x0_bv_eqbC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop :=
  forall r : reg, is_x0 r = false -> reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01Rh12_Hh21rp;1p;2p;3g0000R0p4p7210R1g000\R2p4p710p8P1p10016p4p710p8P1p1001Rp4p710p8P1p10020p4p710p8P1p1002Np4p710p8g002kj10Tg003Pj19Tg0045j12Tg004Sj11TP0j28Tg0056j17TP2j34Tg005^j23Tg006Hj25Tg006bj26Tg007h#0R2#9#2R0%02#0#0#0#0#2#1R2'8%10g008Mf0R0#7g008m34f2f1'3,52W1W21600eW0o"). Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01Hh12Hrh21Rh32R'h41rp;1p;2p;3p;4g0000R0p4p7210R1g000\R2p4p710p8P1p10016p4p710p8P1p1001Rp4p710p8P1p10020p4p710p8P1p1002Np4p710p8g002kj10Tg003Pj19Tg0045j13Tg004Sj11TP0j28Tg006bj24Tg0056j17TP2j35Tg005^j22Tg009Mj46Tg007h#0R2#9#3R0%02#0#0#0#0#3#1R2'8R1f1R3f0R4'4%10g008M%74g008m35P2f4/23f3/23f2R2P3P4O2C6W1W41432eW0X31W2o"). Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h02H1h12H2h22Hrh32R1h42R2h52R3h61rp;1p;2p;3p;6g0000R0p4p7210R1g000\R2p4p710p8P1p10016p4p710p8P1g001RR3p4p710p8P1p10020p4p710p8P1p1002Np4p710p8g002kj10Tg003Pj19Tg0045j13Tg004Sj12TP0j28Tg006bj24Tg0056j17TP2j35Tg005^j21TP3j66Tg007h#0R3#9#3R2%03#0#0#0#0#3#2R3'8R0f2R1f1R4'4R5%22g008Mf0R2#7g008m35P3f6/14f5/14f4R3/14f3P4P2O2P1P4P2O2E6W2W61431eX15W0X50X40W3o"). Qed.

Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01bi001bh11Hh22Hrh31Rh42R'h51kh61rh71vp;1p;2p;3p;5p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj11Tg003Pj1=Tg0045j15Tg004Sj14TP3j2<Tg006bj27Tg0056j1;TP1j33Tg00=Dj36Tg005^j20Tg00>1j52Tg006Hj2:Tg00Enj48TP5j69Tg007h#1R5#=#5R1%15#1#1#1#1#5#4R5'<R3%41R0f3R4f2R2'7g008MR6f0R7#;g008m33P5P6P5f4R8f1R9561R:P4f6R;/09n0100000020000P1P5f5R<P8P;D2/029357X05P5P6P5P:P410<9n0100000020000P6P5A61<2P8f7R=/02n0100000020000=357X05P:P6P6P6P5P7P<f8/04n0100000020000P6P5P7P<10=4n0100000020000535P71:58P4P2P9O2n0110000020000b0P1P5P8P4P<D2/09P<P8P9P4C8E9P1P5P8P4P;D2/09P;P8P9P4C8E9W2X60P1P5P2P9P8D2P1P5P2P9P4D2'7eW1X75W5X43W3o"). Qed.

Lemma is_x0_bv_eqb : forall r : reg, is_x0 r = bv_eqb r 0.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01rp;1p;2p;3p1009ip4p70R0g006HR1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8p10000p4p7210R3P2p8P3p10016p4p710p8P3P0p8P3p10020p4p710p8P3p1002Np4p710p8P3p100;Gp4p710p8p100<Np4p70R3P2p8P3P0p8g002kj1:Tg003Pj19Tg0045j12Tg004Sj11Tg00G7j20Tg00Gaj38Tg00HDj23TP1j24Tg0056j15Tg00=Dj36Tg000\j37Tg007h#:#9#2R1#1g008MR0f0R3,01g00Hag00ER581R2,01'3'4%53A6132570eW0o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01Fh11Rh22R'h32fch42pch52rvp;1p;2p;5p;3p;4p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj10Tg003Pj1@Tg0045j14Tg004Sj16TP3j2?Tg00I?j1>Tg006bj2<Tg00Iaj5;Tg00JJj1:Tg00K3j17TP1j31Tg00K]j18Tg00LDj19Tg00Lmj1=Tg00D>j25Tg006Hj22Tg00MVj43Tg007h#0R1#@#4%01#0#0#0R1#0#4#6R3'?R0%41#6R1%>3R4f5R2f4R5'<f6P5f3R6f2R7f1R8D;R9#:P2P5P6P7P8D;R8#:'<%79%78R7510R6%89%88R5513R2%99%98R:511R;%=9%=8R8514R9'5R<'5R='5f0P6P=1207P2P<1235P;P9121:1248C3C3C3C3UW5W3X43X00X20W1o"). Qed.

Lemma rget_eqv : forall c c' r, core_eqv c c' -> rget c r = rget c' r.
Proof.
  intros c c' r (HR & _). unfold rget. destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR, E.
Qed.
Lemma fget_eqv : forall c c' r, core_eqv c c' -> fget c r = fget c' r.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01Hh12HFh22_Hh33_H0h41bh51ch62c'h71rp;1p;2p;3p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj17Tg003Pj1CTg0045j1:Tg004Sj19Tg00N1j2BTg00JJj18Tg006bj2<TP3j2>Tg00K3j12Tg00K]j15Tg00LDj13Tg00I?j1=Tg00Lmj14TP1j30Tg00Plj26Tg005^j2;Tg006Hj2ATP5j6@Tg00D>R5j2?Tf3R1f2R3f1R030f0R4'?p=1g00O^R2g007h#7R6#C#:R7#91B30P5%81%83'<%76#7#7#7R6#7#:#9R8,>7R7%21%23P8%51%53%:6#9R6%31%33%=8R9%41%4330C1C1C1f4R:/631613508P4f5R3#8%8:'<P7f6R:#2R1%23P8%5:R;%53P6%3:R<%33%4:R=%43509C1C1C1P5f7R5#2=071P8%55P;P6%35P<%45=09=C1C1f8R=/6:165:508P4f9R5#2%2=507P8f:R=#5%55P6%3=%35%4=%45509C1C1P7%2=R91;4=f;R6#2R:/;=508X471;95,A8P:P0E@166516=5508eW3W1P0P4O2n2001000000120000000W0W2P0P4O2n2001000000121000000W0W7X62W5o"). Qed.
Lemma fread_eqv : forall c c' fmt r, core_eqv c c' -> fread c fmt r = fread c' fmt r.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11bh21ch32c'h43fmti003fmth51rp;1p;2p;3p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8p10000p4p7210R3P2p8P3p10016p4p710p8P3P0p8P3g0020R4p4p710p8P3p1002Np4p710p8P3p100;Gp4p710p8p100<Np4p70R3P2p8P3P0p8g002kj11Tg003Pj1<Tg0045j12Tg004Sj16Tg00N1j2;Tg00Plj24Tg00QSj13Tg00G7j20TP1j35Tg006Hj2:Tg00R=j48TP4j69Tg00SCj37Tg00O^R4g00SkR1g007h#1R0#<#2#6f3R3f2R2';%10#1#1#1R0#1#2R5#6R6f1R7,43R8g00TVR9P1P9P3%20R0f0R:#3'0105:n0110000020000P1P9P3f4R;/42R<#3,00105<n011000002000035X16P1P9P2%38,001058n0110000020000,:914;7P;P3P7P:C8E9A7;27A7327559eW0W5W4X34W2o"). Qed.
Lemma c_pc_eqv : forall c c', core_eqv c c' -> c_pc c = c_pc c'.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h02H0h11Hh22_Hh33_H0h43_H1h51ch62c'p;2p;1p;3p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g00N1j2?Tg00JJj17Tg006bj29Tg002kj16Tg003Pj1>Tg0045j18Tg004Sj1:TP3j2<Tg00K3j15Tg00K]j12Tg00LDj13Tg00I?j1;Tg00Lmj14TP1j30Tg00D>R1j2=Tf3R3f2R0f1R430f0R2'=p=1g00O^R51?42P1%70%74'9g007h#6R6#>#8%66#6#6#6R6#6#8#:R7'<R8%50%54P7%20R9%24%86#:R6%30%34%;7R:%40%4430C1C1C1%23=079P2f4R9#7%73'9P8f5R3#5R0%59P7%23R;%29P6%33R<%39%43R3%4950:C1C1C1P1f6R9#5=080P7%29R0P;P6%39P<%49=0:3C1C1f7R3#2=070P2f8R0#5%53508P7f9R8#2R3%20P6%38R9%30%48R8%4050:C1C1P1f:R1#2R0=073P6%31P9%41=0:8C1f;#2R8=070P2f<R0#2=078P6f=R6#3%30%46%4050:C1P4W4W1P4P2O2n2001000000120000000W0W3P4P2O2n2001000000121000000W0W2P4P2O2n2001000000121000000W0X65W5o"). Qed.
Lemma c_fcsr_eqv : forall c c', core_eqv c c' -> c_fcsr c = c_fcsr c'.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h02H0h11Hh22_Hh33_H0h43_H1h53_H2h61ch72c'p;2p;1p;3p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g00N1j2?Tg00JJj17Tg006bj29Tg002kj16Tg003Pj1>Tg0045j18Tg004Sj1:TP3j2<Tg00K3j15Tg00K]j14Tg00LDj11Tg00I?j1;Tg00Lmj12TP1j30Tg00D>R1j2=Tf3R3f2R0f1R430f0R2'=p=3g00O^R51?42P1%70%74'9g007h#6R6#>#8%66#6#6#6R6#6#8#:R7'<R8%50%54P7%40%44%86#:R6%10R9%14%;7R:%20%2430C3C3C3%13=069P2f4R9#7%73'9P8f5R3#5R0%59P7%43R;%49P6%13R<%19%23R3%2950:C3C3C3P1f6R9#5=080P7%49P;P6%19R;P<%29=0:3C3C3f7R3#1=06;P2f8R;#5%53508P7f9R8#4R3%4;P6%18R9%1;%28R8%2;50:C3C3P1f:R;#4=073P6%1;R3P9%2;=0:8C3f;R8#1=063P2f<R3#4%48507P6f=R7#1R8%13%27R7%2350:C3P1f>R1#1R3=068%21=0:7f?#1R7=063P2f@R3#1=067fA#2%2350:P4W5W1P4P2O2n2001000000120000000W0W4P4P2O2n2001000000120000000W0W3P4P2O2n2001000000121000000W0W2P4P2O2n2001000000121000000W0X75W6o"). Qed.
Lemma c_resv_eqv : forall c c', core_eqv c c' -> c_resv c = c_resv c'.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h02H0h11Hh22_Hh33_H0h43_H1h53_H2h61ch72c'p;2p;1p;3p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g00N1j2?Tg00JJj17Tg006bj29Tg002kj16Tg003Pj1>Tg0045j18Tg004Sj1:TP3j2<Tg00K3j15Tg00K]j14Tg00LDj12Tg00I?j1;Tg00Lmj11TP1j30Tg00D>R1j2=Tf3R3f2R0f1R430f0R2'=p=3g00O^R51?42P1%70%74'9g007h#6R6#>#8%66#6#6#6R6#6#8#:R7'<R8%50%54P7%40%44%86#:R6%20%24%;7R9%10R0%1430C3C3C3%13=090P2f4R0#7%73'9P8f5R3#5R:%50P7%43R;%40P6%23R<%20%13R3%10509C3C3C3P1f6R0#5=08:P7%40P;P6%20P<%10R0=093C3C3f7R3#1=090P2f8R0#5%53508P7f9R8#4R3%40P6%28R<%20%18R8%10509C3C3P1f:R0#4=073P6%20P<%10R0=098C3f;R8#1=090P2f<R0#4%48507P6f=R7#2R8%20%17R7%10509C3P1f>R1#2=068%11R1=097f?R7#1=091P2f@R1#2%27506fA#1%11509P2W1W5P4P2O2n2001000000120000000W0W4P4P2O2n2001000000120000000W0W3P4P2O2n2001000000121000000W0W2P4P2O2n2001000000121000000W0X75W6o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11Fh22c'h31fh41sh52F'h62HRh71Rh82R'h91ci001ch:2f'h;1ph<2p'h=2s'h>1vi016c_fcsri027c_fregsi034c_pci046c_regsi056c_resvp;1p;2p;5p;3p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj17Tg0045j1ATg004Sj1BTg00N1j26Tg00WLj28Tg003Pj1GTP3j2FTg00I?j1ETg00Iaj54Tg006bj23TP1j30Tg00D>R1j21Tg006Hj2<Tg00MVj4>TP5j6@Tg00JJj1;Tg00K3j1=Tg00LDj1?Tg00Lmj1:Tg00K]j1CTf5R5f4R3f3R030f2R4f1R2f0R630'1p=9f6R7?053A0042/16'1p=2A0042/16,13p=51126,14p=Dg007h#7R8#7#7#7#7R9#7#A#BR:g00O^R;P;162618341832'6[^2;P6%G8#A/F:R8%A9#BR9%E:R<P;P7P5P3P0P4D4/66f>R=f7R>P7P5P3P0D4'818=2'6[P6f?R?P=f=R@f<RAf;RBD4P3P0P4P2P6D4'6P1f@RC/35P8P?P3P:P=P0P9P@P4P<PAP2E9F2fARD/37P8PCP5P:fHREPEP9P=P0A0<@4F2D5P6fBRF/3>P8PFP>P:PDP7P9PCP5P<P?P3E9F2P1fCRGf8RH508P:PFP>P9PDP7A0<C5F2fERIf:RJ'3P8fDRKf9RLP:fLRMPMP9PFP>A0<D7F2D5P6A08IJP8PBfFR7=0:BR>P9PIPJP<PKPLE9RN'1fIRO/3=RPP8P2P@P:fPRQPQP9P7PBA0<IJF2RBD5[X18P:PIPJP9PKPLA0<GHF2P1P>PNPPP8P@P@PBD5P6A0:E@P9PEP@P<fGRBPAE9P1A09O=A0<E@fMRE/3FP8PDPDP:fTR1P1P9fJP?A0<O=F2D5P6fKRO=09CP9PDA0<MDfQ/37R1A08IIRPfXRN=0:NRNP9P2PGA0<EFD53D[X39A0<OCP<PDPNP9PGPGA0<6FD59D1PX4<13QIA08KKRQfWRI=0:IRPA09FFR1A0<DDRG'1RN'1RO'1P@PQPO1<8KPPPN1<:IP1PG1<9F1<<DC>C>C>C>PMP6E@W0PMP6E@W0P2P6O2n2001000000121000000W0W0P2P6O2n2001000000121000000W0P7P6E@W0P2P6O2n2001000000121000000W0W6P2P6O2n2001000000121000000PCP?P=P@PAD4RA#;%=APB%?A%:AD4R@#;P5P3P0P4P2D4R5#;%=5PB%?5%:5D4R=#;'3P8%=@%==P:%C@%C=P9%?@%?=%:@%:=50<F2D5e18BA18B5'6eW0X=<X:9X<:X58X88P3P0P4P2P6O5n01100000151104102103101105X2;W4W3X;:X18W7P3P0P4P2P6O5n01100000151104102103101105W9W>o"). Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11Fh22c'h31ph41sh52F'h62HRh71Rh82R'h91ci001ch:1fh;2f'h<2p'h=2s'h>1vi016c_fcsri027c_fregsi034c_pci046c_regsi056c_resvp;1p;2p;5p;3p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj17Tg0045j1ATg004Sj1BTg00N1j26Tg00X6j28Tg003Pj1GTP3j2FTg00I?j1ETg00Iaj54Tg006bj23TP1j30Tg00D>R1j21Tg006Hj2<Tg00MVj4>TP5j6@Tg00JJj1;Tg00K3j1=Tg00K]j1?Tg00Lmj1:Tg00LDj1CTf5R5f4R3f3R030f2R4f1R2f0R630'1p=9f6R7?053A0042/16'1p=21126,14p=5A0042/16p=Dg007h#7R8#7#7#7#7R9#A#BR:g00O^R;P;162618341832'6[^2;P6%G8#A%79#A#BR9'FR8%E9R<P;P7P5P3P0P4D4/66f>R=f7R>P7P5P3P0D4'818=2'6[P6f?R?P=f=R@f<RAf;RBD4P3P0P4P2P6D4'6P1f@RC/35P8P?P3P9P=P0P:P@P4P<PAP2E9F2fARD/37A08C5P9P?P3P:fHREPEA0<@4F235P6fBRF/3>P8PFP>P9PDP7P:PCP5P<P?P3E9F2P1fCRGf8RH508P9PFP>P:PDP7A0<C5F2fER>f:RI'3fDRJf9RK508P9PGPHP:fLRLPLA0<D7F235P6A08>IP8PBfFR7=09BRBP:P>PIP<PJPKE9RM'1fIRN/3=ROA082@P9fGRPPAP:fPRQPQA0<>IF2RR35[X18P9P>PIP:PJPKA0<GHF2P1PBPMA08@@=5ORP6A09E@P9P=A0:N=RRA0<E@RO'1fM/3FRMA08DDRBP9P2PCP:fTRHPHP<PNP=E9RHCD35[X39P:PEP@P<PPPAE9P1PRPOP9PCPCPHCD95MBP6fKRB=0:CA0<BCP<PDfQ/37A08>>P9PJPJP:fXRBPBA0<6FF235X4<13Q>A08JJRQA09GGR>fWRF=0:FRBA0<DDRM'1RH'1RO'1P@PQPO1<8JP>PH1<9GPBPM1<:F1<<DC>C>C>C>PLP6E@W0W0P2P6O2n2001000000121000000W0PNP6E@W0P2P6O2n2001000000121000000W0P7P6E@W0P2P6O2n2001000000121000000W0W6P2P6O2n2001000000121000000PCP?P=P@PAD4RA#;%=A%?APP%:AD4R@#;P5P3P0P4P2D4R5#;%=5%?5PP%:5D4R=#;'3%=@%==508P9%?@%?=P:%C@%C=%:@%:=50<F235e18PA18P5'6eW0X=<X;:X<9X58X88P3P0P4P2P6O5n01100000151104102103101105X2;W4X::X39X18W7P3P0P4P2P6O5n01100000151104102103101105W9W>o"). Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11Fh22c'h31fh41ph52F'h62HRh71Rh82R'h91ci001ch:2f'h;2p'h<1sh=2s'h>1vi016c_fcsri027c_fregsi034c_pci046c_regsi056c_resvp;1p;2p;5p;3p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g002kj18Tg0045j1@Tg004Sj1CTg00I?j1ETg00N1j27Tg00Xbj26Tg003Pj1GTP3j2FTg00Iaj54Tg006bj23TP1j30Tg00D>R1j21Tg006Hj2?Tg00MVj4=TP5j6ATg00JJj1;Tg00K3j1<Tg00K]j1>Tg00LDj1:Tg00Lmj1BTf5R5f4R3f3R030f2R4f1R2f0R630'1p=9f6R7?053A0042/16'1p=21126,14p=5A0042/16p=Dg007h#8R8#8#8#8#8R9#8#@#CR:#ER;g00O^R<P<172616341632'7[^2<P6%G8#@/F:R8%@9#CR9P<P7P5P3P0P4D4/76f>R=f7R>P7P5P3P0D4'616=2'7[P6f?R?P=f=R@f<RAf;RBD4P3P0P4P2P6D4'7P1f@RC/35P8P?P3P:P=P0P9P@P4P;PAP2E9F2fARD/37A08C5P:P?P3P9P=P0fHRE=0;EF235P6fBRF/3>P8PFP>P:PDP7P9PCP5P;P?P3E9F2P1fCRGf8RH508P:PFP>P9PDP7A0;C5F2fER7f:RI'3fDRJf9RK508P:PGPHP9PFP>fLR>=0;>F235P6A087IP8PBfFRL=0:BRMP9P7PIP;PJPKE9RN'1fIRO/3=RPA082@P:fGRQPAP9PLPBfPRB=0;BF2RR35[X18P:P7PIP9PJPKA0;GHF2P1PMPNA08@@=5PRP6A0:E@P:P=A09O=RRA0;E@RP'1fM/3FRNA08DDRMP:P2PCP9fJP?P;fTRHPHE9RHCD35[X4:P9PEP@P;PQPAE9P1PRPPP:PCPCPHCD95NMP6fKRM=09CP9PDA0;>DfQ/3LA0877P:PJPJP9P2PGfXRD=0;DF235[X39A0;MC13B7A08JJRBA0:GGR7A09FFRMfWRD=0;DRN'1RH'1RP'1P@PBPP1?8JP7PH1?:GPMPN1?9F1?;DC=C=C=C=W0P>P6EAW0P2P6O2n2001000000121000000W0POP6EAW0P2P6O2n2001000000121000000W0PLP6EAW0P2P6O2n2001000000121000000W0W6P2P6O2n2001000000121000000PCP?P=P@PAD4RA#;%<A%>A%:APQD4R@#;P5P3P0P4P2D4R5#;%<5%>5%:5PQD4R=#;'3%<@%<=508P:%>@%>=P9%:@%:=%B@%B=50;F235e16QA16Q5'7eW0X=;X:9X;:X58X88P3P0P4P2P6O5n01100000151104102103101105X2<X<;W3X4:X18W7P3P0P4P2P6O5n01100000151104102103101105W9W>o"). Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11Fh22c'h31fh41ph51sh62F'h72HRh81Rh92R'h:1ci001ch;2f'h<2flh=2p'h>2s'i016c_fcsri027c_fregsi034c_pci046c_regsi056c_resvp;2p;1p;5p;3p;4p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g00N1j2:Tg00YNj28Tg002kj17Tg003Pj1LTg0045j1@Tg004Sj1KTP3j2NTg00I?j1MTg00Iaj59Tg006bj24TP1j30Tg00Z7j16Tg00G7j2JTg00D>R1j23Tg006Hj2>Tg00MVj4<TP5j6=Tg00LDj1?Tg00X6j2ETg00JJj1CTg00K3j1GTg00K]j1HTg00Lmj1BTg00Zej2ATg00[Bj2DTf5R5f4R3f3R030f2R4f1R2f0R630'3p=;f6R7?053A0042/36'3p=51J42/A6,D0p=21326,34p=11A26,D4p=IA0042/36p=Fg00[hg00O^R8P81:2618341832':[^28P6g007h#7R9#L#@%79#7#7#7R9#7#@#KR:'NR;%@9R9#KR<%M:R=P8P7P5P3P0P4D9/:6f>R>f7R?P7P5P3P0D9'818>2':[P6f?R@P>f=RAf<RBf;RCD9P3P0P4P2P6D9':P1f@RD/45P;P@P3P:P>P0P<PAP4P=PBP2E;F5fARE/47A0;D5P:P@P3P<P9P9P>fHRF#6RGC2P9P9P0PGC2A0=A4F531P6fBRG/4?P;PGP?P:PEP7P<PDP5P=P@P3E;F5P1fCRHf8RI50;P:PGP?P<PEP7A0=D5F5fERJf:RK'4fDRLf9RM50;P:PHPIP<1J9GRNfLRO#6RP5I9P9P9P?PPC2A0=E7F531P6A0;JKP;PCfFR7=0:CRPP<PJPKP=PLPME;R?'3fIRQ/4>RRA0;2AP:fGRSPBP<P9P9P7fPRT#6RUC2P9P9PCPUC2A0=JKF5RU31[X1;P:PJPKP<PLPMA0=HIF5P1PPP?A0;AA=1RUP6A0:FAP:P>A0<Q>RUA0=FARR'3fMR?/4GRPA0;EERIP:P2PDP<P9P9fJfT#6RMC2P9P9P@PMC2P=PQP>E;RMCF31[X4:P<PFPAP=PSPBE;P1PUPRP:PDPDPMCF91PIP6fKRI=0<DP<PEA0=OEfQ/47RPA0;JJRMA0:LLRRP9P9P2fX#6RUC2P9P9PHPUC2RU50<A0=?G3131[X3<A0=IDP=PEA0<UUA0=6G51R91PMX5=14TJA0;LLRTA0:HHRJfW#69I9NRN=0<NRMA0=EERP'3RR'3RG'3PAPTPG1>;LPJPR1>:HPMPP1><N1>=EC<C<C<C<POP6E=W0POP6E=W0P2P6O2n2001000000121000000W0PQP6E=W0P2P6O2n2001000000121000000W0P7P6E=W0P2P6O2n2001000000121000000W0W7P2P6O2n2001000000121000000P9P9PDP@P>PAPBD9RB#?%6SRAC2/EBR>#CP9P9P5P3P0P4P2D9R5#?PAC2/E5RA#C'4%G>%GA50;P:%H>%HAP<%?>%?A%B>%BA50=F531e18SB18S5':eW0X>=X;<X=:X6;X9;P3P0P4P2P6O5n01100000151104102103101105X28W5W3X4:X1;W8P3P0P4P2P6O5n01100000151104102103101105W:W<o"). Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h01Hh11ch22c'h33fmth41rh51vi001fp;1p;2p;4p;5p1009ip4p70R0p1000\p4p710R1p8P0p1001Rp4p710R0p8p100:Yp4p70R2P1p8P2P0p8p10000p4p7210R2P1p8P2p10016p4p710p8P2P0p8P2p10020p4p710p8P2p1002Np4p710p8P2p100;Gp4p710p8p100<Np4p70R2P1p8P2P0p8g002kj10Tg003Pj18Tg0045j11Tg004Sj16Tg00N1j25Tg00\Sj44Tg00[Bj23Tg00]<j17Tg00]fj52Tg00SkR0g007h#0R2#8#1#6g00TVg00O^R1f1R3f0R4'5P0P4f5R0f4R5f3R6C4P4P0P5f2R7C4'5P0P5%02#0#0#0R2#1/36#7P7P3P4D2P5%02#1/36P7P3P4D2n0110000020000W0X21W1W5W4W3o"). Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
  destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
  core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "p'0h02c1h13c1'h22c2h33c2'h42H1h52H2h61bi001bp;2p1009ip4p70R0p1000\p4p710R1p8P0p1001Rp4p710R0p8p100:Yp4p70R2P1p8P2P0p8p10000p4p7210R2P1p8P2p10016p4p710p8P2P0p8P2p10020p4p710p8P2p1002Np4p710p8P2p100;Gp4p710p8p100<Np4p70R2P1p8P2P0p8g00N1j20Tg008MR0P0g00O^R2f3R1f2R3'0R4f1R5,03R6P0P2f6R7f5P1n0110000020000P0P2P7f4P3n0110000020000'0[[^32^22^12]0f0R3P5X56X44X32X22X12X02P3X56X44X32X22X12X02n0110000020000W6o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h01Fh12HRh21Rh32R'h42fch52pch61rh72rvp;1p;2p;5p;7p;4p1009ip4p70R0p1000\p4p710R1p8P0p1001Rp4p710R0p8p100:Yp4p70R2P1p8P2P0p8g0000R2p4p7210R3P1p8P3p10016p4p710p8P3P0p8P3p10020p4p710p8P3p1002Np4p710p8P3p100;Gp4p710p8p100<Np4p70R3P1p8P3P0p8g002kj10Tg003Pj19Tg0045j12Tg004Sj11TP2j28Tg006bj27Tg00I?j15Tg00Iaj53Tg00`bj74Tg00akj46Tg007h#0R2#9#2R0%02#0#0#0R2#0#2#1R3'8R1f1R4f0R5'7%22#1%53%10f7R0f4R2f3R6f2R7P4D3f6R8P2P6P7P4D3P5P0P8P2P6P7P4f5F4C6W6W7W4X53X01W1X31W2o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) [] "h02msh11rp;1p;2p;3p;4p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g02BCj18Tg006bj2DTg002kj13Tg003Pj1;Tg0045j16Tg004Sj15TP3j2>Tg02CBj1=TP1j31Tg02DBj1<Tg00I?j17Tg02ECj1:Tg02FIj19Tg02GHj1CTg02HGj1BTg02IEj1ATg00D>j24Tg0056j1@Tg005^j2?Tg006Hj20Tg00MVj42Tg02JCf0R1#8R3/D3g007h#3R3#;#6R0%33#3R3#3#3R4#3#6#5R2'>R5%=1R6;16R7%<1R8=128R9%72R:%:1R;;1;R<%91R==1:=R>%64#5R4%C1R?;1?R@%63#5#7\2R3%B1RA;1ARB%A1RC=13CRD'4RE'4RF'4RG'4RH'4RI'4%50g008M%@1g008m31f2#8f1'?,02UW1P7PI1056P9PH1028P<PG10:;P>PF10:=P@PE104?PBPD103A103CC2C2C2C2C2C2C2W0o"). Qed.
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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) ["WithSegs"] "h01Hh12HRh22_Hh32msh43ms'p;2p;1p;3p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g02KJj2ITg02BCj13Tg006bj2@Tg002kj11Tg003Pj1CTg0045j1:Tg004Sj1=TP3j2FTg02CBj17Tg02DBj15Tg00I?j1>Tg02ECj14Tg02FIj19Tg02GHj1<Tg02HGj16Tg02IEj18TP1j30Tg01TNj1HTg00Gaj3ATg02cej2;Tg006Hj2GTg00=Dj3ETg00[Bj2DTg005^j2BTg00D>R1j2?Tf6R3f5R0f4R430f3R2f2R5f1R630f0R7'?'?p=2g02JCR81I67P1%35%36'@g007h#1R1#C#:R9%11#1R1#1#1R:#1#:R;#=R<'FR=%75%76P<%55%56%><R>%45%46P>%95%96%::#=R:%<5%<6%:1#=#>\<R?%65%66%85%8650?F2F2F2%C1#Hg00ERR15A9R@,;21;5@50<P7%34%32'@P=%70%74P<%50%54P>%40%44P>%90%94P:%<0%<4P?%60%64%80%8450?F2F2F2P6P@g008MR?g008m'GO2P?P<g00HaR4=A919E9@R91D;4R4%33/B@n0100000020000P?P<P9P4%30/B@n010000002000050<e1;3@1;0@50<eW2W1P6P7O2n2001000000121000000W0X48W3o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) ["WithSegs"] "h01bh11Hh22HRh32_Hh42msh53ms'p;2p;1p;3p;6p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8g0000R3p4p7210R4P2p8P4p10016p4p710p8P4P0p8P4g0020R5p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P0p8g02KJj2OTg02BCj15Tg006bj2ITg002kj14Tg003Pj1NTg0045j1ATg004Sj1ETP3j2KTg02CBj1>Tg02DBj1@Tg00I?j1GTg02ECj1=Tg02FIj1<Tg02GHj1DTg02HGj1CTg02IEj1BTP1j32Tg02Q3j1MTg03>ij1?Tg01TNj1LTg03?bj1:Tg03@Bj27Tg00[Bj26Tg005^j20Tg03@_j1;Tg02RZj1JTg02\1j33Tg006Hj2HTP5j69Tg00D>R5j2FTf6R1f5R3f4R032f3R4f2R2f1R632f0R7'F'Fp=8A32679304p=1g02JCR81O67P5%52%56'Ig007h#4R5#NR9#AR:%45#4R5#4#4R;#4#A#ER<'KR=%>2%>6P<%@2%@6%G<R>%=2%=6P>%<2%<6%A;#ER;%D2%D6%A5#E#G\<R5%C2%C6%B2%B6525F8F8F8%M<R?%?4%?232P7%50%54'IP=%>3%>0P<%@3%@0P>%=3%=0P>%<3%<0P;%D3%D0P5%C3%C0%B3%B0525F8F8F8P<%53R5%49#LR9g03A>R0#:'7,6:R;'0R>P<P7P<f7#5R=%;0R0#:,79,6:R4'0%;0R0#:,79,6:R2,0=%;0R0#:,79,6:R@,0=%;0R0#:,79,6:RA,0=%;0#:,79,6:R:,0=%J<R=53<R953<R053<RB53<RCD1P<%51RD/0;REP<10D4RFP<10D2RGP<10D@RHP<10DARIP<10D:RDP=D1D1D1RJ52?X0<P<1054RKP<PEP<P7PCD1=2?JX0<P<1052RCP<PEP<PFA3<7BD1=2?JX0<P<105@RBP<PEP<PFP<PGP<P7P0D1D1=2?JX0<P<105AR0P<PEP<PFP<PGP<PHA3<79D1D1=2?JX0<P<105:R5P<PEP<PFP<PGP<PHP<PIP<P7P=D1D1D1=2?JX0<P<P>P<PKP<PCP<PBP<P0P<P5P=D1D1D1,H?PDP6P:g008Mg008m'HR:O2E9PIP6PAP:O2E9PHP6P@P:O2E9PGP6P2P:O2E9PFP6P4P:O2E9PEP6P;P:O2E9%?1%?352?eW3W2P6P7O2n2001000000121000000W1X58W4o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) ["WithSegs"] "h01cp;1p;2p;3p;4p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8p10000p4p7210R3P2p8P3p10016p4p710p8P3P0p8P3p10020p4p710p8P3p1002Np4p710p8P3p100;Gp4p710p8p100<Np4p70R3P2p8P3P0p8g03RWj16Tg02KJj25Tg03SJj10TP1j31Tg03T@j14Tg006Hj22Tg00MVj43Tg03UIf0R1#6R0/50g03>3R3%01R1;11%401231C3W0o"). Qed.
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) ["WithSegs"] "h01Hh12H1h22H2h31ch42c'p;2p;1p;3p;4p1009ip4p70R0g000\R1p4p710R2p8P0p1001Rp4p710R0p8p100:Yp4p70R3P2p8P3P0p8p10000p4p7210R3P2p8P3p10016p4p710p8P3P0p8P3p10020p4p710p8P3p1002Np4p710p8P3p100;Gp4p710p8p100<Np4p70R3P2p8P3P0p8g03V>j24Tg03RWj10Tg02KJj22Tg03SJj11TP1j33Tg03WCj37Tg009Mj46Tg00MVj45Tg03UIR1f1R0f0R3'4g00D>f2R2#0%00'2g03>3R4%12%1033f3R5,42P3f4R2#0%05'2f5R5#1R6%12534%05R5f6R2#0R7'2%12R29346A7750P4P2P6P3C6C5W2W1P0P3O2n2001000000120000000W0X41W3o"). Qed.
Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
ltac2:(KReplay.run1 (kr_t_BrRegs ()) ["WithSegs"] "h01Hh12G1h22G2h32H1h42H2h51ah61bh71cp;2p;1p;3p;5p;6p;4p1009ip4p70R0g000\R1p4p710R2p8P0g001RR0p4p710R3p8p100:Yp4p70R4P2p8P4P3p8p10000p4p7210R4P2p8P4p10016p4p710p8P4P3p8P4p10020p4p710p8P4p1002Np4p710p8P4p100;Gp4p710p8p100<Np4p70R4P2p8P4P3p8g03V>j22Tg03RWj10Tg02KJj23Tg03SJj11TP1j34Tg03XKj57TP0j66Tg00MVj45Tg03UIR0f2R1f1R3'2g00D>R4f3R2#0%01'3g03>3R5%12%11341221f5R1/22[f0R2%01f4#0'3f6R6#1R7%115451261P4f7R4#0%06'3%14=457f9R7/24P2%07f8#0'3f:R4#1R8%17545f<R7#0R9%04R4'3%17R7=458P9f;R9#0P4P6P3D7P5P7%19P8P1P2E6C5W2W1P3P2O2n2001000000120000000W0W4W3P3P2O2n2001000000120000000W0X70X60W5o"). Qed.

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
End BrRegs.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes.
Module BrBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Exec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083.BrRegs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BrBase () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec6msteps00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec5mstepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2CJ3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4implC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_doneC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4nretC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec8evt_monoC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4respC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase=impl_bind_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_ebind_invC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase<impl_vis_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_enode_invC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs6ms_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8regs_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics5Riscv3Sem5is_x0C69OSSVerify5KrLib2CJ3Lib5Nodes4aregC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4list00K69OSSVerify5KrLib2CJ3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase8areg_eqvC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List6concatI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ3Lib5Nodes;iovec_bytesC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List7Forall200I47Corelib4Init5Logic2ex00K69OSSVerify5KrLib2CJ3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z5ldiffC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appK69OSSVerify5KrLib2CJ3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes3nat02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9O_CLOEXECC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;O_LARGEFILEK69OSSVerify5KrLib2CJ3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectc79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs@apply_effect_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegsDadvance_past_svc_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase=cj_msteps_catC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs:msteps_eqvC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01".
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_msteps_cat : forall a b, Exec.msteps segs a b -> CatSim.msteps segs a b.
Proof.
  intros a b H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
  impl segs (at_node segs) (ITree.bind _ t f) Q ms ->
  impl segs (at_node segs) t (fun r ms' => impl segs (at_node segs) (f r) Q ms') ms.
Proof.
  intros A B t. induction t as [r | n k IH]; intros f Q ms H; cbn in *.
  - apply evt_done. exact H.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. apply IH. apply Hk.
Qed.

Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
  impl segs (at_node segs) (ebind t f) (epost Q) ms ->
  impl segs (at_node segs) t
       (fun r ms' => match r with Ok a => impl segs (at_node segs) (f a) (epost Q) ms' | Unr => True end) ms.
Proof.
  intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
  eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

(* [comment removed for export] *)
Lemma impl_vis_inv : forall {A} n (k : resp -> itree node A) Q ms,
  impl segs (at_node segs) (Vis n k) Q ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BrBase ()) ["WithSegs"] "h01Ah11Hh21Qh31kh42msh51np;2p;1p;4p;7p10000p4p70R0p1000`p4p710R1p8P0p1001:p4p710R0p8p1001Xp4p70R2P1p8P2P0p8p1002Fp4p7210R2P1p8P2p10032p4p710p8P2P0p8P2p1003Np4p710p8P2p1003lp4p710p8P2p1004Ip4p710p8p100PKR2p60721002R3p100E?p4p7210p8P3p100F:R4p4p7210p8P3g00G0R5p4p741110R6p8P2p607311001R2P4p4p73110p8P2P6p8p100WiR4p60721003R7P6p8P7p100QVp4p741110p8P7P3p8P7p100RQR7p4p7210p8P4p607311002R4P6p8P4P2p8P4P7p4p73110p8P4p100SHp4p710p8p200R4P6p8p1005Pp4p70R6P1p8P6P0p8g00Gfj23Tg00H_j12Tg00KRj40TP5j71Tg00N]R5g00OUf2R0,35[g00C8R6p-0[\0P5p,4segsR1%21f4R1P5P1f3P0C0f1f0R0F1P0W1X46W2W3W5X04o"). Qed.

Lemma impl_enode_inv : forall {A} n (pl : resp -> option A) Q ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms.
Proof.
  intros A n pl Q ms H. cbn in H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp a E. specialize (Hk rsp). rewrite E in Hk. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma areg_eqv : forall ms ms' r, ms_eqv ms ms' -> is_x0 r = false -> areg ms r = areg ms' r.
Proof.
ltac2:(KReplay.run1 (kr_t_BrBase ()) ["WithSegs"] "h01Hh12HRh22Hrh32_Hh42msh53ms'h61rp;1p;2p;3p10000p4p70R0g000`R1p4p710R2p8P0p1001:p4p710R0p8p1001Xp4p70R3P2p8P3P0p8g002FR3p4p7210R4P2p8P4p10032p4p710R5p8P4P0p8P4p1003Np4p710p8P4p1003lp4p710p8P4p1004Ip4p710p8p100PKR4p60721002R6p100E?p4p7210p8P6p100F:R7p4p7210p8P6p100G0p4p741110R8p8P4p607311001R4P7p4p73110p8P4P8p8p100WiR7p60721003R9P8p8P9p100QVp4p741110p8P9P6p8P9p100RQR9p4p7210p8P7p607311002R7P8p8P7P4p8P7P9p4p73110p8P7p100SHp4p710R7p8p100Y5p60721001P8p8p100\Sp60721001R9P5p8P9P8p8P9P7p8P9p100Z?p4p7210p8p1005Pp4p70R9P2p8P9P0p8g00:=j12Tg00]_j1DTg00:bj14Tg00;@j13Tg00^Dj2CTg00_Hj1;Tg00`Gj2?TP3j2BTg00aMj16Tg00bMj17Tg00;cj1>Tg00<Ej19Tg00cNj1:Tg00dMj1=Tg00eLj1<Tg00fJj18TP1j30Tg00gHj1ATg00h0j25Tg00D?R1j2@Tf6R3f5R0f4R930f3R2f2R7f1R830f0R5'@'@p=1g00C8R4g00DZ#2R6#D#4R:#31C78P1%;2%;7'?%26#2R6#2#2R1#2#4#3R;,B:R:%62%67P;%72%77%>;R<%92%97P<%:2%:7%41#3R1%=2%=7%46#3#>\;R6%<2%<7%82%87506F1F1F1g00hfR=%A7g00iFR>301502159250;[P5%;0%;9'?P:%63%60P;%73%70P<%93%90P<%:3%:0P1%=3%=0P6%<3%<0%83%80506F1F1F1%A0=0=>P7P3P5O2f8/53f7/5350;eW2W3W1P8P5O2n2001000000120000000W0W6X54W4o"). Qed.

Lemma at_node_eqv : forall n ms ms', ms_eqv ms ms' -> at_node segs n ms -> at_node segs n ms'.
Proof.
  intros n ms ms' Heqv Hat. pose proof Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  destruct n; cbn [at_node] in *; rewrite <- ?Hsvc, <- ?Hm, <- ?Hro;
    repeat (rewrite <- (areg_eqv ms ms' _ Heqv) by (vm_compute; reflexivity)); exact Hat.
Qed.

Lemma nret_eqv : forall ms ms' rsp, ms_eqv ms ms' -> ms_eqv (nret ms rsp) (nret ms' rsp).
Proof.
ltac2:(KReplay.run1 (kr_t_BrBase ()) ["WithSegs"] "h01Hh12msh23ms'h33rspp;2p;4p;3p10000p4p70R0p1000`p4p710R1p8P0p1001:p4p710R0p8p1001Xp4p70R2P1p8P2P0p8p1002Fp4p7210R2P1p8P2p10032p4p710R3p8P2P0p8P2p1003Np4p710p8P2p1003lp4p710p8P2p1004Ip4p710p8p100PKR2p60721002R4p100E?p4p7210p8P4p100F:R5p4p7210p8P4p100G0p4p741110R6p8P2p607311001R2P5p4p73110p8P2P6p8p100WiR5p60721003R7P6p8P7p100QVp4p741110p8P7P4p8P7p100RQR7p4p7210p8P5p607311002R5P6p8P5P2p8P5P7p4p73110p8P5p100SHp4p710R5p8p100Y5p60721001P6p8p100\Sp60721001R7P3p8P7P6p8P7P5p8P7p100Z?p4p7210p8p1005Pp4p70R7P1p8P7P0p8g00^Dj20Tg01I8j22Tg01J1j44Tg01K?j33Tg00LKj21Tg00C8R0g00OUf2R7f1R1'0f3R5/211271P5P7P1f0C43311511171'0eW0W3X20W1o"). Qed.

(* [comment removed for export] *)
Lemma evt_eqv_transfer : forall P ms ms', ms_eqv ms ms' -> evt segs P ms ->
  exists ms1 ms1', P ms1 /\ ms_eqv ms1 ms1' /\ CatSim.msteps segs ms' ms1'.
Proof.
  intros P ms ms' Heqv (ms1 & Hms & HP).
  destruct (msteps_eqv segs ms ms1 (cj_msteps_cat _ _ Hms) ms' Heqv) as (ms1' & Hms' & Heqv1).
  exists ms1, ms1'. auto.
Qed.

End WithSegs.

End BrBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad.
Module BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Exec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Frame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Import Monad.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083.BrRegs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083.BrBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BrXfer () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase=impl_bind_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4implC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_ebind_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5epostC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase<impl_vis_invC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_enode_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec6msteps00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec6msteps01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init5Logic3and01K79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2CJ3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs6ms_eqvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K69OSSVerify5KrLib2CJ3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase@evt_eqv_transferC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00394Exec3evtC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrXfer=cat_msteps_cjC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K69OSSVerify5KrLib2CJ3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4nretC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase;at_node_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase8nret_eqvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I69OSSVerify5KrLib2CJ3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4respC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrXferAimpl_eqv_transferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic4True01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrXferBimplM_eqv_transferC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs:canon_regsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs8regs_eqvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs>canon_regs_eqvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrRegs<regs_eqv_symC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC79OSSVerify5KrLib2CJ3Lib7Mh_00396MState2MSC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma cat_msteps_cj : forall a b, CatSim.msteps segs a b -> Exec.msteps segs a b.
Proof.
  intros a b H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.

Lemma impl_eqv_transfer : forall {R} (t : itree node R) Q ms ms',
  impl segs (at_node segs) t Q ms -> ms_eqv ms ms' ->
  impl segs (at_node segs) t (fun r ms1' => exists ms1, Q r ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
  intros R t. induction t as [r | n k IH]; intros Q ms ms' H Heqv; cbn [impl] in *.
  - destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & HQ & Heqv1 & Hms).
    exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. exists ms1. auto.
  - destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & [Hat Hk] & Heqv1 & Hms).
    exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. split; [eapply at_node_eqv; [exact Heqv1| exact Hat]|].
    intros rsp. eapply IH; [apply Hk| apply nret_eqv; exact Heqv1].
Qed.

Lemma implM_eqv_transfer : forall {St A} (c : Monad.M St A) s Q ms ms',
  implM segs c s Q ms -> ms_eqv ms ms' ->
  implM segs c s (fun a s' ms1' => exists ms1, Q a s' ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
  intros St A c s Q ms ms' H Heqv. unfold implM in *.
  eapply impl_mono; [eapply impl_eqv_transfer; [exact H| exact Heqv]|].
  intros [|[a s']] ms1' (ms1 & HQ & Heqv1); cbn in *; [exact I|]. exists ms1. auto.
Qed.

(* [comment removed for export] *)
Context {fx : FPState}.

Lemma mkst_eqv_canon : forall R pc M rom,
  ms_eqv (MS (canon_regs R) fp_regs pc fp_csr None M rom) (mkst R pc M rom).
Proof.
  intros R pc M rom. unfold ms_eqv, MS, mkst; cbn. repeat split; try reflexivity.
  apply regs_eqv_sym, canon_regs_eqv.
Qed.

(* [comment removed for export] *)
Lemma MS_is_mkst : forall R pc M rom, MS R fp_regs pc fp_csr None M rom = mkst R pc M rom.
Proof.
ltac2:(KReplay.run1 (kr_t_BrXfer ()) ["WithSegs"] "h01Mh11Rh22pch33romp;1p;2p;5p10000p4p70R0g00l`R1p4p710R2p8P0p1001:p4p710R0p8p1001Xp4p70R3P2p8P3P0p8g002FR3p4p7210R4P2p8P4p10032p4p710R5p8P4P0p8P4p1003Np4p710p8P4p1003lR6p4p710R7p8P4p1004Ip4p710p8p1005PR4p60721002R8p1006[p4p7210R9p8P8p1007VR:p4p7210p8P8p1008Lp4p741110R;p8P4p607311001R4P:p4p73110p8P4P;p8p1009BR:p60721003R<P;p8P<p100:Np4p741110R=p8P<P8p8P<p100;IR<p4p7210p8P:p607311002R:P;p8P:P4p8P:P<p4p73110p8P:p100<@p4p710R:p8p100=7p60721001P;p8p100>Ap60721001R<P5p8P<P;p8P<P:p8P<p100?Mp4p7210p8p100]9p60721001R<P9p8P<P;p8p100d^R;p60721002R9p100^HR5p4p710p8P9P6p4p7210p8P9P=p8P9P<p8P9P:p8P;p607311001R;P5p4p7210p8P;P7p8P;p100_<p4p73110p8P;P=p8P;P<p8P;P:p8p100@Dp4p70R:P2p8P:P0p8g00D8j10Tg00enj17Tg00D]j11Tg00E;j12TP3j26Tg00E^j15Tg0168j54TP1j23Tg00NU#0R1#7#1%01#0R1#0#0#0#1#2R3'6%11#2#5\3R1g00MNp,2fxf3f2f1f0D4'3X31W0X23W1o"). Qed.

Lemma ms_eqv_MS_inv : forall R F pc fc m rom ms',
  ms_eqv (MS R F pc fc None m rom) ms' ->
  ms' = MS (ms_regs ms') F pc fc None m rom /\ regs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m rom [R' F' pc' svc' rv' fc' m' rom'] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); cbn in *.
  subst. split; [reflexivity| exact H1].
Qed.

End WithSegs.

End BrXfer.
