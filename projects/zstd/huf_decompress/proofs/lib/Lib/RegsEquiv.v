(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (43 recorded proofs replaced by written proofs (regs_eqv_refl, regs_eqv_sym, regs_eqv_trans and 40 more); init_ms, init_machine_state_eqv, init_behaviour_eqv and 1 more restated for the revision's model; sstep_eqv_scfg re-proved; adds set_reg_eqv, vdso_write_regs_eqv, ms_read_byte_eqv and 6 more). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RegsEquiv () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem7reg_getK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib3Lib9RegsEquiv8regs_eqvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib3Lib6MState@reg_get_set_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib6MStateAreg_get_set_otherC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3Lib9RegsEquiv;reg_get_setC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv3Sem6c_resvK47Corelib4Init5Logic3and01c59OSSVerify5KrLib3Lib9RegsEquiv8core_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rsetC4ELinuxProcessSemantics5Riscv3Sem5is_x0c59OSSVerify5KrLib3Lib9RegsEquiv<regs_eqv_setC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem4fsetC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem9with_fcsrC4ELinuxProcessSemantics5Riscv3Sem9with_resvC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions7Z_to_bvI4ELinuxProcessSemantics5Riscv3Fpu6fflags00C4ELinuxProcessSemantics5Riscv3Sem6fwriteC4ELinuxProcessSemantics5Riscv3Sem7nan_boxc59OSSVerify5KrLib3Lib9RegsEquiv=core_eqv_fsetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr4ffmt00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv3Sem:inval_resvC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addc59OSSVerify5KrLib3Lib9RegsEquiv;core_eqv_mkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv=core_eqv_rsetC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andK4ELinuxProcessSemantics5Riscv5Instr5instr04C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv3Sem3eff07i59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics5Riscv3Sem5low32c59OSSVerify5KrLib3Lib9RegsEquivCcore_eqv_inval_resvC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv08C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv04C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv3Sem3eff06k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivBcore_eqv_with_resvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics5Riscv3Sem7amo_valK4ELinuxProcessSemantics5Riscv5Instr5instr0FC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv3Sem9csr_sliceC4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions5bv_orC4ELinuxProcessSemantics5Riscv3Sem9slice_setK4ELinuxProcessSemantics5Riscv3Sem3eff02k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivBcore_eqv_with_fcsrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv;core_eqv_ifC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib9RegsEquiv7eff_eqv02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmac59OSSVerify5KrLib3Lib9RegsEquiv?core_eqv_fwriteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Fpu7fp_sqrtK4ELinuxProcessSemantics5Riscv5Instr5instr0MC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Fpu9fp_minmaxK4ELinuxProcessSemantics5Riscv5Instr5instr0OC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leK4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC4ELinuxProcessSemantics5Riscv3Fpu8int_wrapC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv3Fpu<round_scaledC4ELinuxProcessSemantics5Riscv3Fpu9fp_encodeC47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RC4ELinuxProcessSemantics5Riscv3Fpu8fp_classK4ELinuxProcessSemantics5Riscv5Instr5instr0SC4ELinuxProcessSemantics5Riscv3Sem4execC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics5Riscv3Sem2w1I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv3Sem3eff00I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I47Corelib6Floats9SpecFloat:spec_float00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00c59OSSVerify5KrLib3Lib9RegsEquiv=exec_eqv_coreC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib3Lib9RegsEquiv6ms_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv<regs_eqv_symC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv>regs_eqv_transC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib3Lib9RegsEquiv;eff_eqv_indC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions4BvWfc59OSSVerify5KrLib3Lib9RegsEquiv:ms_reg_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc59OSSVerify5KrLib3Lib9RegsEquiv7res_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivGinterp_eff_accesses_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec59OSSVerify5KrLib3Lib9RegsEquivHdecode_exec_accesses_eqvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesc59OSSVerify5KrLib3Lib9RegsEquivAstep_accesses_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem3Run<syscall_argsC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib3Lib9RegsEquiv@syscall_args_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteK4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput01I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcc59OSSVerify5KrLib3Lib9RegsEquiv7cfg_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc59OSSVerify5KrLib3Lib9RegsEquiv:ms_eqv_symC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c59OSSVerify5KrLib3Lib9RegsEquivCmi_account_step_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib3Lib9RegsEquiv6to_eqvC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep02K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep03C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesc59OSSVerify5KrLib3Lib9RegsEquiv=sys_input_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c59OSSVerify5KrLib3Lib9RegsEquiv@apply_effect_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivDadvance_past_svc_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep05C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep07K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep08I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib3Lib9RegsEquiv9sstep_eqvC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00K4ELinuxProcessSemantics?LinuxProcessSem3Run4star01c59OSSVerify5KrLib3Lib9RegsEquiv=sstep_cfg_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib3Lib9RegsEquiv8star_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run=reaches_errorC4ELinuxProcessSemantics?LinuxProcessSem3Run<unmodeled_atK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_unmodeledc59OSSVerify5KrLib3Lib9RegsEquiv@unmodeled_at_eqvC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run@all_traces_error00c59OSSVerify5KrLib3Lib9RegsEquiv;cfg_eqv_symC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run@all_traces_error01C4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_indC47Corelib4Init5Logic3iffc59OSSVerify5KrLib3Lib9RegsEquiv=obs_trace_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivAreaches_error_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivDall_traces_error_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivEreaches_unmodeled_eqvC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg01K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg02K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg03K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg05K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg06K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg07K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg08C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgc59OSSVerify5KrLib3Lib9RegsEquiv>sstep_eqv_scfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg01c59OSSVerify5KrLib3Lib9RegsEquivBsstep_cfg_eqv_scfgC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgc59OSSVerify5KrLib3Lib9RegsEquiv=star_eqv_scfgC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunEreaches_unmodeled_cfgI4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_cfg01C4ELinuxProcessSemantics?LinuxProcessSem3RunHall_traces_error_cfg_indc59OSSVerify5KrLib3Lib9RegsEquivBobs_trace_eqv_scfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivFreaches_error_eqv_scfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivIall_traces_error_eqv_scfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivJreaches_unmodeled_eqv_scfgC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib3Lib9RegsEquiv:reg_of_natC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyc59OSSVerify5KrLib3Lib9RegsEquiv8mkR_initC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib3Lib8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv7init_msC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv=init_regs_mkRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC59OSSVerify5KrLib3Lib8PropExec9init_mkstC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C59OSSVerify5KrLib3Lib8PropExec3fx0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivFinit_machine_state_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquiv=behaviour_eqvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9RegsEquivBbehaviour_eqv_scfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_eqv (R R' : bvmap 5 word) : Prop := forall r, reg_get R r = reg_get R' r.

Lemma regs_eqv_refl : forall R, regs_eqv R R.
Proof. intros R r. reflexivity. Qed.
Lemma regs_eqv_sym : forall R R', regs_eqv R R' -> regs_eqv R' R.
Proof. intros R R' H r. symmetry. apply H. Qed.
Lemma regs_eqv_trans : forall R1 R2 R3, regs_eqv R1 R2 -> regs_eqv R2 R3 -> regs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r. etransitivity; [apply H1|apply H2]. Qed.

(* [comment removed for export] *)
Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
  reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
  intros R k r v. destruct (bv_eqb k r) eqn:E.
  - apply bv_eqb_eq in E. subst. apply reg_get_set_same.
  - apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma regs_eqv_set : forall R R' (k : reg) v,
  regs_eqv R R' -> regs_eqv (bvmap_set k v R) (bvmap_set k v R').
Proof. intros R R' k v H r. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv (c c' : core) : Prop :=
  regs_eqv (c_regs c) (c_regs c') /\ regs_eqv (c_fregs c) (c_fregs c') /\
  c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : forall R R' F F' pc fc rv, regs_eqv R R' -> regs_eqv F F' ->
  core_eqv (Core R F pc fc rv) (Core R' F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : forall r v c c', core_eqv c c' -> core_eqv (rset r v c) (rset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_fset : forall r v c c', core_eqv c c' -> core_eqv (fset r v c) (fset r v c').
Proof.
  intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_with_pc : forall v c c', core_eqv c c' -> core_eqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : forall v c c', core_eqv c c' -> core_eqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : forall v c c', core_eqv c c' -> core_eqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : forall fl c c', core_eqv c c' -> core_eqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : forall fmt r v c c', core_eqv c c' -> core_eqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : forall a c c', core_eqv c c' -> core_eqv (inval_resv a c) (inval_resv a c').
Proof.
  intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & HF & -> & -> & ->).
  destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
  core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

(* [comment removed for export] *)
Local Ltac solve_core HR HF :=
  repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
               | apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
               | apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
               | match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
  apply (core_eqv_mk _ _ _ _ _ _ _ HR HF).

Local Ltac eqv_struct HR HF :=
  repeat first
    [ apply EqvDone; solve_core HR HF
    | apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

(* [comment removed for export] *)
Lemma exec_eqv_core : forall R R' F F' pc fc rv sz i,
  regs_eqv R R' -> regs_eqv F F' ->
  eff_eqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F' pc fc rv)).
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?HR, ?HF; eqv_struct HR HF.
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
  regs_eqv (ms_regs ms) (ms_regs ms') /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
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

(* [comment removed for export] *)
Definition res_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b => ms_eqv (access_value _ a) (access_value _ b) /\ accessed_ranges _ a = accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk r, MachineOk r' =>
      core_eqv (fst (access_value _ r)) (fst (access_value _ r')) /\ snd (access_value _ r) = snd (access_value _ r')
      /\ accessed_ranges _ r = accessed_ranges _ r'
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|];
      [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [r| |]; destruct (interp_eff_accesses segs (k' _) m) as [r'| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    destruct H0 as (H1 & H2 & H3). rewrite H3. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [r| |]; destruct (interp_eff_accesses segs k' _) as [r'| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (H1 & H2 & H3). rewrite H3. auto.
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r (HR & _). unfold ms_reg. rewrite (HR r). reflexivity. Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  res_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - simpl. rewrite H17. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] acc]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
    simpl in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, moa), MachineOk (b, mob) => ms_eqv a b /\ moa = mob
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as K. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [r| |]; destruct (RiscvSemantics.step_accesses segs ms') as [r'| |];
    simpl in K; try exact K; try contradiction.
  destruct K as [Hv <-]. destruct (materialize_model_accesses mo (accessed_ranges _ r)); [auto| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR. reflexivity. Qed.

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

Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.

Definition to_eqv (X X' : step_to) : Prop :=
  match X, X' with
  | SError, SError => True
  | SNext c, SNext c' => cfg_eqv c c'
  | _, _ => False
  end.

Lemma set_reg_eqv : forall ms ms' r v, ms_eqv ms ms' -> ms_eqv (set_reg ms r v) (set_reg ms' r v).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] r v
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold set_reg. destruct (bv_eqb r 0); repeat split; simpl; auto using regs_eqv_set.
Qed.

Lemma vdso_write_regs_eqv : forall rs vs ms ms', ms_eqv ms ms' ->
  ms_eqv (vdso_write_regs ms rs vs) (vdso_write_regs ms' rs vs).
Proof.
  induction rs as [|r rs IH]; intros vs ms ms' H; [exact H|].
  destruct vs as [|v vs]; [exact H|].
  cbn [vdso_write_regs]. apply IH, set_reg_eqv, H.
Qed.

Lemma ms_read_byte_eqv : forall ms ms', ms_eqv ms ms' -> ms_read_byte ms = ms_read_byte ms'.
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst. reflexivity.
Qed.

Lemma ms_sp_eqv : forall ms ms', ms_eqv ms ms' -> ms_sp ms = ms_sp ms'.
Proof. intros ms ms' (HR & _). unfold ms_sp. apply HR. Qed.

Lemma vdso_read_regs_eqv : forall ms ms', ms_eqv ms ms' -> vdso_read_regs ms = vdso_read_regs ms'.
Proof.
  intros ms ms' H. unfold vdso_read_regs. apply List.map_ext.
  intros r. apply (ms_reg_eqv _ _ _ H).
Qed.

Lemma vdso_with_mem_eqv : forall ms ms' m, ms_eqv ms ms' ->
  ms_eqv (vdso_with_mem ms m) (vdso_with_mem ms' m).
Proof.
  intros [R F pc svc rv fc m0 ro] [R' F' pc' svc' rv' fc' m0' ro'] m
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_with_mem. repeat split; simpl; auto.
Qed.

Lemma vdso_set_pc_eqv : forall ms ms' pc, ms_eqv ms ms' ->
  ms_eqv (vdso_set_pc ms pc) (vdso_set_pc ms' pc).
Proof.
  intros [R F pc0 svc rv fc m ro] [R' F' pc0' svc' rv' fc' m' ro'] pc
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold vdso_set_pc. repeat split; simpl; auto.
Qed.

Lemma vdso_post_eqv : forall ms ms' model fr eff, ms_eqv ms ms' ->
  ms_eqv (vdso_post segs ms model fr eff) (vdso_post segs ms' model fr eff).
Proof.
  intros ms ms' model fr eff H.
  unfold vdso_post. cbv zeta.
  rewrite (ms_reg_eqv _ _ _ H), (ms_sp_eqv _ _ H), (vdso_read_regs_eqv _ _ H), (ms_read_byte_eqv _ _ H).
  match goal with |- ms_eqv (vdso_set_pc (apply_effect (vdso_with_mem (vdso_write_regs ms ?rs ?vs) _) _) _) _ =>
    pose proof (vdso_write_regs_eqv rs vs ms ms' H) as HW end.
  pose proof HW as (_ & _ & _ & _ & _ & _ & Hmw & _). rewrite Hmw.
  apply vdso_set_pc_eqv, apply_effect_eqv, vdso_with_mem_eqv, HW.
Qed.

Lemma vdso_call_unmodeled_eqv : forall ms ms' mo fn, ms_eqv ms ms' ->
  vdso_call_unmodeled segs ms mo fn -> vdso_call_unmodeled segs ms' mo fn.
Proof.
  intros ms ms' mo fn H Hun. unfold vdso_call_unmodeled in *.
  destruct Hun as [Hn0 | [(n0 & Hn0 & Hsp0) | (n0 & e0 & m0 & v0 & Hn0 & Hsp0 & Hor)]].
  - left. exact Hn0.
  - right. left. exists n0. split; [exact Hn0|]. rewrite <- (sys_input_eqv ms ms' _ H). exact Hsp0.
  - right. right. exists n0, e0, m0, v0. split; [exact Hn0|]. split; [|exact Hor].
    rewrite <- (sys_input_eqv ms ms' _ H). exact Hsp0.
Qed.

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  exists X', sstep segs (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_instr_fault; auto; congruence| exact I].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply sstep_instr_unmodeled; [assumption | congruence | exact E |].
    match goal with Hx : vdso_entry_fn _ (ms_pc ms) = None |- _ =>
      unfold ms_pc in *; rewrite <- Hpc; exact Hx end.
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    eexists. split.
    + eapply sstep_vdso_call; eauto; congruence.
    + cbn [to_eqv cfg_eqv cfg_ms cfg_model]. split; [apply vdso_post_eqv, Heqv | reflexivity].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    exists SError. split; [eapply sstep_vdso_materialization_fault; eauto; congruence | exact I].
  - match goal with Hx : mi_account_step segs ms mo = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    match goal with Hx : vdso_call_unmodeled _ ms mo _ |- _ =>
      pose proof (vdso_call_unmodeled_eqv ms ms' mo _ Heqv Hx) as Hun' end.
    unfold ms_pc in *. rewrite Hpc in *.
    eapply sstep_vdso_unmodeled; eauto; congruence.
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_syscall segs ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_syscall_materialization_fault segs ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_exit segs ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_killed segs ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_syscall_unmodeled segs ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep segs c evs X -> exists X', sstep segs c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

Lemma star_eqv : forall c tr c1, star segs c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star segs c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_refl| exact Heqv].
  - destruct (sstep_cfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_step; eassumption| exact H3].
Qed.

Lemma obs_trace_eqv : forall c c' tr, cfg_eqv c c' -> obs_trace segs c tr -> obs_trace segs c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_eqv : forall c c', cfg_eqv c c' -> reaches_error segs c -> reaches_error segs c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

Lemma unmodeled_at_eqv : forall c c', cfg_eqv c c' -> unmodeled_at segs c -> unmodeled_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hun; simpl in Hms, Hmo; subst.
  unfold unmodeled_at in *. cbn [cfg_ms cfg_model] in *. destruct Hun as (Hh & Hcase).
  pose proof Hms as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  pose proof (mi_account_step_eqv ms ms' mo' Hms) as Hres.
  split; [exact Hh|].
  destruct Hcase as [(Hnone & Hstep & Hvd) | [(Hnone & Hstep & fn & Hfn & Hun) | (x8 & Hsome & Hspec)]].
  - left. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction.
    split; [congruence|]. split; [reflexivity|]. unfold ms_pc in *. rewrite <- Hpc. exact Hvd.
  - right. left. rewrite Hstep in Hres.
    destruct (mi_account_step segs ms' mo') as [[? ?]| |]; simpl in Hres; try contradiction.
    split; [congruence|]. split; [reflexivity|]. exists fn. split.
    + unfold ms_pc in *. rewrite <- Hpc. exact Hfn.
    + exact (vdso_call_unmodeled_eqv ms ms' mo' fn Hms Hun).
  - right. right. exists x8. split; [congruence|]. rewrite <- (sys_input_eqv ms ms' x8 Hms). exact Hspec.
Qed.

Lemma reaches_unmodeled_eqv : forall c c', cfg_eqv c c' ->
  reaches_unmodeled segs c -> reaches_unmodeled segs c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hun).
  destruct (star_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| eapply unmodeled_at_eqv; eassumption].
Qed.

Lemma all_traces_error_eqv : forall c, all_traces_error segs c ->
  forall c', cfg_eqv c c' -> all_traces_error segs c'.
Proof.
  intros c H. induction H as [c Hprog Hnext IH]; intros c' Heqv.
  constructor.
  - destruct Hprog as (evs & to & Hst).
    destruct (sstep_cfg_eqv c c' evs to Heqv Hst) as (X' & Hst' & _). eauto.
  - intros evs c2' Hst'.
    destruct (sstep_cfg_eqv c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
    destruct X as [c2|]; simpl in HX; [|contradiction].
    apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

(* [comment removed for export] *)
Theorem behaviour_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace segs (mkCfg ms mo) tr <-> obs_trace segs (mkCfg ms' mo) tr) /\
  (reaches_error segs (mkCfg ms mo) <-> reaches_error segs (mkCfg ms' mo)) /\
  (all_traces_error segs (mkCfg ms mo) <-> all_traces_error segs (mkCfg ms' mo)) /\
  (reaches_unmodeled segs (mkCfg ms mo) <-> reaches_unmodeled segs (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [| split; [| split]]; [intros tr|..]; split; intros H.
  - exact (obs_trace_eqv _ _ tr H1 H).
  - exact (obs_trace_eqv _ _ tr H2 H).
  - exact (reaches_error_eqv _ _ H1 H).
  - exact (reaches_error_eqv _ _ H2 H).
  - exact (all_traces_error_eqv _ H _ H1).
  - exact (all_traces_error_eqv _ H _ H2).
  - exact (reaches_unmodeled_eqv _ _ H1 H).
  - exact (reaches_unmodeled_eqv _ _ H2 H).
Qed.

Section Scfg.
Variable scfg : SpuriousCfg.

Lemma sstep_eqv_scfg : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs scfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs scfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply sstep_cfg_instr_unmodeled; [assumption | congruence | exact E |].
    match goal with Hx : vdso_entry_fn _ (ms_pc ms) = None |- _ =>
      unfold ms_pc in *; rewrite <- Hpc; exact Hx end.
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    eexists. split.
    + eapply sstep_cfg_vdso_call; eauto; congruence.
    + cbn [to_eqv cfg_eqv cfg_ms cfg_model]. split; [apply vdso_post_eqv, Heqv | reflexivity].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    unfold ms_pc in *. rewrite Hpc in *.
    repeat match goal with Hx : context [sys_input segs ms ?x] |- _ => rewrite (sys_input_eqv ms ms' x Heqv) in Hx end.
    exists SError. split; [eapply sstep_cfg_vdso_materialization_fault; eauto; congruence | exact I].
  - match goal with Hm : mi_account_step segs ms mo = _ |- _ => rewrite Hm in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    match goal with Hx : vdso_call_unmodeled _ ms mo _ |- _ =>
      pose proof (vdso_call_unmodeled_eqv ms ms' mo _ Heqv Hx) as Hun' end.
    unfold ms_pc in *. rewrite Hpc in *.
    eapply sstep_cfg_vdso_unmodeled; eauto; congruence.
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs scfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs scfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs scfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs scfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs scfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_cfg_eqv_scfg : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs scfg c evs X -> exists X', sstep_cfg segs scfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv_scfg ms ms'); assumption.
Qed.

Lemma star_eqv_scfg : forall c tr c1, star_cfg segs scfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs scfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstep_cfg_eqv_scfg c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

Lemma obs_trace_eqv_scfg : forall c c' tr, cfg_eqv c c' ->
  obs_trace_cfg segs scfg c tr -> obs_trace_cfg segs scfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_eqv_scfg c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_eqv_scfg : forall c c', cfg_eqv c c' ->
  reaches_error_cfg segs scfg c -> reaches_error_cfg segs scfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_eqv_scfg c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_cfg_eqv_scfg c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

Lemma reaches_unmodeled_eqv_scfg : forall c c', cfg_eqv c c' ->
  reaches_unmodeled_cfg segs scfg c -> reaches_unmodeled_cfg segs scfg c'.
Proof.
  intros c c' Heqv (tr & c1 & Hstar & Hun).
  destruct (star_eqv_scfg c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  exists tr, c1'. split; [exact Hstar'| eapply unmodeled_at_eqv; eassumption].
Qed.

Lemma all_traces_error_eqv_scfg : forall c, all_traces_error_cfg segs scfg c ->
  forall c', cfg_eqv c c' -> all_traces_error_cfg segs scfg c'.
Proof.
  intros c H. induction H as [c Hprog Hnext IH]; intros c' Heqv.
  constructor.
  - destruct Hprog as (evs & to & Hst).
    destruct (sstep_cfg_eqv_scfg c c' evs to Heqv Hst) as (X' & Hst' & _). eauto.
  - intros evs c2' Hst'.
    destruct (sstep_cfg_eqv_scfg c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
    destruct X as [c2|]; simpl in HX; [|contradiction].
    apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

Theorem behaviour_eqv_scfg : forall ms ms' mo, ms_eqv ms ms' ->
  (forall tr, obs_trace_cfg segs scfg (mkCfg ms mo) tr <-> obs_trace_cfg segs scfg (mkCfg ms' mo) tr) /\
  (reaches_error_cfg segs scfg (mkCfg ms mo) <-> reaches_error_cfg segs scfg (mkCfg ms' mo)) /\
  (all_traces_error_cfg segs scfg (mkCfg ms mo) <-> all_traces_error_cfg segs scfg (mkCfg ms' mo)) /\
  (reaches_unmodeled_cfg segs scfg (mkCfg ms mo) <-> reaches_unmodeled_cfg segs scfg (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Heqv.
  assert (H1 : cfg_eqv (mkCfg ms mo) (mkCfg ms' mo)) by (split; [exact Heqv| reflexivity]).
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [| split; [| split]]; [intros tr|..]; split; intros H.
  - exact (obs_trace_eqv_scfg _ _ tr H1 H).
  - exact (obs_trace_eqv_scfg _ _ tr H2 H).
  - exact (reaches_error_eqv_scfg _ _ H1 H).
  - exact (reaches_error_eqv_scfg _ _ H2 H).
  - exact (all_traces_error_eqv_scfg _ H _ H1).
  - exact (all_traces_error_eqv_scfg _ H _ H2).
  - exact (reaches_unmodeled_eqv_scfg _ _ H1 H).
  - exact (reaches_unmodeled_eqv_scfg _ _ H2 H).
Qed.

End Scfg.

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

(* [comment removed for export] *)
Definition mkR_init (sp : word) : bvmap 5 word :=
  mkR w0 sp w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0.

Lemma init_regs_mkR : forall sp : word,
  regs_eqv (bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty)) (mkR_init sp).
Proof.
  intros sp r. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition init_ms (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp mbase : word)
    (draw : EntryDraw) (inp : ProcInput) : machine_state :=
  MS (mkR_init sp) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp draw) (seg_rom segs).

Lemma init_machine_state_eqv : forall segs pc ph sp mbase draw inp,
ms_eqv (init_machine_state segs pc ph sp mbase draw inp) (init_ms segs pc ph sp mbase draw inp).
Proof.
  intros segs pc ph sp mbase draw inp.
  split; [exact (init_regs_mkR sp)|].
  split; [apply regs_eqv_refl|].
  repeat split.
Qed.

(* [comment removed for export] *)
Theorem init_behaviour_eqv : forall segs pc ph sp mbase draw inp mo,
let c0 := mkCfg (init_machine_state segs pc ph sp mbase draw inp) mo in
let c0' := mkCfg (init_ms segs pc ph sp mbase draw inp) mo in
(forall tr, obs_trace segs c0 tr <-> obs_trace segs c0' tr) /\
(reaches_error segs c0 <-> reaches_error segs c0') /\
(all_traces_error segs c0 <-> all_traces_error segs c0') /\
(reaches_unmodeled segs c0 <-> reaches_unmodeled segs c0').
Proof.
intros. apply behaviour_eqv. apply init_machine_state_eqv. Qed.

Theorem init_behaviour_eqv_scfg : forall scfg segs pc ph sp mbase draw inp mo,
  let c0 := mkCfg (init_machine_state segs pc ph sp mbase draw inp) mo in
  let c0' := mkCfg (init_ms segs pc ph sp mbase draw inp) mo in
  (forall tr, obs_trace_cfg segs scfg c0 tr <-> obs_trace_cfg segs scfg c0' tr) /\
  (reaches_error_cfg segs scfg c0 <-> reaches_error_cfg segs scfg c0') /\
  (all_traces_error_cfg segs scfg c0 <-> all_traces_error_cfg segs scfg c0') /\
  (reaches_unmodeled_cfg segs scfg c0 <-> reaches_unmodeled_cfg segs scfg c0').
Proof. intros. apply behaviour_eqv_scfg. apply init_machine_state_eqv. Qed.
