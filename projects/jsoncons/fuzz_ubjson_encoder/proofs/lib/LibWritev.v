(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the read-only-backing form of the system-call steps; the channel-reader premise of writev; the model's access_ok checks; imports; new lemmas; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/LibWritev.v, 292 lines within its lines 27-682. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes FileSim AgentLib AgentNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_LibWritev () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=bv_wrap_smallC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch9lookup_caC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch8ca_checkC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite<check_writevC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I47Corelib4Init9Datatypes6option00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch:CheckedArm00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys8Dispatch=checked_tableK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_altC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgFnode_ok_of_pnode_sysnoC13~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_alt_wallC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init6Specif3sig01K47Corelib4Init5Logic2ex01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~C47Corelib4Init6Specif9proj1_sigC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_SymmetricI47Corelib4Init6Specif3sig00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_nodeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srz_conseqC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec?bytes_le_to_Z_8C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9le_word_vC13~~~C35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExecAms_read_bytes_rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimHread_bytes_map_read_byteC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8read_u64I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev9iov_arrayC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State@read_iovec_entryK4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry01K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic5proj2c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev<read_u64_rdnC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev<bv_add_ZformC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry03K4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry02K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevIread_iovec_entry_of_arrayC13~~~C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State?copy_iovecs_auxI4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import00K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import02K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev8iov_bufsC13~~~C46Stdlib5Lists4List6concatC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem5State=gather_iovecsc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevBread_bytes_map_rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:iovs_totalC4ELinuxProcessSemantics?LinuxProcessSem5State>cap_iovecs_auxC4ELinuxProcessSemantics?LinuxProcessSem5StateAiovs_total_nonnegc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev>u64_roundtrip'C13~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z5min_rc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev;iov_bufs_okC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?iovs_access_okbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7forallbC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@access_okb_introC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes4negbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev@access_okb_of_leC13~~~K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic6eq_symc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevEiovs_access_okb_of_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevDcopy_iovecs_of_arrayC13~~~C56Stdlib6ZArith4Znat5Nat2Z2idc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev=word_to_nat_ZC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C4ELinuxProcessSemantics?LinuxProcessSem5State=import_iovecsK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem5State7IOV_MAXC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z8inj_succC4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTI47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev>gather_of_bufsC13~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDgather_iovecs_lengthC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5State?addr_is_error_bC4ELinuxProcessSemantics?LinuxProcessSem5StateCiov_prefix_accessesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite8iovcnt32C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem5State:cap_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5StateFimport_iovecs_accessesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State?writev_gatheredC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>rw_pos_einvalbC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite@modeled_file_gapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem2Fs:file_writeC4ELinuxProcessSemantics?LinuxProcessSem2Fs6fs_setC4ELinuxProcessSemantics?LinuxProcessSem5State7with_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>append_new_posK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev=cap_iovecs_idC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=gather_prefixC56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat7eqb_neqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBgather_prefix_fullc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevFimport_iovecs_of_arrayC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim9in_mem_siC13~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim:in_arg2_siC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim:in_arg1_siC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim:in_arg0_siC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim;in_sysno_siC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevDcheck_syscall_writevC13~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAaccess_ranges_eqbK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State6in_memI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev<writev_checkC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimMapply_effect_copyins_no_writeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7wr_fullC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDaccess_ranges_eqb_eqC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Nodes>sstep_of_checkC13~~~C57Corelib7BinNums6PosDef3Pos6to_natC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Nodes=sstep_svc_invC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7halt_evC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC56Stdlib6ZArith6BinInt1Z3maxI4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Scfg?injected_arm_66C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C46Stdlib5Lists4List9app_nil_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes5ependC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend2C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare3at_C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare5at_atC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=adv_set_ependC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritevArz_writev_pendingC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes6rz_sysC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:rdn_lengthC13~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev:rz_writev2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev7rz_wallC13~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibWritev:rz_writev1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_write_chC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDcopy_iovecs_accessesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5NodesJrz_ret_only_copyins_silentC13~~~".
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require RomBase RomWrite RomWritev.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Section FPX_1. Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
  intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma access_okb_of_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma check_syscall_writev : forall i eff m,
  bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt_wall_nat : forall (ch : word) (bs : list byte) (K : TSet),
  K [] -> (1 <= length bs)%nat ->
  t_eq (t_alt (fun k : nat =>
          fun tr => (1 <= k <= length bs)%nat /\
            t_emit (map (WriteEv ch) (firstn k bs)) (t_emit (map (WriteEv ch) (skipn k bs)) K) tr))
       (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros ch bs K HK Hnb tr. rewrite <- (t_alt_wall ch bs K HK Hnb tr). unfold t_alt. split.
  - intros [k [Hk Ht]]. exists (exist _ k Hk). exact Ht.
  - intros [[k Hk] Ht]. exists k. split; [exact Hk | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma rz_wall : forall segs scfg c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  srealizes segs scfg c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  srealizes segs scfg c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs scfg c ch bs K Hnb HK H. eapply srz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma read_u64_rdn : forall ms a v,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (ms_read_byte ms) a = Some v.
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

Lemma read_bytes_map_rdn : forall ms a (n : word) bs,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a (word_to_nat n) = Some bs ->
  read_bytes_map (ms_read_byte ms) a n = Some bs.
Proof.
  intros ms a n bs Hrom H.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Lemma read_iovec_entry_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov ((b, n) :: r) ->
  read_iovec_entry (ms_read_byte ms) iov = IovEntry b n.
Proof.
  intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.
Lemma iovec_entry_accesses_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov ((b, n) :: r) ->
  iovec_entry_accesses (ms_read_byte ms) iov = [(iov, 16%nat)].
Proof.
  intros ms b n r iov Hrom (Hb & Hn & _). unfold iovec_entry_accesses.
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn), (read_u64_rdn ms iov b Hrom Hb).
  reflexivity.
Qed.

Lemma copy_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov iovs ->
  copy_iovecs_aux (ms_read_byte ms) iov (length iovs) = ImpOk iovs.
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  cbn [length copy_iovecs_aux].
  rewrite (read_iovec_entry_of_array ms b n r iov Hrom Ha).
  destruct Ha as (_ & _ & _ & Hr).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

Lemma gather_of_bufs : forall ms iovs bss,
  ms_rom ms = seg_rom segs ->
  iov_bufs (ms_mem ms) iovs bss ->
  gather_iovecs (ms_read_byte ms) iovs = Some (concat bss).
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

Lemma cap_iovecs_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite u64_roundtrip', IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
  end.

Lemma iovs_access_okb_of_ok : forall iovs, iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros ms iovs iov Hrom Hcnt Hok Harr Hbok. unfold import_iovecs.
  destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
  destruct r as [|[b2 n2] r2].
  -
    cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array ms b n [] iov Hrom Harr).
    destruct Hbok as [Hb _]. pose proof (u64_range n).
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
      by (unfold MAX_RW_COUNT in *; lia).
    reflexivity.
  -
    set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
    assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
    assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    rewrite E1, E0. rewrite u64_lit by lia.
    replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * cnt)) by lia.
    rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
    rewrite (copy_iovecs_of_array ms _ iov Hrom Harr).
    rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.

Lemma writev_rob : forall ms model x8 ch iovs bs,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 66%Z ->
  fd_lookup (m_fds model) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
  import_iovecs (ms_read_byte ms) (ms_gpr ms 1) (iovcnt32 (ms_gpr ms 2)) = ImpOk iovs ->
  gather_iovecs (ms_read_byte ms) (cap_iovecs iovs) = Some bs ->
  RomBase.sys_rob segs (mkCfg ms model).
Proof.
  intros ms model x8 ch iovs bs Hs Hno Hfd Himp Hg.
  apply RomBase.sys_rob_of_check. intros r x8' Hr Hs' eff. cbn [cfg_ms] in Hs'.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite !(check_syscall_writev _ eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite RomBase.sys_input_wrom.
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 0)
    with (in_arg (sys_input segs ms x8) 0).
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 1)
    with (in_arg (sys_input segs ms x8) 1).
  change (in_arg (RomBase.with_mem (sys_input segs ms x8) (ms_read_byte (RomBase.wrom ms r))) 2)
    with (in_arg (sys_input segs ms x8) 2).
  apply (RomWritev.check_writev_chan_ext _ _ _ _ _ eff model ch iovs bs).
  - rewrite in_arg0_si. exact Hfd.
  - rewrite in_mem_si. apply RomBase.mem_ext_read_byte_wrom. exact Hr.
  - rewrite in_mem_si, in_arg1_si, in_arg2_si. exact Himp.
  - rewrite in_mem_si. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma writev_check : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= rw_bytes_max)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  Z.of_nat (length bs) = tot /\
  forall eff, check_syscall (sys_input segs ms x8) eff model
    = match eff with
      | mkEffectU ret [] [] [] [] ci =>
          if (1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret)
          then if access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
               then CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
               else CheckReject
          else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Htmax Ht30 CA.
  pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false
    by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  rewrite in_mem_si, Hcnt32.
  rewrite (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
  (* [check_writev] has no [modeled_iovs_total] gate, so there is no
     [iovs_total_in_range] rewrite; [Htmax] stays a premise for the callers' sake. *)
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
  cbv beta iota zeta. fold tot.
  replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hrdr. change (negb true) with false.
  assert (Hlw : bv_unsigned (len_word bs) = tot).
  { unfold len_word. rewrite Hlen. apply u64_lit. lia. }
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  cbv beta iota.
  destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity].
  rewrite Hlen. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* 08b1429 [check_writev] gates the channel on the reader; [writev_check] takes it *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= rw_bytes_max)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes segs scfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Htmax Ht30 Hk.
  destruct (writev_check ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Htmax Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  3:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  2:{ assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs)))
        by (unfold iovcnt32, abi_low32; rewrite u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (Hcap : cap_iovecs iovs = iovs)
        by (unfold cap_iovecs; apply cap_iovecs_id; unfold MAX_RW_COUNT; try fold tot; lia).
      apply (writev_rob ms model x8 (Z_to_bv 64 fd) iovs (concat bss) Hsvc Hno).
      - rewrite H0, fd32_id by (rewrite u64_lit; lia). exact Hfd.
      - rewrite H1, H2, Hcnt32. exact (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
      - rewrite Hcap. exact (gather_of_bufs ms iovs bss Hrom Hbufs). }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  (* [comment removed for export] *)
  apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* 08b1429: [check_writev] gates the channel on the reader *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1 : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* 08b1429: [check_writev] gates the channel on the reader *)
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_ch : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= rw_bytes_max)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
  intros. unfold t_write_ch.
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (0 <= rw_bytes_max)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hrdr Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmax Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    exact (iovec_entry_accesses_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr). }
  assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
  { apply (writev_rob ms model (getr regs 17) (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] [] eq_refl Hno).
    - unfold ms. rewrite ms_gpr_epend0, H10, fd32_id by (rewrite u64_lit; lia). exact Hfd.
    - unfold ms. rewrite ms_gpr_epend1, ms_gpr_epend2, H11, H12.
      change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). exact Himp.
    - reflexivity. }
  eapply (rz_ret_only_copyins_silent segs scfg ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | exact Hrob | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.

End WithSegs.

End FPX_1.
